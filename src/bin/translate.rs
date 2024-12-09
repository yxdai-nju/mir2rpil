#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_driver::Compilation;
use rustc_hir::{self as hir};

use std::path::PathBuf;
use std::process::Command;

use anyhow::{Context, Result};
use clap::Parser;
use serde_json::Value;

struct Mir2rpilCompilerCalls {}

impl rustc_driver::Callbacks for Mir2rpilCompilerCalls {
    #[allow(clippy::needless_lifetimes)]
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> Compilation {
        mir2rpil::debug::prepare_func_mir_log_dir();

        if tcx.sess.dcx().has_errors_or_delayed_bugs().is_some() {
            tcx.dcx()
                .fatal("mir2rpil cannot be run on programs that fail compilation");
        }

        let mut pub_funcs = vec![];
        let items = tcx.hir_crate_items(());
        let free_items_owner_id = items.free_items().map(|id| id.owner_id);
        let impl_items_owner_id = items.impl_items().map(|id| id.owner_id);
        let func_ids = free_items_owner_id
            .chain(impl_items_owner_id)
            .map(|id| id.to_def_id());

        for func_id in func_ids {
            match tcx.def_kind(func_id) {
                hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                    if tcx.visibility(func_id).is_public() {
                        pub_funcs.push(func_id);
                    }
                }
                _ => {}
            }
        }

        println!("{} public functions in total", pub_funcs.len());
        println!("Public Functions: {:#?}", pub_funcs);
        for pub_func in pub_funcs {
            let rpil_insts_variants = mir2rpil::translate_function_def(tcx, pub_func);
            if rpil_insts_variants.is_empty() {
                println!("No Variants available");
                continue;
            }
            for (variant_idx, rpil_insts) in rpil_insts_variants.iter().enumerate() {
                println!("Variant {}:", variant_idx + 1);
                mir2rpil::debug::print_func_rpil_insts(tcx, pub_func, rpil_insts);
            }
        }

        tcx.dcx().abort_if_errors();

        Compilation::Stop
    }
}

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, value_name = "FILE")]
    manifest_path: Option<PathBuf>,
}

/// Execute a compiler with the given CLI arguments and callbacks.
fn run_compiler(
    args: Vec<String>,
    callbacks: &mut (dyn rustc_driver::Callbacks + Send),
    using_internal_features: std::sync::Arc<std::sync::atomic::AtomicBool>,
) -> ! {
    // Invoke compiler, and handle return code.
    let exit_code = rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&args, callbacks)
            .set_using_internal_features(using_internal_features)
            .run()
    });
    std::process::exit(exit_code)
}

struct RustcInvocation {
    args: Vec<String>,
}

fn get_rustc_invocation(manifest_path: &str) -> Result<RustcInvocation> {
    // Run cargo build with build-plan
    let output = Command::new("cargo")
        .args([
            "build",
            "-Z",
            "unstable-options",
            "--build-plan",
            "--manifest-path",
            manifest_path,
        ])
        .output()
        .context("Failed to execute cargo build-plan command")?;

    // Parse the JSON output
    let json_str =
        String::from_utf8(output.stdout).context("Failed to parse command output as UTF-8")?;

    let v: Value = serde_json::from_str(&json_str).context("Failed to parse JSON output")?;

    // Extract all invocations
    let invocations = v["invocations"]
        .as_array()
        .context("Could not find invocations array in build plan")?;

    let last_invocation = invocations
        .last()
        .context("The invocations array is empty")?;

    let program = last_invocation["program"]
        .as_str()
        .context("Field `program` is not a string")?
        .to_string();

    let raw_args = last_invocation["args"]
        .as_array()
        .context("Could not find args array in invocation")?
        .iter()
        .map(|arg| {
            arg.as_str()
                .context("Field `args` is not a string")
                .map(String::from)
        })
        .collect::<Result<Vec<_>>>()?;

    anyhow::ensure!(
        program.ends_with("rustc") && raw_args.first().is_some_and(|arg| arg == "--crate-name"),
        "Invoked program is not `rustc`, or the first argument is not '--crate-name'"
    );

    // Process the arguments to merge pairs where appropriate
    let mut processed_args = Vec::new();
    let mut i = 0;
    while i < raw_args.len() {
        if i + 1 < raw_args.len() && raw_args[i].starts_with("--") && !raw_args[i].contains('=') {
            // Check if the next argument doesn't start with '-'
            if !raw_args[i + 1].starts_with('-') {
                // Merge this pair with '='
                processed_args.push(format!("{}={}", raw_args[i], raw_args[i + 1]));
                i += 2;
                continue;
            }
        }
        // If no merging occurred, add the current argument as is
        processed_args.push(raw_args[i].clone());
        i += 1;
    }

    Ok(RustcInvocation {
        args: processed_args,
    })
}

fn main() -> Result<()> {
    let args = Args::parse();

    let manifest_path = args.manifest_path.context("No manifest path provided")?;

    let manifest_path_str = manifest_path
        .to_str()
        .context("Manifest path contains invalid Unicode")?;

    let invocation =
        get_rustc_invocation(manifest_path_str).context("Failed to get build invocations")?;

    let using_internal_features =
        rustc_driver::install_ice_hook(rustc_driver::DEFAULT_BUG_REPORT_URL, |_| ());

    rustc_driver::install_ctrlc_handler();

    let status = Command::new("cargo")
        .args(vec!["build", "--manifest-path", manifest_path_str])
        .status()
        .context("Failed to execute cargo build")?;
    if !status.success() {
        anyhow::bail!("Failed to execute cargo build with status: {}", status);
    }

    // Get the directory containing the manifest file
    let manifest_dir = manifest_path
        .parent()
        .context("Failed to get manifest directory")?;

    // Change the current working directory
    std::env::set_current_dir(manifest_dir).context("Failed to change working directory")?;

    run_compiler(
        invocation.args,
        &mut Mir2rpilCompilerCalls {},
        using_internal_features.clone(),
    );
}
