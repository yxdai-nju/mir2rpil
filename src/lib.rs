#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

mod context;
pub mod debug;
mod path;
mod rpil;
mod translate;

pub use translate::translate_function_def;
