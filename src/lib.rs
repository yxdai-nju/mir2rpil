#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;

mod context;
pub mod debug;
mod path;
mod rpil;
mod rpilmap;
mod serialmap;
mod translate;

pub use translate::translate_function_def;
