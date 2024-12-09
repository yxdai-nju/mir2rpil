use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

use std::fmt;

#[derive(Clone)]
pub struct ExecutionPath {
    call_stack: Vec<DefId>,
    bb_trace: Vec<(DefId, usize)>,
    visited_functions: FxHashSet<DefId>,
    visited_bbs: FxHashSet<(DefId, usize)>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        Self {
            call_stack: vec![],
            bb_trace: vec![],
            visited_functions: FxHashSet::default(),
            visited_bbs: FxHashSet::default(),
        }
    }

    #[inline(always)]
    pub fn stack_depth(&self) -> usize {
        self.call_stack.len()
    }

    #[inline(always)]
    pub fn stack_top_func_def_id(&self) -> DefId {
        *self.call_stack.last().unwrap()
    }

    pub fn push_function(&mut self, func_def_id: DefId) {
        self.call_stack.push(func_def_id);
        self.visited_functions.insert(func_def_id);
    }

    pub fn pop_function(&mut self) {
        let func_def_id = self.call_stack.pop().unwrap();
        self.visited_functions.remove(&func_def_id);
    }

    #[inline(always)]
    pub fn is_revisiting_visited_function(&self) -> bool {
        self.visited_functions.len() < self.call_stack.len()
    }

    pub fn is_basic_block_visited(&self, bb: mir::BasicBlock) -> bool {
        let waypoint = (self.stack_top_func_def_id(), bb.as_usize());
        self.visited_bbs.contains(&waypoint)
    }

    pub fn push_basic_block(&mut self, bb: mir::BasicBlock) {
        let waypoint = (self.stack_top_func_def_id(), bb.as_usize());
        self.bb_trace.push(waypoint);
        self.visited_bbs.insert(waypoint);
    }

    pub fn pop_basic_block(&mut self) {
        let waypoint = self.bb_trace.pop().unwrap();
        self.visited_bbs.remove(&waypoint);
    }
}

pub struct ExecutionPathWithTcx<'a, 'tcx> {
    pub path: &'a ExecutionPath,
    pub tcx: TyCtxt<'tcx>,
}

impl fmt::Debug for ExecutionPathWithTcx<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Stack: [")?;
        for (idx, func_def_id) in self.path.call_stack.iter().enumerate() {
            let func_name = self.tcx.def_path_str(func_def_id);
            let (func_crt, func_idx) = (func_def_id.krate.as_u32(), func_def_id.index.as_u32());
            write!(f, "<{}:{}> {}", func_crt, func_idx, func_name)?;
            if idx != self.path.call_stack.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]\nPath: ")?;
        for (idx, (func_def_id, bb)) in self.path.bb_trace.iter().enumerate() {
            let (func_crt, func_idx) = (func_def_id.krate.as_u32(), func_def_id.index.as_u32());
            write!(f, "<{}:{}>.bb{}", func_crt, func_idx, bb)?;
            if idx != self.path.bb_trace.len() - 1 {
                write!(f, " -> ")?;
            }
        }
        Ok(())
    }
}
