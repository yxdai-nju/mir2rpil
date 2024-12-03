use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

use std::fmt;

use crate::path::ExecutionPathWithTcx;

use super::path::ExecutionPath;
use super::rpil::{LowRpilInst, LowRpilOp};

#[derive(Debug, Clone)]
enum StatusChange {
    Pin,
    Move,
    Forget,
}

#[derive(Clone)]
pub struct TranslationCtxt {
    execution_path: ExecutionPath,
    mapping: FxHashMap<LowRpilOp, (LowRpilOp, usize)>,
    status_changes: Vec<(LowRpilOp, StatusChange, usize)>,
    serial: usize,
}

impl TranslationCtxt {
    pub fn from_function_def(func_def_id: DefId) -> Self {
        let mut execution_path = ExecutionPath::new();
        execution_path.push_function(func_def_id);
        Self {
            execution_path,
            mapping: FxHashMap::default(),
            status_changes: vec![],
            serial: 0,
        }
    }

    pub fn eval(&mut self, inst: LowRpilInst) {
        println!("[Low RPIL] {:?}", inst);
        match inst {
            LowRpilInst::CallFunc {
                def_id: func_def_id,
                ret: ret_local_op,
                arg_ops,
            } => {
                let depth = self.execution_path.stack_depth();

                // Insert a mapping for the return place
                let sub_ret_op = LowRpilOp::UpLocal {
                    depth: depth + 1,
                    index: 0,
                };
                let ret_op = LowRpilOp::local_with_depth(ret_local_op, depth);
                self.insert_mapping(sub_ret_op, ret_op);

                // Insert mappings for argument places
                for (idx, arg_local_op) in arg_ops.into_iter().enumerate() {
                    let sub_arg_op = LowRpilOp::UpLocal {
                        depth: depth + 1,
                        index: idx + 1,
                    };
                    let arg_op = LowRpilOp::local_with_depth(arg_local_op, depth);
                    self.insert_mapping(sub_arg_op, arg_op);
                }

                // Push function DefId onto the call stack
                self.execution_path.push_function(func_def_id);
            }
            LowRpilInst::CallClosure {
                closure,
                ret,
                args_op,
            } => {
                let depth = self.execution_path.stack_depth();
            }
            LowRpilInst::Assign { lhs, rhs } => unimplemented!(),
            LowRpilInst::Pin(op) => unimplemented!(),
            LowRpilInst::Move(op) => unimplemented!(),
            LowRpilInst::Forget(op) => unimplemented!(),
            LowRpilInst::EnterBasicBlock { bb } => {
                self.execution_path.push_basic_block(bb);
            }
            LowRpilInst::LeaveBasicBlock => {
                self.execution_path.pop_basic_block();
            }
            LowRpilInst::Return => {
                self.execution_path.pop_function();
            }
        }
    }

    pub fn is_basic_block_visited(&self, bb: mir::BasicBlock) -> bool {
        self.execution_path.is_basic_block_visited(bb)
    }

    fn insert_mapping(&mut self, key: LowRpilOp, value: LowRpilOp) {
        self.mapping.insert(key, (value, self.serial));
        self.serial += 1;
    }
}

pub struct TranslationCtxtWithTcx<'a, 'tcx> {
    pub trcx: &'a TranslationCtxt,
    pub tcx: TyCtxt<'tcx>,
}

impl fmt::Debug for TranslationCtxtWithTcx<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let execution_path_with_tcx = ExecutionPathWithTcx {
            path: &self.trcx.execution_path,
            tcx: self.tcx,
        };
        write!(
            f,
            "{:?}\nCtxt: {:?} {:?}",
            execution_path_with_tcx, self.trcx.mapping, self.trcx.status_changes
        )
    }
}
