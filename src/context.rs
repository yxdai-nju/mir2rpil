use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

use std::fmt;

use super::path::{ExecutionPath, ExecutionPathWithTcx};
use super::rpil::{LowRpilInst, LowRpilOp, PlaceDesc, RpilInst, StatusChange};
use super::rpilmap::LowRpilMap;
use super::serialmap::{SerialMap, SerialMapForUnaryRecursive};

#[derive(Clone)]
pub struct TranslationCtxt {
    execution_path: ExecutionPath,
    mapping: LowRpilMap,
    status_changes: Vec<(LowRpilOp, StatusChange, usize)>,
    serial: usize,
    variant: Vec<usize>,
}

impl TranslationCtxt {
    pub fn from_function_def_id(func_def_id: DefId) -> Self {
        let mut execution_path = ExecutionPath::new();
        execution_path.push_function(func_def_id);
        Self {
            execution_path,
            mapping: LowRpilMap::new(),
            status_changes: vec![],
            serial: 0,
            variant: vec![],
        }
    }

    pub fn eval(&mut self, inst: LowRpilInst) {
        if let LowRpilInst::Return | LowRpilInst::LeaveBasicBlock = inst {
        } else {
            println!("[Low RPIL] {:?}", inst);
        }
        match inst {
            LowRpilInst::CallFunc {
                def_id: func_def_id,
                ret: ret_local_op,
                arg_ops,
            } => {
                self.handle_function_call(func_def_id, ret_local_op, arg_ops);
            }
            LowRpilInst::CallClosure {
                closure: closure_local_op,
                ret: ret_local_op,
                args_op,
            } => {
                self.handle_closure_call(closure_local_op, ret_local_op, args_op);
            }
            LowRpilInst::Assign {
                lhs: lhs_local_op,
                rhs: rhs_local_op,
            } => {
                let lhs = self.local_rpil_op_into_reduced_op_with_depth(lhs_local_op);
                let rhs = self.local_rpil_op_into_reduced_op_with_depth(rhs_local_op);
                self.insert_mapping(lhs, rhs);
                println!("Ctxt: {:?}", self);
            }
            LowRpilInst::Pin(local_op) => {
                let op = self.local_rpil_op_into_reduced_op_with_depth(local_op);
                self.insert_status_change(op, StatusChange::Pin);
            }
            LowRpilInst::Move(local_op) => {
                let op = self.local_rpil_op_into_reduced_op_with_depth(local_op);
                self.insert_status_change(op, StatusChange::Move);
            }
            LowRpilInst::Forget(local_op) => {
                let op = self.local_rpil_op_into_reduced_op_with_depth(local_op);
                self.insert_status_change(op, StatusChange::Forget);
            }
            LowRpilInst::EnterBasicBlock { bb } => {
                self.execution_path.push_basic_block(bb);
            }
            LowRpilInst::LeaveBasicBlock => {
                self.execution_path.pop_basic_block();
            }
            LowRpilInst::Return => {
                let max_depth = self.execution_path.stack_depth();
                if max_depth > 1 {
                    self.mapping.remove_over_depth_mapping(max_depth);
                }
                self.execution_path.pop_function();
            }
        }
    }

    #[inline(always)]
    pub fn is_revisiting_visited_function(&self) -> bool {
        self.execution_path.is_revisiting_visited_function()
    }

    #[inline(always)]
    pub fn is_basic_block_visited(&self, bb: mir::BasicBlock) -> bool {
        self.execution_path.is_basic_block_visited(bb)
    }

    #[inline(always)]
    pub fn stack_top_function_def_id(&self) -> DefId {
        self.execution_path.stack_top_func_def_id()
    }

    #[inline(always)]
    pub fn mark_variant(&mut self, variant_idx: usize) {
        self.variant.push(variant_idx);
    }

    pub fn variant_string(&self) -> String {
        self.variant
            .iter()
            .map(|idx| idx.to_string())
            .collect::<String>()
    }

    fn handle_function_call(
        &mut self,
        func_def_id: DefId,
        ret_local_op: LowRpilOp,
        arg_ops: Vec<LowRpilOp>,
    ) {
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

    fn handle_closure_call(
        &mut self,
        closure_local_op: LowRpilOp,
        ret_local_op: LowRpilOp,
        args_op: LowRpilOp,
    ) {
        let depth = self.execution_path.stack_depth();

        // Insert a mapping for the return place
        let sub_ret_op = LowRpilOp::UpLocal {
            depth: depth + 1,
            index: 0,
        };
        let ret_op = LowRpilOp::local_with_depth(ret_local_op, depth);
        self.insert_mapping(sub_ret_op, ret_op);

        // Insert a mapping for the closure place
        let sub_closure_op = LowRpilOp::UpLocal {
            depth: depth + 1,
            index: 1,
        };
        let closure_op = LowRpilOp::local_with_depth(closure_local_op, depth);
        self.insert_mapping(sub_closure_op, closure_op.clone());

        // Insert mappings for argument places
        let mut to_insert = vec![];
        for (key, val, _serial) in self.mapping.iter() {
            let place_index = match key {
                LowRpilOp::Place {
                    base,
                    place_desc: PlaceDesc::P(place_index),
                } if **base == args_op => place_index,
                _ => continue,
            };
            let sub_arg_op = LowRpilOp::UpLocal {
                depth: depth + 1,
                index: place_index + 2,
            };
            let arg_op = LowRpilOp::local_with_depth(val.clone(), depth);
            to_insert.push((sub_arg_op, arg_op));
        }
        for (sub_arg_op, arg_op) in to_insert {
            self.insert_mapping(sub_arg_op, arg_op);
        }

        // Push the closure's function DefId onto the call stack
        let func_def_id = self.mapped_rpil_op(&closure_op).assume_closure().unwrap();
        self.execution_path.push_function(func_def_id);
    }
}

// Mapping-related operations
impl TranslationCtxt {
    fn insert_mapping(&mut self, lhs: LowRpilOp, rhs: LowRpilOp) {
        self.mapping.insert(lhs, rhs, self.serial);
        self.serial += 1;
    }

    fn mapped_rpil_op(&self, op: &LowRpilOp) -> LowRpilOp {
        if let Some(mapped_op) = self.mapping.get(op) {
            self.mapped_rpil_op(mapped_op)
        } else {
            op.clone()
        }
    }

    fn reduced_rpil_op(&self, op: &LowRpilOp) -> LowRpilOp {
        self.mapped_rpil_op(&match op {
            LowRpilOp::Local { .. } | LowRpilOp::UpLocal { .. } | LowRpilOp::Closure { .. } => {
                op.clone()
            }
            LowRpilOp::Place { base, place_desc } => LowRpilOp::Place {
                base: Box::new(self.reduced_rpil_op(base)),
                place_desc: place_desc.clone(),
            },
            LowRpilOp::Ref(inner_op) => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                // Turn `Ref(Deref(op))` into `op` when possible
                match reduced_inner_op {
                    LowRpilOp::Deref(referenced_op) => *referenced_op.clone(),
                    _ => LowRpilOp::Ref(Box::new(reduced_inner_op)),
                }
            }
            LowRpilOp::Deref(inner_op) => {
                let reduced_inner_op = self.reduced_rpil_op(inner_op);
                // Turn `Deref(Ref(op))` into `op` when possible
                match reduced_inner_op {
                    LowRpilOp::Ref(referenced_op) => *referenced_op.clone(),
                    _ => LowRpilOp::Deref(Box::new(reduced_inner_op)),
                }
            }
        })
    }

    fn local_rpil_op_into_reduced_op_with_depth(&self, local_op: LowRpilOp) -> LowRpilOp {
        let depth = self.execution_path.stack_depth();
        let op = LowRpilOp::with_depth(local_op, depth);
        self.reduced_rpil_op(&op)
    }
}

// Status-change-related operations
impl TranslationCtxt {
    fn insert_status_change(&mut self, op: LowRpilOp, status_change: StatusChange) {
        self.status_changes.push((op, status_change, self.serial));
        self.serial += 1;
    }
}

// RPIL conversion
impl TranslationCtxt {
    pub fn into_rpil_insts(mut self, func_argc: usize) -> Vec<RpilInst> {
        assert_eq!(self.execution_path.stack_depth(), 0);
        self.mapping.expand_to_transitive_closure();
        let assignments: Vec<_> = self
            .mapping
            .into_iter()
            .filter(|(low_lhs, low_rhs, _)| {
                matches!(
                    (low_lhs.origin_index(), low_rhs.origin_index()),
                    (Some(key_index), Some(val_index))
                        if key_index <= func_argc && val_index <= func_argc
                )
            })
            .map(|(low_lhs, low_rhs, serial)| {
                let inst = RpilInst::from_low_rpil_assignment(low_lhs, low_rhs);
                (inst, serial)
            })
            .collect();
        let status_changes: Vec<_> = self
            .status_changes
            .into_iter()
            .map(|(low_op, status_change, serial)| {
                let inst = RpilInst::from_low_rpil_status_change(low_op, status_change);
                (inst, serial)
            })
            .collect();
        let mut insts_with_serial: Vec<_> = assignments.into_iter().chain(status_changes).collect();
        insts_with_serial.sort_by_key(|(_, serial)| *serial);

        insts_with_serial
            .into_iter()
            .map(|(inst, _)| inst)
            .collect()
    }
}

impl fmt::Debug for TranslationCtxt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut entries: Vec<_> = self.mapping.iter().collect();
        entries.sort_by_key(|(_, _, serial)| *serial);
        let sorted_entries = entries;
        write!(f, "{{")?;
        for (i, (key, val, _serial)) in sorted_entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}: ({:?})", key, val)?;
        }
        write!(f, "}} {:?}", self.status_changes)
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
        write!(f, "{:?}\nCtxt: {:?}", execution_path_with_tcx, self.trcx)
    }
}
