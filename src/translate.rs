use rustc_data_structures::graph::StartNode;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{FnDef, TyCtxt};

use std::mem::discriminant;

use super::context::TranslationCtxt;
use super::debug;
use super::rpil::{LowRpilInst, LowRpilOp, RpilInst};

pub fn translate_function_def(tcx: TyCtxt<'_>, func_def_id: DefId) -> Vec<Vec<RpilInst>> {
    debug::log_func_mir(tcx, func_def_id);

    let func_name = tcx.def_path_str(func_def_id);
    let func_idx = func_def_id.index.as_u32();
    let func_argc = tcx.fn_arg_names(func_def_id).len();
    if !tcx.is_mir_available(func_def_id) {
        println!("    (empty)");
        return vec![vec![]];
    }

    println!("===== Entered function '{}' {} =====", func_name, func_idx);
    let trcx = TranslationCtxt::from_function_def(func_def_id);
    let func_body = tcx.optimized_mir(func_def_id);
    let bb0 = func_body.basic_blocks.start_node();
    let trcx_variants = translate_basic_block(tcx, trcx, func_body, bb0);
    println!("===== Leaving function '{}' {} =====", func_name, func_idx);

    vec![vec![]]
}

fn translate_basic_block(
    tcx: TyCtxt<'_>,
    mut trcx: TranslationCtxt,
    func_body: &mir::Body,
    bb: mir::BasicBlock,
) -> Vec<TranslationCtxt> {
    trcx.eval(LowRpilInst::EnterBasicBlock { bb });
    debug::log_translation_context(tcx, &trcx);

    let bb_data = func_body.basic_blocks.get(bb).unwrap();
    for statement in &bb_data.statements {
        // translate_statement(tcx, trcx, statement);
    }
    let terminator = bb_data.terminator();
    let (mut trcx_variants, next_bb) = translate_terminator(tcx, trcx, terminator);

    match next_bb {
        Some(ref next_bbs) => {
            println!("Next: {:?}", next_bbs);
            println!("-----");
            trcx_variants = trcx_variants
                .into_iter()
                .flat_map(|trcx| {
                    next_bbs.iter().copied().flat_map(move |bb| {
                        if trcx.is_basic_block_visited(bb) {
                            return vec![];
                        }
                        translate_basic_block(tcx, trcx.clone(), func_body, bb)
                    })
                })
                .collect();
        }
        None => {
            println!("Next: return");
            println!("-----");
        }
    };

    for trcx in trcx_variants.iter_mut() {
        trcx.eval(LowRpilInst::LeaveBasicBlock);
    }

    trcx_variants
}

fn translate_terminator(
    tcx: TyCtxt<'_>,
    mut trcx: TranslationCtxt,
    terminator: &mir::Terminator,
) -> (Vec<TranslationCtxt>, Option<Vec<mir::BasicBlock>>) {
    let terminator = &terminator.kind;
    match terminator {
        mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            let arg_list: Vec<_> = args.iter().map(|s| s.node.clone()).collect();
            println!(
                "[MIR Term] Assign(({:?}, {:?}{:?}))",
                destination, func, arg_list
            );
            let func_def_id = get_def_id_from_fndef_operand(func);
            // println!("Function Name: {}", tcx.def_path_str(func_def_id));
            // println!("Function Args: {:?}", arg_list);

            let trcx_variants;
            if is_function_excluded(tcx, func_def_id) {
                trcx_variants = vec![trcx];
            } else if is_function_fn_trait_shim(tcx, func_def_id) {
                assert_eq!(arg_list.len(), 2);
                let closure_place = match &arg_list[0] {
                    mir::Operand::Move(place) => place,
                    _ => unreachable!(),
                };
                let closure_args_place = match &arg_list[1] {
                    mir::Operand::Move(place) => place,
                    _ => unreachable!(),
                };
                trcx.eval(LowRpilInst::CallClosure {
                    closure: LowRpilOp::from_mir_place(closure_place),
                    ret: LowRpilOp::from_mir_place(destination),
                    args_op: LowRpilOp::from_mir_place(closure_args_place),
                });
                trcx_variants = translate_function_call(tcx, trcx);
            } else {
                let arg_ops = arg_list
                    .iter()
                    .filter_map(|arg_operand| match arg_operand {
                        mir::Operand::Copy(_) => unreachable!(),
                        mir::Operand::Move(arg_place) => {
                            let arg_op = LowRpilOp::from_mir_place(arg_place);
                            Some(arg_op)
                        }
                        mir::Operand::Constant(_) => None,
                    })
                    .collect();
                trcx.eval(LowRpilInst::CallFunc {
                    def_id: func_def_id,
                    ret: LowRpilOp::from_mir_place(destination),
                    arg_ops,
                });
                trcx_variants = translate_function_call(tcx, trcx);
            }
            (trcx_variants, Some(target.map_or(vec![], |bb| vec![bb])))
        }
        mir::TerminatorKind::Goto { target }
        | mir::TerminatorKind::Assert { target, .. }
        | mir::TerminatorKind::Drop { target, .. } => (vec![trcx], Some(vec![*target])),
        mir::TerminatorKind::SwitchInt {
            discr, ref targets, ..
        } => {
            println!("[Term] SwitchInt({:?})", discr);
            (vec![trcx], Some(targets.all_targets().into()))
        }
        mir::TerminatorKind::Return => {
            trcx.eval(LowRpilInst::Return);
            (vec![trcx], None)
        }
        mir::TerminatorKind::UnwindResume | mir::TerminatorKind::Unreachable => {
            (vec![trcx], Some(vec![]))
        }
        _ => {
            let x = discriminant(terminator);
            println!("[Term-{:?}] Unknown `{:?}`", x, terminator);
            unimplemented!()
        }
    }
}

fn translate_function_call(tcx: TyCtxt<'_>, trcx: TranslationCtxt) -> Vec<TranslationCtxt> {
    vec![trcx]
}

// fn translate_function_call<'tcx>(tcx: TyCtxt<'tcx>, trcx: &mut TranslationCtxt) {
//     trcx.translate_function_call_with_each_variant(|trcx_variant, def_id| {
//         debug::log_func_mir(tcx, def_id);

//         let func_name = tcx.def_path_str(def_id);
//         let func_idx = def_id.index.as_u32();
//         if !tcx.is_mir_available(def_id) {
//             println!("    (empty)");
//             return;
//         }

//         trcx_variant.enter_function(func_name.as_str());
//         println!("===== Entered function `{}` {} =====", func_name, func_idx);

//         let func_body = tcx.optimized_mir(def_id);
//         let bb0 = func_body.basic_blocks.start_node();
//         let mut snapshots = vec![];
//         translate_basic_block(tcx, trcx_variant, func_body, bb0, &mut snapshots);
//         trcx_variant.gather_variants(snapshots);

//         trcx_variant.leave_function();
//         println!("===== Leaving function `{}` {} =====", func_name, func_idx);
//     });
// }

// fn translate_statement<'tcx>(
//     tcx: TyCtxt<'tcx>,
//     trcx: &mut TranslationCtxt,
//     statement: &mir::Statement<'tcx>,
// ) {
//     let statement = &statement.kind;
//     match statement {
//         mir::StatementKind::Assign(p) => {
//             println!("[MIR Stmt] {:?}", statement);
//             let (lplace, rvalue) = &**p;
//             translate_statement_of_assign(tcx, trcx, lplace, rvalue);
//         }
//         mir::StatementKind::Intrinsic(intrinsic_func) => {
//             println!("[MIR Stmt] {:?}", statement);
//             match &**intrinsic_func {
//                 mir::NonDivergingIntrinsic::Assume(..) => {}
//                 mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
//                     println!("[MIR-Intrinsic] CopyNonOverlapping({:?})", cno);
//                     unimplemented!();
//                 }
//             }
//         }
//         mir::StatementKind::StorageDead(..)
//         | mir::StatementKind::StorageLive(..)
//         | mir::StatementKind::Retag(..)
//         | mir::StatementKind::PlaceMention(..) => {}
//         _ => {
//             let x = discriminant(statement);
//             println!("[MIR Stmt-{:?}] Unknown `{:?}`", x, statement);
//             unimplemented!();
//         }
//     }
// }

// fn translate_statement_of_assign<'tcx>(
//     tcx: TyCtxt<'tcx>,
//     trcx: &mut TranslationCtxt,
//     lplace: &mir::Place<'tcx>,
//     rvalue: &mir::Rvalue<'tcx>,
// ) {
//     let lhs = LowRpilOp::from_mir_place(lplace, trcx.depth);
//     match rvalue {
//         mir::Rvalue::Use(operand) | mir::Rvalue::Cast(_, operand, _) => {
//             // if let mir::Rvalue::Use(_) = rvalue {
//             //     println!("[Rvalue] Use({:?})", operand);
//             // } else {
//             //     println!("[Rvalue] Cast({:?})", operand);
//             // }
//             match operand {
//                 mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => {
//                     trcx.push_rpil_inst(LowRpilInst::Assign {
//                         lhs,
//                         rhs: LowRpilOp::from_mir_place(rplace, trcx.depth),
//                     });
//                 }
//                 mir::Operand::Constant(_) => {}
//             }
//         }
//         mir::Rvalue::Aggregate(aggregate, values) => {
//             // println!("[Rvalue] Aggregate({:?}, {:?})", aggregate, values);
//             translate_statement_of_assign_aggregate(tcx, trcx, &lhs, rvalue);
//         }
//         mir::Rvalue::Ref(_, kind, rplace) => {
//             let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
//             match kind {
//                 mir::BorrowKind::Shared => {
//                     // println!("[Rvalue] Ref(Shared, {:?})", rplace);
//                     trcx.push_rpil_inst(LowRpilInst::Assign {
//                         lhs,
//                         rhs: LowRpilOp::Ref(Box::new(rhs)),
//                     });
//                 }
//                 mir::BorrowKind::Mut { kind } => {
//                     // println!("[Rvalue] Ref(Mut({:?}), {:?})", kind, rplace);
//                     trcx.push_rpil_inst(LowRpilInst::Assign {
//                         lhs,
//                         rhs: LowRpilOp::MutRef(Box::new(rhs)),
//                     });
//                 }
//                 mir::BorrowKind::Fake(kind) => {
//                     println!("[Rvalue] Ref(Fake({:?}), {:?})", kind, rplace);
//                     unimplemented!();
//                 }
//             };
//         }
//         mir::Rvalue::CopyForDeref(rplace) => {
//             // println!("[Rvalue] CopyForDeref({:?})", rplace);
//             trcx.push_rpil_inst(LowRpilInst::Assign {
//                 lhs,
//                 rhs: LowRpilOp::from_mir_place(rplace, trcx.depth),
//             });
//         }
//         mir::Rvalue::ShallowInitBox(op, ty) => {
//             // println!("[Rvalue] ShallowInitBox({:?}, {:?})", op, ty);
//             match op {
//                 mir::Operand::Move(_ptr) => {
//                     // The `lhs = ShallowInitBox(ptr, T)` operation is similar to
//                     // `lhs = Box::<T>::from_raw(ptr, ..)`. It's sufficient to know
//                     // that the reference stored within lhs (lhs.p0.p0.p0)
//                     // points to some external (heap) location, which we represent
//                     // as lhs.ext.
//                     //
//                     // Therefore, we omit the ptr argument and interpret this
//                     // operation as: lhs.p0.p0.p0 = &mut lhs.ext;
//                     let ptr = LowRpilOp::Place {
//                         base: Box::new(LowRpilOp::Place {
//                             base: Box::new(LowRpilOp::Place {
//                                 base: Box::new(lhs.clone()),
//                                 place_desc: PlaceDesc::P(0),
//                             }),
//                             place_desc: PlaceDesc::P(0),
//                         }),
//                         place_desc: PlaceDesc::P(0),
//                     };
//                     let ext_place = LowRpilOp::Place {
//                         base: Box::new(lhs),
//                         place_desc: PlaceDesc::PExt,
//                     };
//                     trcx.push_rpil_inst(LowRpilInst::Assign {
//                         lhs: ptr,
//                         rhs: LowRpilOp::MutRef(Box::new(ext_place)),
//                     });
//                 }
//                 mir::Operand::Copy(..) | mir::Operand::Constant(..) => {
//                     unimplemented!();
//                 }
//             }
//         }
//         mir::Rvalue::Discriminant(..)
//         | mir::Rvalue::NullaryOp(..)
//         | mir::Rvalue::UnaryOp(..)
//         | mir::Rvalue::BinaryOp(..) => {}
//         _ => {
//             let x = discriminant(rvalue);
//             println!("[Rvalue-{:?}] Unknown `{:?}`", x, rvalue);
//             unimplemented!();
//         }
//     }
// }

// fn translate_statement_of_assign_aggregate<'tcx>(
//     tcx: TyCtxt<'tcx>,
//     trcx: &mut TranslationCtxt,
//     lhs: &LowRpilOp,
//     rvalue: &mir::Rvalue<'tcx>,
// ) {
//     let (aggregate, values) = match rvalue {
//         mir::Rvalue::Aggregate(aggregate, values) => (&**aggregate, values),
//         _ => unreachable!(),
//     };
//     match aggregate {
//         mir::AggregateKind::Array(..) | mir::AggregateKind::Tuple => {
//             if let mir::AggregateKind::Array(..) = aggregate {
//                 println!("[Aggregate] Array({:?})", values);
//             } else {
//                 println!("[Aggregate] Tuple({:?})", values);
//             }
//             for (lidx, value) in values.iter().enumerate() {
//                 let lhs_place = LowRpilOp::Place {
//                     base: Box::new(lhs.clone()),
//                     place_desc: PlaceDesc::P(lidx),
//                 };
//                 handle_aggregate(trcx, lhs_place, value);
//             }
//         }
//         mir::AggregateKind::Adt(_, variant_idx, _, _, _) => {
//             println!("[Aggregate] Adt(variant_idx={:?})", variant_idx);
//             for (lidx, value) in values.iter().enumerate() {
//                 let lhs_place = LowRpilOp::Place {
//                     base: Box::new(lhs.clone()),
//                     place_desc: PlaceDesc::V(variant_idx.as_usize()),
//                 };
//                 let lhs_place = LowRpilOp::Place {
//                     base: Box::new(lhs_place),
//                     place_desc: PlaceDesc::P(lidx),
//                 };
//                 handle_aggregate(trcx, lhs_place, value);
//             }
//         }
//         mir::AggregateKind::Closure(def_id, _) => {
//             println!("[Aggregate] Closure(def_id={})", def_id.index.as_u32());
//             let def_id = *def_id;
//             debug::log_func_mir(tcx, def_id);
//             trcx.push_rpil_inst(LowRpilInst::Assign {
//                 lhs: lhs.clone(),
//                 rhs: LowRpilOp::Closure { def_id },
//             });
//             for (lidx, value) in values.iter().enumerate() {
//                 let lhs_place = LowRpilOp::Place {
//                     base: Box::new(lhs.clone()),
//                     place_desc: PlaceDesc::P(lidx),
//                 };
//                 handle_aggregate(trcx, lhs_place, value);
//             }
//         }
//         _ => {
//             let x = discriminant(aggregate);
//             println!("[Aggregate-{:?}] Unknown `{:?}`", x, aggregate);
//             unimplemented!();
//         }
//     };
// }

// fn handle_aggregate<'tcx>(trcx: &mut TranslationCtxt, lhs: LowRpilOp, value: &mir::Operand<'tcx>) {
//     match value {
//         mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => {
//             let rhs = LowRpilOp::from_mir_place(rplace, trcx.depth);
//             trcx.push_rpil_inst(LowRpilInst::Assign { lhs, rhs });
//         }
//         mir::Operand::Constant(_) => {}
//     }
// }

fn is_function_excluded<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let excluded_from_translation: rustc_data_structures::fx::FxHashSet<&str> =
        ["alloc::alloc::exchange_malloc"].iter().cloned().collect();
    let def_path = tcx.def_path_str(def_id);
    excluded_from_translation.contains(def_path.as_str())
}

fn is_function_fn_trait_shim<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);
    def_path.contains("::call")
        && (def_path.contains("std::ops::Fn")
            || def_path.contains("std::ops::FnMut")
            || def_path.contains("std::ops::FnOnce"))
}

fn get_def_id_from_fndef_operand(func: &mir::Operand<'_>) -> DefId {
    match func {
        mir::Operand::Constant(operand) => match operand.const_ {
            mir::Const::Val(_, fn_def) => match fn_def.kind() {
                FnDef(def_id, _) => *def_id,
                _ => unimplemented!(),
            },
            mir::Const::Unevaluated(_, _) | mir::Const::Ty(_, _) => unimplemented!(),
        },
        mir::Operand::Copy(_) | mir::Operand::Move(_) => unimplemented!(),
    }
}
