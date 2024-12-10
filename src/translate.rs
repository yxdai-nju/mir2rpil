use rustc_data_structures::graph::StartNode;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{FnDef, TyCtxt};

use std::mem::discriminant;

use super::context::TranslationCtxt;
use super::debug;
use super::rpil::{LowRpilInst, LowRpilOp, PlaceDesc, RpilInst};

pub fn translate_function_def(tcx: TyCtxt<'_>, func_def_id: DefId) -> Vec<Vec<RpilInst>> {
    debug::log_func_mir(tcx, func_def_id);

    let func_name = tcx.def_path_str(func_def_id);
    let func_argc = tcx.fn_arg_names(func_def_id).len();
    if !tcx.is_mir_available(func_def_id) {
        println!("    (empty)");
        return vec![vec![]];
    }

    let (func_crt, func_idx) = (func_def_id.krate.as_u32(), func_def_id.index.as_u32());
    println!(
        "===== Translating function '{}' {}:{} =====",
        func_name, func_crt, func_idx
    );
    let trcx = TranslationCtxt::from_function_def_id(func_def_id);
    let func_body = tcx.optimized_mir(func_def_id);
    let bb0 = func_body.basic_blocks.start_node();
    let trcx_variants = translate_basic_block(tcx, trcx, func_body, bb0);

    trcx_variants
        .into_iter()
        .map(|trcx| trcx.into_rpil_insts(func_argc))
        .collect()
}

fn translate_basic_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut trcx: TranslationCtxt,
    func_body: &mir::Body<'tcx>,
    bb: mir::BasicBlock,
) -> Vec<TranslationCtxt> {
    println!("----- {}", trcx.variant_string());
    trcx.eval(LowRpilInst::EnterBasicBlock { bb });
    debug::log_translation_context(tcx, &trcx);

    let bb_data = func_body.basic_blocks.get(bb).unwrap();
    for statement in &bb_data.statements {
        trcx = translate_statement(tcx, trcx, statement);
    }
    let terminator = bb_data.terminator();
    let (mut trcx_variants, next_bb) = translate_terminator(tcx, trcx, terminator);

    match next_bb {
        Some(ref next_bbs) => {
            println!("Next: {:?}", next_bbs);
            trcx_variants = trcx_variants
                .into_iter()
                .flat_map(|trcx| {
                    let next_unvisited_bbs: Vec<_> = next_bbs
                        .iter()
                        .copied()
                        .filter(|bb| !trcx.is_basic_block_visited(*bb))
                        .collect();
                    let unvisited_bb_count = next_unvisited_bbs.len();
                    next_unvisited_bbs
                        .into_iter()
                        .enumerate()
                        .flat_map(move |(variant_idx, bb)| {
                            let mut trcx_variant = trcx.clone();
                            if unvisited_bb_count > 1 {
                                trcx_variant.mark_variant(variant_idx);
                            }
                            translate_basic_block(tcx, trcx_variant, func_body, bb)
                        })
                })
                .collect();
        }
        None => {
            println!("Next: return");
            for trcx in trcx_variants.iter_mut() {
                trcx.eval(LowRpilInst::Return);
            }
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
                trcx_variants = if trcx.is_revisiting_visited_function() {
                    vec![]
                } else {
                    translate_function_call(tcx, trcx)
                }
            } else {
                let arg_ops = arg_list
                    .iter()
                    .filter_map(|arg_operand| match arg_operand {
                        mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
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
                trcx_variants = if trcx.is_revisiting_visited_function() {
                    vec![]
                } else {
                    translate_function_call(tcx, trcx)
                }
            }
            (
                trcx_variants,
                target.map_or(Some(vec![]), |bb| Some(vec![bb])),
            )
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
        mir::TerminatorKind::Return => (vec![trcx], None),
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

fn translate_function_call(tcx: TyCtxt<'_>, mut trcx: TranslationCtxt) -> Vec<TranslationCtxt> {
    let func_def_id = trcx.stack_top_function_def_id();
    debug::log_func_mir(tcx, func_def_id);

    if !tcx.is_mir_available(func_def_id) {
        trcx.eval(LowRpilInst::Return);
        return vec![trcx];
    }

    let (func_crt, func_idx) = (func_def_id.krate.as_u32(), func_def_id.index.as_u32());
    println!("{}:{} (", func_crt, func_idx);
    let func_body = tcx.optimized_mir(func_def_id);
    let bb0 = func_body.basic_blocks.start_node();
    let trcx_variants = translate_basic_block(tcx, trcx, func_body, bb0);
    println!(") {}:{}", func_crt, func_idx);

    trcx_variants
}

fn translate_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut trcx: TranslationCtxt,
    statement: &mir::Statement<'tcx>,
) -> TranslationCtxt {
    let statement = &statement.kind;
    match statement {
        mir::StatementKind::Assign(p) => {
            println!("[MIR Stmt] {:?}", statement);
            let (lplace, rvalue) = &**p;
            trcx = translate_statement_of_assign(tcx, trcx, lplace, rvalue);
        }
        mir::StatementKind::Intrinsic(intrinsic_func) => {
            println!("[MIR Stmt] {:?}", statement);
            match &**intrinsic_func {
                mir::NonDivergingIntrinsic::Assume(..) => {}
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    println!("[MIR-Intrinsic] CopyNonOverlapping({:?})", cno);
                    unimplemented!();
                }
            }
        }
        mir::StatementKind::StorageDead(..)
        | mir::StatementKind::StorageLive(..)
        | mir::StatementKind::Retag(..)
        | mir::StatementKind::PlaceMention(..) => {}
        _ => {
            let x = discriminant(statement);
            println!("[MIR Stmt-{:?}] Unknown `{:?}`", x, statement);
            unimplemented!();
        }
    }

    trcx
}

fn translate_statement_of_assign<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut trcx: TranslationCtxt,
    lplace: &mir::Place<'tcx>,
    rvalue: &mir::Rvalue<'tcx>,
) -> TranslationCtxt {
    let lhs = LowRpilOp::from_mir_place(lplace);
    match rvalue {
        mir::Rvalue::Use(operand) | mir::Rvalue::Cast(_, operand, _) => {
            // if let mir::Rvalue::Use(_) = rvalue {
            //     println!("[Rvalue] Use({:?})", operand);
            // } else {
            //     println!("[Rvalue] Cast({:?})", operand);
            // }
            match operand {
                mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => {
                    let rhs = LowRpilOp::from_mir_place(rplace);
                    trcx.eval(LowRpilInst::Assign { lhs, rhs });
                }
                mir::Operand::Constant(_) => {}
            }
        }
        mir::Rvalue::CopyForDeref(rplace) => {
            // println!("[Rvalue] CopyForDeref({:?})", rplace);
            let rhs = LowRpilOp::from_mir_place(rplace);
            trcx.eval(LowRpilInst::Assign { lhs, rhs });
        }
        mir::Rvalue::Ref(_, kind, rplace) => {
            let rhs_inner = LowRpilOp::from_mir_place(rplace);
            match kind {
                mir::BorrowKind::Shared | mir::BorrowKind::Mut { .. } => {
                    // println!("[Rvalue] Ref(Shared, {:?})", rplace);
                    let rhs = LowRpilOp::Ref(Box::new(rhs_inner));
                    trcx.eval(LowRpilInst::Assign { lhs, rhs });
                }
                mir::BorrowKind::Fake(kind) => {
                    println!("[Rvalue] Ref(Fake({:?}), {:?})", kind, rplace);
                    unimplemented!();
                }
            };
        }
        mir::Rvalue::RawPtr(_, rplace) => {
            println!("[Rvalue] RawPtr({:?})", rplace);
            let rhs_inner = LowRpilOp::from_mir_place(rplace);
            let rhs = LowRpilOp::Ref(Box::new(rhs_inner));
            trcx.eval(LowRpilInst::Assign { lhs, rhs });
        }
        mir::Rvalue::Aggregate(aggregate, values) => {
            println!("[Rvalue] Aggregate({:?}, {:?})", aggregate, values);
            trcx = translate_statement_of_assign_aggregate(tcx, trcx, &lhs, rvalue);
        }
        mir::Rvalue::ShallowInitBox(op, _ty) => {
            // println!("[Rvalue] ShallowInitBox({:?}, {:?})", op, ty);
            match op {
                mir::Operand::Move(_ptr) => {
                    // The `lhs = ShallowInitBox(ptr, T)` operation is similar to
                    // `lhs = Box::<T>::from_raw(ptr, ..)`. It's sufficient to know
                    // that the reference stored within lhs (lhs.p0.p0.p0)
                    // points to some external (heap) location, which we represent
                    // as lhs.ext.
                    //
                    // Therefore, we omit the ptr argument and interpret this
                    // operation as: lhs.p0.p0.p0 = &mut lhs.ext;
                    trcx.eval(LowRpilInst::Assign {
                        lhs: LowRpilOp::Place {
                            base: Box::new(LowRpilOp::Place {
                                base: Box::new(LowRpilOp::Place {
                                    base: Box::new(lhs.clone()),
                                    place_desc: PlaceDesc::P(0),
                                }),
                                place_desc: PlaceDesc::P(0),
                            }),
                            place_desc: PlaceDesc::P(0),
                        },
                        rhs: LowRpilOp::Ref(Box::new(LowRpilOp::Place {
                            base: Box::new(lhs),
                            place_desc: PlaceDesc::PExt,
                        })),
                    });
                }
                mir::Operand::Copy(..) | mir::Operand::Constant(..) => {
                    unimplemented!();
                }
            }
        }
        mir::Rvalue::Discriminant(..)
        | mir::Rvalue::NullaryOp(..)
        | mir::Rvalue::UnaryOp(..)
        | mir::Rvalue::BinaryOp(..) => {}
        _ => {
            let x = discriminant(rvalue);
            println!("[Rvalue-{:?}] Unknown `{:?}`", x, rvalue);
            unimplemented!();
        }
    }

    trcx
}

fn translate_statement_of_assign_aggregate<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut trcx: TranslationCtxt,
    lhs: &LowRpilOp,
    rvalue: &mir::Rvalue<'tcx>,
) -> TranslationCtxt {
    let (aggregate, values) = match rvalue {
        mir::Rvalue::Aggregate(aggregate, values) => (&**aggregate, values),
        _ => unreachable!(),
    };
    match aggregate {
        mir::AggregateKind::Array(..) | mir::AggregateKind::Tuple => {
            if let mir::AggregateKind::Array(..) = aggregate {
                println!("[Aggregate] Array({:?})", values);
            } else {
                println!("[Aggregate] Tuple({:?})", values);
            }
            for (lidx, value) in values.iter().enumerate() {
                let lhs_place = LowRpilOp::Place {
                    base: Box::new(lhs.clone()),
                    place_desc: PlaceDesc::P(lidx),
                };
                trcx = handle_aggregate(trcx, lhs_place, value);
            }
        }
        mir::AggregateKind::Adt(def_id, variant_idx, _, _, field_idx) => {
            let def_path = tcx.def_path_str(*def_id);
            let adt_def = tcx.type_of(def_id).skip_binder().ty_adt_def().unwrap();
            let is_transparent = adt_def.repr().transparent();
            let is_enum = adt_def.is_enum();
            println!(
                "[Aggregate] Adt(def_path={:?}, variant_idx={:?}, transparent={:?})",
                def_path, variant_idx, is_transparent
            );
            if def_path == "std::pin::Pin" {
                match values.iter().next().unwrap() {
                    mir::Operand::Copy(rhs_place) => {
                        let rhs = LowRpilOp::from_mir_place(rhs_place);
                        trcx.eval(LowRpilInst::Pin(rhs));
                    }
                    mir::Operand::Move(_) | mir::Operand::Constant(_) => unreachable!(),
                }
            }
            if is_transparent {
                let lhs_place = lhs.clone();
                // Ensure that all values except the first are constant (e.g. marker::PhantomData)
                let value = {
                    let mut result = None;
                    for (i, v) in values.iter().enumerate() {
                        if i == 0 {
                            result = Some(v);
                        } else {
                            assert!(v.constant().is_some());
                        }
                    }
                    result.unwrap()
                };
                trcx = handle_aggregate(trcx, lhs_place, value);
            } else {
                for (lidx, value) in values.iter().enumerate() {
                    let base = Box::new(lhs.clone());
                    let lhs_place = match (is_enum, field_idx) {
                        // Enum
                        (true, None) => LowRpilOp::Place {
                            base,
                            place_desc: PlaceDesc::VP(variant_idx.as_usize(), lidx),
                        },
                        // Struct
                        (false, None) => {
                            assert!(adt_def.is_struct());
                            LowRpilOp::Place {
                                base,
                                place_desc: PlaceDesc::P(lidx),
                            }
                        }
                        // Union
                        (false, Some(union_field_idx)) => {
                            assert!(adt_def.is_union());
                            LowRpilOp::Place {
                                base,
                                place_desc: PlaceDesc::P(union_field_idx.as_usize()),
                            }
                        }
                        _ => unreachable!(),
                    };
                    trcx = handle_aggregate(trcx, lhs_place, value);
                }
            }
        }
        mir::AggregateKind::Closure(def_id, _) => {
            println!("[Aggregate] Closure(def_id={})", def_id.index.as_u32());
            let def_id = *def_id;
            debug::log_func_mir(tcx, def_id);
            trcx.eval(LowRpilInst::Assign {
                lhs: lhs.clone(),
                rhs: LowRpilOp::Closure { def_id },
            });
            for (lidx, value) in values.iter().enumerate() {
                let lhs_place = LowRpilOp::Place {
                    base: Box::new(lhs.clone()),
                    place_desc: PlaceDesc::P(lidx),
                };
                trcx = handle_aggregate(trcx, lhs_place, value);
            }
        }
        _ => {
            let x = discriminant(aggregate);
            println!("[Aggregate-{:?}] Unknown `{:?}`", x, aggregate);
            unimplemented!();
        }
    };

    trcx
}

fn handle_aggregate(
    mut trcx: TranslationCtxt,
    lhs: LowRpilOp,
    value: &mir::Operand<'_>,
) -> TranslationCtxt {
    match value {
        mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => {
            let rhs = LowRpilOp::from_mir_place(rplace);
            trcx.eval(LowRpilInst::Assign { lhs, rhs });
        }
        mir::Operand::Constant(_) => {}
    }

    trcx
}

fn is_function_excluded(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let excluded_from_translation: rustc_data_structures::fx::FxHashSet<&str> =
        ["alloc::alloc::exchange_malloc", "core::mem::swap"]
            .iter()
            .cloned()
            .collect();
    let def_path = tcx.def_path_str(def_id);
    excluded_from_translation.contains(def_path.as_str())
}

fn is_function_fn_trait_shim(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
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
