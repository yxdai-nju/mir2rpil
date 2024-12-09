use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;
use std::mem::discriminant;

use super::serialmap::UnaryRecursive;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LowRpilOp {
    Local {
        index: usize,
    },
    UpLocal {
        depth: usize,
        index: usize,
    },
    Place {
        base: Box<LowRpilOp>,
        place_desc: PlaceDesc,
    },
    Closure {
        def_id: DefId,
    },
    Ref(Box<LowRpilOp>),
    Deref(Box<LowRpilOp>),
}

impl UnaryRecursive for LowRpilOp {
    fn get_inner(&self) -> Option<&Self> {
        match self {
            LowRpilOp::Local { .. } | LowRpilOp::UpLocal { .. } | LowRpilOp::Closure { .. } => None,
            LowRpilOp::Place { base: op, .. } | LowRpilOp::Ref(op) | LowRpilOp::Deref(op) => {
                Some(op)
            }
        }
    }

    fn replace_inner(&self, op: Self) -> Self {
        match self {
            LowRpilOp::Local { .. } | LowRpilOp::UpLocal { .. } | LowRpilOp::Closure { .. } => {
                unreachable!()
            }
            LowRpilOp::Place { place_desc, .. } => LowRpilOp::Place {
                base: Box::new(op),
                place_desc: place_desc.clone(),
            },
            LowRpilOp::Ref(_) => LowRpilOp::Ref(Box::new(op)),
            LowRpilOp::Deref(_) => LowRpilOp::Deref(Box::new(op)),
        }
    }
}

pub enum LowRpilInst {
    Assign {
        lhs: LowRpilOp,
        rhs: LowRpilOp,
    },
    CallFunc {
        def_id: DefId,
        ret: LowRpilOp,
        arg_ops: Vec<LowRpilOp>,
    },
    CallClosure {
        closure: LowRpilOp,
        ret: LowRpilOp,
        args_op: LowRpilOp,
    },
    Pin(LowRpilOp),
    Move(LowRpilOp),
    Forget(LowRpilOp),
    EnterBasicBlock {
        bb: mir::BasicBlock,
    },
    LeaveBasicBlock,
    Return,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RpilOp {
    Local {
        index: usize,
    },
    Place {
        base: Box<RpilOp>,
        place_desc: PlaceDesc,
    },
    Ref(Box<RpilOp>),
    Deref(Box<RpilOp>),
}

pub enum RpilInst {
    Bind(RpilOp, RpilOp),
    Borrow(RpilOp, RpilOp),
    Pin(RpilOp),
    Move(RpilOp),
    Forget(RpilOp),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PlaceDesc {
    VP(usize, usize),
    P(usize),
    PExt,
}

#[derive(Debug, Clone)]
pub enum StatusChange {
    Pin,
    Move,
    Forget,
}

impl LowRpilOp {
    pub fn from_mir_place(place: &mir::Place<'_>) -> Self {
        project_rpil_place(place, place.projection.len(), None)
    }

    pub fn with_depth(op: LowRpilOp, depth: usize) -> LowRpilOp {
        match op {
            LowRpilOp::UpLocal { .. } => unreachable!(),
            LowRpilOp::Local { index } => LowRpilOp::UpLocal { depth, index },
            LowRpilOp::Closure { .. } => op.clone(),
            LowRpilOp::Place { base, place_desc } => LowRpilOp::Place {
                base: Box::new(LowRpilOp::with_depth(*base, depth)),
                place_desc: place_desc.clone(),
            },
            LowRpilOp::Ref(inner_op) => {
                LowRpilOp::Ref(Box::new(LowRpilOp::with_depth(*inner_op, depth)))
            }
            LowRpilOp::Deref(inner_op) => {
                LowRpilOp::Deref(Box::new(LowRpilOp::with_depth(*inner_op, depth)))
            }
        }
    }

    pub fn local_with_depth(op: LowRpilOp, depth: usize) -> LowRpilOp {
        match op {
            LowRpilOp::Local { index } => LowRpilOp::UpLocal { depth, index },
            _ => unreachable!(),
        }
    }

    pub fn assume_closure(&self) -> Option<DefId> {
        match self {
            LowRpilOp::Closure { def_id } => Some(*def_id),
            LowRpilOp::Ref(inner_op) => inner_op.assume_closure(),
            _ => None,
        }
    }

    pub fn depth(&self) -> usize {
        match self {
            LowRpilOp::Local { .. } => unreachable!(),
            LowRpilOp::UpLocal { depth, .. } => *depth,
            LowRpilOp::Place { base: op, .. } | LowRpilOp::Ref(op) | LowRpilOp::Deref(op) => {
                op.depth()
            }
            LowRpilOp::Closure { .. } => 0,
        }
    }

    pub fn origin_index(&self) -> Option<usize> {
        match self {
            LowRpilOp::Local { .. } | LowRpilOp::Closure { .. } => None,
            LowRpilOp::UpLocal { index, .. } => Some(*index),
            LowRpilOp::Place { base, .. } => base.origin_index(),
            LowRpilOp::Ref(op) | LowRpilOp::Deref(op) => op.origin_index(),
        }
    }
}

fn project_rpil_place(
    place: &mir::Place<'_>,
    idx: usize,
    pending_place_idx: Option<usize>,
) -> LowRpilOp {
    if idx == 0 {
        let inner_projection_result = LowRpilOp::Local {
            index: place.local.as_usize(),
        };
        return if let Some(place_idx) = pending_place_idx {
            LowRpilOp::Place {
                base: Box::new(inner_projection_result),
                place_desc: PlaceDesc::P(place_idx),
            }
        } else {
            inner_projection_result
        };
    }
    let rplace = &place.projection[idx - 1];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) => {
            let new_place_idx = ridx.as_usize();
            let inner_projection_result = project_rpil_place(place, idx - 1, Some(new_place_idx));
            resolve_pending_field_cast(inner_projection_result, pending_place_idx, |p| {
                PlaceDesc::P(p)
            })
        }
        mir::ProjectionElem::Downcast(_, variant_idx) => {
            let inner_projection_result = project_rpil_place(place, idx - 1, None);
            resolve_pending_field_cast(inner_projection_result, pending_place_idx, |p| {
                PlaceDesc::VP(variant_idx.as_usize(), p)
            })
        }
        mir::ProjectionElem::Deref => {
            let inner_projection_result = project_rpil_place(place, idx - 1, None);
            LowRpilOp::Deref(Box::new(resolve_pending_field_cast(
                inner_projection_result,
                pending_place_idx,
                |p| PlaceDesc::P(p),
            )))
        }
        _ => {
            println!(
                "[ProjectionElem-{:?}] Unknown `{:?}`",
                discriminant(rplace),
                rplace
            );
            unimplemented!()
        }
    }
}

fn resolve_pending_field_cast(
    inner_projection_result: LowRpilOp,
    pending_place_idx: Option<usize>,
    mut f: impl FnMut(usize) -> PlaceDesc,
) -> LowRpilOp {
    if let Some(place_idx) = pending_place_idx {
        LowRpilOp::Place {
            base: Box::new(inner_projection_result),
            place_desc: f(place_idx),
        }
    } else {
        inner_projection_result
    }
}

impl RpilOp {
    pub fn from_low_rpil(op: LowRpilOp) -> RpilOp {
        match op {
            LowRpilOp::Local { .. } | LowRpilOp::Closure { .. } => {
                unreachable!()
            }
            LowRpilOp::UpLocal { index, .. } => RpilOp::Local { index },
            LowRpilOp::Place { base, place_desc } => RpilOp::Place {
                base: Box::new(RpilOp::from_low_rpil(*base)),
                place_desc: place_desc.clone(),
            },
            LowRpilOp::Ref(inner_op) => RpilOp::Ref(Box::new(RpilOp::from_low_rpil(*inner_op))),
            LowRpilOp::Deref(inner_op) => RpilOp::Deref(Box::new(RpilOp::from_low_rpil(*inner_op))),
        }
    }
}

impl RpilInst {
    pub fn from_low_rpil_assignment(low_lhs: LowRpilOp, low_rhs: LowRpilOp) -> RpilInst {
        let lhs = RpilOp::from_low_rpil(low_lhs);
        let rhs = RpilOp::from_low_rpil(low_rhs);
        match rhs {
            RpilOp::Ref(inner_op) => RpilInst::Borrow(lhs, *inner_op),
            _ => RpilInst::Bind(lhs, rhs),
        }
    }

    pub fn from_low_rpil_status_change(low_op: LowRpilOp, status_change: StatusChange) -> RpilInst {
        let op = RpilOp::from_low_rpil(low_op);
        match status_change {
            StatusChange::Pin => RpilInst::Pin(op),
            StatusChange::Move => RpilInst::Move(op),
            StatusChange::Forget => RpilInst::Forget(op),
        }
    }
}

impl fmt::Debug for LowRpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowRpilOp::Local { index } => write!(f, "_{}", index),
            LowRpilOp::UpLocal { depth, index } => write!(f, "{}_{}", depth, index),
            LowRpilOp::Place { base, place_desc } => write!(f, "{:?}.{:?}", base, place_desc),
            LowRpilOp::Closure { def_id } => {
                let (func_crt, func_idx) = (def_id.krate.as_u32(), def_id.index.as_u32());
                write!(f, "<{}:{}>", func_crt, func_idx)
            }
            LowRpilOp::Ref(op) => write!(f, "& {:?}", op),
            LowRpilOp::Deref(op) => write!(f, "(*{:?})", op),
        }
    }
}

impl fmt::Debug for LowRpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowRpilInst::Assign { lhs, rhs } => {
                write!(f, "{:?} = {:?};", lhs, rhs)
            }
            LowRpilInst::CallFunc {
                def_id,
                ret,
                arg_ops,
            } => {
                let (func_crt, func_idx) = (def_id.krate.as_u32(), def_id.index.as_u32());
                write!(f, "{:?} = <{}:{}>{:?};", ret, func_crt, func_idx, arg_ops)
            }
            LowRpilInst::CallClosure {
                closure,
                ret,
                args_op,
            } => {
                write!(f, "{:?} = Call({:?}, {:?});", ret, closure, args_op)
            }
            LowRpilInst::Pin(op) => write!(f, "pin {:?};", op),
            LowRpilInst::Move(op) => write!(f, "move {:?};", op),
            LowRpilInst::Forget(op) => write!(f, "forget {:?};", op),
            LowRpilInst::EnterBasicBlock { bb } => write!(f, "enter bb{};", bb.as_usize()),
            LowRpilInst::LeaveBasicBlock => write!(f, "leave;"),
            LowRpilInst::Return => write!(f, "return;"),
        }
    }
}

impl fmt::Debug for PlaceDesc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PlaceDesc::VP(v, p) => write!(f, "v{}p{}", v, p),
            PlaceDesc::P(p) => write!(f, "p{}", p),
            PlaceDesc::PExt => write!(f, "ext"),
        }
    }
}

impl fmt::Debug for RpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RpilOp::Local { index } => write!(f, "_{}", index),
            RpilOp::Place { base, place_desc } => write!(f, "{:?}.{:?}", base, place_desc),
            RpilOp::Ref(op) => write!(f, "& {:?}", op),
            RpilOp::Deref(op) => write!(f, "(*{:?})", op),
        }
    }
}

impl fmt::Debug for RpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RpilInst::Bind(op1, op2) => write!(f, "BIND {:?}, {:?}", op1, op2),
            RpilInst::Borrow(op1, op2) => write!(f, "BORROW {:?}, {:?}", op1, op2),
            RpilInst::Pin(op) => write!(f, "PIN {:?}", op),
            RpilInst::Move(op) => write!(f, "MOVE {:?}", op),
            RpilInst::Forget(op) => write!(f, "FORGET {:?}", op),
        }
    }
}
