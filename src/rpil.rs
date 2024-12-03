use rustc_hir::def_id::DefId;
use rustc_middle::mir;

use std::fmt;
use std::mem::discriminant;

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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PlaceDesc {
    V(usize),
    P(usize),
    PExt,
}

impl fmt::Debug for PlaceDesc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PlaceDesc::*;
        match self {
            V(v) => write!(f, "v{}", v),
            P(p) => write!(f, "p{}", p),
            PExt => write!(f, "ext"),
        }
    }
}

impl LowRpilOp {
    pub fn assume_closure(&self) -> Option<DefId> {
        use LowRpilOp::*;
        match self {
            Closure { def_id } => Some(*def_id),
            Ref(inner_op) => inner_op.assume_closure(),
            _ => None,
        }
    }

    // pub fn depth(&self) -> usize {
    //     use LowRpilOp::*;
    //     match self {
    //         Local { depth, .. } => *depth,
    //         Place { base: op, .. } | Ref(op) | Deref(op) => op.depth(),
    //         Closure { .. } => 0,
    //     }
    // }

    // pub fn origin_var_index(&self) -> Option<usize> {
    //     use LowRpilOp::*;
    //     match self.origin() {
    //         UpLocal { index, .. } => Some(index),
    //         _ => None,
    //     }
    // }

    // fn origin(&self) -> LowRpilOp {
    //     use LowRpilOp::*;
    //     match self {
    //         Local { .. } => unreachable!(),
    //         UpLocal { .. } | Closure { .. } => self.clone(),
    //         Place { base, .. } => base.origin(),
    //         Ref(op) | Deref(op) => op.origin(),
    //     }
    // }

    // pub fn replace_origin(&self, from: &LowRpilOp, to: &LowRpilOp) -> Option<LowRpilOp> {
    //     use LowRpilOp::*;
    //     if self == from {
    //         return Some(to.clone());
    //     }
    //     match self {
    //         Local { .. } | Closure { .. } => None,
    //         Place { base, place_desc } => {
    //             base.replace_origin(from, to).map(|replaced_base| Place {
    //                 base: Box::new(replaced_base),
    //                 place_desc: place_desc.clone(),
    //             })
    //         }
    //         Ref(op) => op
    //             .replace_origin(from, to)
    //             .map(|replaced_op| Ref(Box::new(replaced_op))),
    //         Deref(op) => op
    //             .replace_origin(from, to)
    //             .map(|replaced_op| Ref(Box::new(replaced_op))),
    //     }
    // }
}

impl fmt::Debug for LowRpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilOp::*;
        match self {
            Local { index } => write!(f, "_{}", index),
            UpLocal { depth, index } => write!(f, "{}_{}", depth, index),
            Place { base, place_desc } => write!(f, "{:?}.{:?}", base, place_desc),
            Closure { def_id } => write!(f, "{{closure:{}}}", def_id.index.as_u32()),
            Ref(op) => write!(f, "& {:?}", op),
            Deref(op) => write!(f, "(*{:?})", op),
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

impl fmt::Debug for LowRpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LowRpilInst::*;
        match self {
            Assign { lhs, rhs } => {
                write!(f, "{:?} = {:?};", lhs, rhs)
            }
            CallFunc {
                def_id,
                ret,
                arg_ops,
            } => {
                let (func_crt, func_idx) = (def_id.krate.as_u32(), def_id.index.as_u32());
                write!(f, "{:?} = <{}:{}>{:?};", ret, func_crt, func_idx, arg_ops)
            }
            CallClosure {
                closure,
                ret,
                args_op,
            } => {
                write!(f, "{:?} = Call({:?}, {:?});", ret, closure, args_op)
            }
            Pin(op) => write!(f, "pin {:?};", op),
            Move(op) => write!(f, "move {:?};", op),
            Forget(op) => write!(f, "forget {:?};", op),
            EnterBasicBlock { bb } => write!(f, "enter bb{};", bb.as_usize()),
            LeaveBasicBlock => write!(f, "leave;"),
            Return => write!(f, "return;"),
        }
    }
}

impl LowRpilOp {
    pub fn local_with_depth(op: LowRpilOp, depth: usize) -> LowRpilOp {
        match op {
            LowRpilOp::Local { index } => LowRpilOp::UpLocal { depth, index },
            _ => unreachable!(),
        }
    }

    pub fn from_mir_place<'tcx>(place: &mir::Place<'tcx>) -> Self {
        let projection = project_rpil_place(place, place.projection.len());
        // if place.projection.len() > 0 {
        //     println!("[Projection] {:?}, {:?}", place.local, place.projection);
        //     println!("[Projection Result] {:?}", projection);
        // }
        projection
    }
}

fn project_rpil_place<'tcx>(place: &mir::Place<'tcx>, idx: usize) -> LowRpilOp {
    if idx == 0 {
        return LowRpilOp::Local {
            index: place.local.as_usize(),
        };
    }
    let rplace = &place.projection[idx - 1];
    match rplace {
        mir::ProjectionElem::Field(ridx, _) => LowRpilOp::Place {
            base: Box::new(project_rpil_place(place, idx - 1)),
            place_desc: PlaceDesc::P(ridx.as_usize()),
        },
        mir::ProjectionElem::Downcast(_, variant_idx) => LowRpilOp::Place {
            base: Box::new(project_rpil_place(place, idx - 1)),
            place_desc: PlaceDesc::V(variant_idx.as_usize()),
        },
        mir::ProjectionElem::Deref => {
            LowRpilOp::Deref(Box::new(project_rpil_place(place, idx - 1)))
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RpilOp {
    Local {
        index: usize,
    },
    Place {
        base: Box<RpilOp>,
        place_desc: PlaceDesc,
    },
    Deref(Box<RpilOp>),
}

impl fmt::Debug for RpilOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RpilOp::*;
        match self {
            Local { index } => write!(f, "_{}", index),
            Place { base, place_desc } => write!(f, "{:?}.{:?}", base, place_desc),
            Deref(op) => write!(f, "(*{:?})", op),
        }
    }
}

pub enum RpilInst {
    Bind(RpilOp, RpilOp),
    Borrow(RpilOp, RpilOp),
    Pin(RpilOp),
    Move(RpilOp),
    Forget(RpilOp),
}

impl fmt::Debug for RpilInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RpilInst::*;
        match self {
            Bind(op1, op2) => write!(f, "BIND {:?}, {:?}", op1, op2),
            Borrow(op1, op2) => write!(f, "BORROW {:?}, {:?}", op1, op2),
            Pin(op) => write!(f, "PIN {:?}", op),
            Move(op) => write!(f, "MOVE {:?}", op),
            Forget(op) => write!(f, "FORGET {:?}", op),
        }
    }
}
