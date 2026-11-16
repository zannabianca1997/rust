//! Structural check for the `Move` trait.
//!
//! A type is movable unless it contains `PhantomUnmovable` inline.
//!
//! This module walks the type, stopping at the first indirection, as moving a pointer does not move
//! the pointed type.

use crate::inherent::*;
use crate::lang_items::SolverAdtLangItem;
use crate::{self as ty, Interner, Unnormalized};

/// Outcome of the walk
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MoveCheck {
    /// Freely movable
    Movable,
    /// Unmovable
    ///
    /// the type contains `PhantomUnmovable`
    Unmovable,
    /// Can't decide now, cause generics
    Unknown,
}

pub fn check_structural_move<I: Interner>(cx: I, move_trait: I::TraitId, ty: I::Ty) -> MoveCheck {
    match ty.kind() {
        ty::Uint(_)
        | ty::Int(_)
        | ty::Bool
        | ty::Float(_)
        | ty::Char
        | ty::Str
        | ty::Never
        | ty::FnDef(..)
        | ty::FnPtr(..)
        | ty::Error(_)
        | ty::Infer(ty::IntVar(_) | ty::FloatVar(_))
        | ty::Foreign(..)
        | ty::UnsafeBinder(_)
        | ty::Dynamic(..)
        // Pointers
        | ty::RawPtr(..)
        | ty::Ref(..)
        | ty::Pat(..)
        | ty::Slice(..) => MoveCheck::Movable,

        // Whether these contain `PhantomUnmovable` cannot be decided yet...
        ty::Param(..)
        | ty::Placeholder(..)
        | ty::Bound(..)
        | ty::Alias(..)
        | ty::Infer(_) => MoveCheck::Unknown,

        ty::Array(elem_ty, _) => check_structural_move(cx, move_trait, elem_ty),

        ty::Tuple(tys) => tys
            .iter()
            .map(|ty| check_structural_move(cx, move_trait, ty))
            .fold(MoveCheck::Movable, combine),

        ty::Closure(_, args) | ty::CoroutineClosure(_, args) => {
            check_structural_move(cx, move_trait, args.as_closure().tupled_upvars_ty())
        }

        // FIXME: maybe we can recurse here...?
        ty::Coroutine(..) | ty::CoroutineWitness(..) => MoveCheck::Unknown,

        ty::Adt(def, args) => {
            if cx.as_adt_lang_item(def.def_id()) == Some(SolverAdtLangItem::PhantomUnmovable) {
                return MoveCheck::Unmovable;
            }
            // `PhantomData<T>` and owned boxes
            if def.is_phantom_data()
                || cx.as_adt_lang_item(def.def_id()) == Some(SolverAdtLangItem::OwnedBox)
            {
                return MoveCheck::Movable;
            }
            // Explicit `Move`/`!Move` impls exist for this type, take precedence
            let trait_ref = ty::TraitRef::new(
                cx,
                move_trait,
                [<I::Ty as Into<<I as Interner>::GenericArg>>::into(ty)],
            );
            let mut has_impl = false;
            cx.for_each_relevant_impl(trait_ref, |_| has_impl = true);
            if has_impl {
                return MoveCheck::Unknown;
            }
            def.all_field_tys(cx)
                .iter_instantiated(cx, args)
                .map(|ty| check_structural_move(cx, move_trait, Unnormalized::skip_norm_wip(ty)))
                .fold(MoveCheck::Movable, combine)
        }
    }
}

/// ternary logic
fn combine(a: MoveCheck, b: MoveCheck) -> MoveCheck {
    match (a, b) {
        (MoveCheck::Unmovable, _) | (_, MoveCheck::Unmovable) => MoveCheck::Unmovable,
        (MoveCheck::Unknown, _) | (_, MoveCheck::Unknown) => MoveCheck::Unknown,
        (MoveCheck::Movable, MoveCheck::Movable) => MoveCheck::Movable,
    }
}
