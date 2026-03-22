use std::fmt::Debug;
use std::marker::PhantomData;

/// Relates a real type and a model type through a common observable form.
///
/// The bridge algebra replaces Haskell's manual `ModelValue` + `Observable`
/// GADTs with composable combinators. Each bridge describes how to project
/// a real value and a model value into a common `Observed` type that
/// supports equality comparison.
pub trait LockstepBridge {
    /// The type returned by the real system-under-test.
    type Real;
    /// The type returned by the pure model.
    type Model;
    /// The common observable form — must support `Debug + PartialEq`.
    type Observed: Debug + PartialEq;

    /// Project a real value into its observable form.
    fn observe_real(r: &Self::Real) -> Self::Observed;
    /// Project a model value into its observable form.
    fn observe_model(m: &Self::Model) -> Self::Observed;

    /// Compare a real and model value through the bridge.
    /// Returns `Ok(())` if they match, or an error message describing the mismatch.
    fn check(real: &Self::Real, model: &Self::Model) -> Result<(), String> {
        let obs_real = Self::observe_real(real);
        let obs_model = Self::observe_model(model);
        if obs_real == obs_model {
            Ok(())
        } else {
            Err(format!(
                "  Real observed:  {:?}\n  Model observed: {:?}",
                obs_real, obs_model
            ))
        }
    }

    /// Compare two model values through the bridge, using `observe_model`
    /// on both sides. This is the correct comparison for DPOR commutativity
    /// checks, where both values are model results (not a real/model pair).
    ///
    /// For symmetric bridges (where `observe_real == observe_model`), this
    /// gives the same result as `check`. For asymmetric bridges, this avoids
    /// the imprecision of passing two model results to `check` (which would
    /// apply `observe_real` to the first and `observe_model` to the second).
    fn check_model(m1: &Self::Model, m2: &Self::Model) -> Result<(), String> {
        let obs1 = Self::observe_model(m1);
        let obs2 = Self::observe_model(m2);
        if obs1 == obs2 {
            Ok(())
        } else {
            Err(format!(
                "  Model observed 1: {:?}\n  Model observed 2: {:?}",
                obs1, obs2
            ))
        }
    }
}

// ===========================================================================
// Primitive bridges
// ===========================================================================

/// Fully observable: model and real are the same type, compared directly.
///
/// Use for types like `String`, `i32`, `bool`, error enums — anything
/// where the model produces the exact same type as the real system.
pub struct Transparent<T>(PhantomData<T>);

impl<T> LockstepBridge for Transparent<T>
where
    T: Debug + Clone + PartialEq + 'static,
{
    type Real = T;
    type Model = T;
    type Observed = T;

    fn observe_real(r: &T) -> T {
        r.clone()
    }

    fn observe_model(m: &T) -> T {
        m.clone()
    }
}

/// Opaque: real and model types differ, and direct comparison is meaningless.
///
/// Use for handles, cursors, session IDs — anything where the model uses
/// a surrogate type. The observed form is `()`, so the bridge always
/// succeeds. A wrong handle only manifests later when *using* it produces
/// the wrong result.
pub struct Opaque<R, M>(PhantomData<(R, M)>);

impl<R, M> LockstepBridge for Opaque<R, M>
where
    R: 'static,
    M: 'static,
{
    type Real = R;
    type Model = M;
    type Observed = ();

    fn observe_real(_: &R) {}
    fn observe_model(_: &M) {}
}

// ===========================================================================
// Algebraic lifts
// ===========================================================================

/// Bridge for `Result<Ok, Err>` types.
///
/// Composes an ok-bridge and an err-bridge. The observed form is
/// `Result<OkB::Observed, ErrB::Observed>`.
pub struct ResultBridge<OkB, ErrB>(PhantomData<(OkB, ErrB)>);

impl<OkB, ErrB> LockstepBridge for ResultBridge<OkB, ErrB>
where
    OkB: LockstepBridge,
    ErrB: LockstepBridge,
    OkB::Observed: Debug + PartialEq,
    ErrB::Observed: Debug + PartialEq,
{
    type Real = Result<OkB::Real, ErrB::Real>;
    type Model = Result<OkB::Model, ErrB::Model>;
    type Observed = Result<OkB::Observed, ErrB::Observed>;

    fn observe_real(r: &Self::Real) -> Self::Observed {
        match r {
            Ok(v) => Ok(OkB::observe_real(v)),
            Err(e) => Err(ErrB::observe_real(e)),
        }
    }

    fn observe_model(m: &Self::Model) -> Self::Observed {
        match m {
            Ok(v) => Ok(OkB::observe_model(v)),
            Err(e) => Err(ErrB::observe_model(e)),
        }
    }
}

/// Bridge for `(A, B)` tuple types.
///
/// Composes bridges for each element. The observed form is
/// `(AB::Observed, BB::Observed)`.
pub struct TupleBridge<AB, BB>(PhantomData<(AB, BB)>);

impl<AB, BB> LockstepBridge for TupleBridge<AB, BB>
where
    AB: LockstepBridge,
    BB: LockstepBridge,
    AB::Observed: Debug + PartialEq,
    BB::Observed: Debug + PartialEq,
{
    type Real = (AB::Real, BB::Real);
    type Model = (AB::Model, BB::Model);
    type Observed = (AB::Observed, BB::Observed);

    fn observe_real(r: &Self::Real) -> Self::Observed {
        (AB::observe_real(&r.0), BB::observe_real(&r.1))
    }

    fn observe_model(m: &Self::Model) -> Self::Observed {
        (AB::observe_model(&m.0), BB::observe_model(&m.1))
    }
}

/// Bridge for 3-tuples `(A, B, C)`.
pub struct Tuple3Bridge<AB, BB, CB>(PhantomData<(AB, BB, CB)>);

impl<AB, BB, CB> LockstepBridge for Tuple3Bridge<AB, BB, CB>
where
    AB: LockstepBridge,
    BB: LockstepBridge,
    CB: LockstepBridge,
    AB::Observed: Debug + PartialEq,
    BB::Observed: Debug + PartialEq,
    CB::Observed: Debug + PartialEq,
{
    type Real = (AB::Real, BB::Real, CB::Real);
    type Model = (AB::Model, BB::Model, CB::Model);
    type Observed = (AB::Observed, BB::Observed, CB::Observed);

    fn observe_real(r: &Self::Real) -> Self::Observed {
        (
            AB::observe_real(&r.0),
            BB::observe_real(&r.1),
            CB::observe_real(&r.2),
        )
    }

    fn observe_model(m: &Self::Model) -> Self::Observed {
        (
            AB::observe_model(&m.0),
            BB::observe_model(&m.1),
            CB::observe_model(&m.2),
        )
    }
}

/// Bridge for `Option<T>` types.
///
/// Composes an inner bridge. The observed form is `Option<B::Observed>`.
pub struct OptionBridge<B>(PhantomData<B>);

impl<B> LockstepBridge for OptionBridge<B>
where
    B: LockstepBridge,
    B::Observed: Debug + PartialEq,
{
    type Real = Option<B::Real>;
    type Model = Option<B::Model>;
    type Observed = Option<B::Observed>;

    fn observe_real(r: &Self::Real) -> Self::Observed {
        r.as_ref().map(B::observe_real)
    }

    fn observe_model(m: &Self::Model) -> Self::Observed {
        m.as_ref().map(B::observe_model)
    }
}

/// Bridge for `Vec<T>` types.
///
/// Composes an element bridge. The observed form is `Vec<B::Observed>`.
pub struct VecBridge<B>(PhantomData<B>);

impl<B> LockstepBridge for VecBridge<B>
where
    B: LockstepBridge,
    B::Observed: Debug + PartialEq,
{
    type Real = Vec<B::Real>;
    type Model = Vec<B::Model>;
    type Observed = Vec<B::Observed>;

    fn observe_real(r: &Self::Real) -> Self::Observed {
        r.iter().map(B::observe_real).collect()
    }

    fn observe_model(m: &Self::Model) -> Self::Observed {
        m.iter().map(B::observe_model).collect()
    }
}

/// Bridge for the unit type `()`. Always matches.
pub struct UnitBridge;

impl LockstepBridge for UnitBridge {
    type Real = ();
    type Model = ();
    type Observed = ();

    fn observe_real(_: &()) {}
    fn observe_model(_: &()) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transparent_match() {
        assert!(Transparent::<i32>::check(&42, &42).is_ok());
    }

    #[test]
    fn transparent_mismatch() {
        assert!(Transparent::<i32>::check(&42, &99).is_err());
    }

    #[test]
    fn opaque_always_matches() {
        // Different types, different values — still matches.
        assert!(Opaque::<u64, String>::check(&42u64, &"hello".to_string()).is_ok());
    }

    #[test]
    fn result_bridge_ok_match() {
        type B = ResultBridge<Transparent<i32>, Transparent<String>>;
        let real: Result<i32, String> = Ok(42);
        let model: Result<i32, String> = Ok(42);
        assert!(B::check(&real, &model).is_ok());
    }

    #[test]
    fn result_bridge_ok_mismatch() {
        type B = ResultBridge<Transparent<i32>, Transparent<String>>;
        let real: Result<i32, String> = Ok(42);
        let model: Result<i32, String> = Ok(99);
        assert!(B::check(&real, &model).is_err());
    }

    #[test]
    fn result_bridge_variant_mismatch() {
        type B = ResultBridge<Transparent<i32>, Transparent<String>>;
        let real: Result<i32, String> = Ok(42);
        let model: Result<i32, String> = Err("bad".into());
        assert!(B::check(&real, &model).is_err());
    }

    #[test]
    fn tuple_bridge_with_opaque() {
        // Simulates Result<(Handle, Path), Err> where Handle is opaque
        type B = ResultBridge<
            TupleBridge<Opaque<u64, i32>, Transparent<String>>,
            Transparent<bool>,
        >;
        let real: Result<(u64, String), bool> = Ok((999, "foo".into()));
        let model: Result<(i32, String), bool> = Ok((1, "foo".into()));
        // Handles differ but are opaque — should match
        assert!(B::check(&real, &model).is_ok());
    }

    #[test]
    fn tuple_bridge_transparent_mismatch() {
        type B = TupleBridge<Transparent<i32>, Transparent<String>>;
        let real = (1, "a".to_string());
        let model = (1, "b".to_string());
        assert!(B::check(&real, &model).is_err());
    }

    #[test]
    fn option_bridge() {
        type B = OptionBridge<Transparent<i32>>;
        assert!(B::check(&Some(42), &Some(42)).is_ok());
        assert!(B::check(&None, &None).is_ok());
        assert!(B::check(&Some(42), &None).is_err());
    }

    #[test]
    fn vec_bridge() {
        type B = VecBridge<Transparent<i32>>;
        assert!(B::check(&vec![1, 2, 3], &vec![1, 2, 3]).is_ok());
        assert!(B::check(&vec![1, 2], &vec![1, 2, 3]).is_err());
    }
}
