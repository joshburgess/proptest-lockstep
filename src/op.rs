use std::fmt::Debug;
use std::marker::PhantomData;


/// A projection from type `A` to type `B`.
///
/// This is a small DSL for decomposing compound return types. Each
/// implementor is a zero-sized type -- the entire projection chain compiles
/// down to nothing at runtime.
///
/// Returns `Option<B>` because the projection may fail at runtime (e.g.,
/// `OpOk` on an `Err` value). This is handled gracefully during variable
/// resolution.
pub trait Op<A, B>: Debug + Clone + Send + Sync + 'static {
    fn apply(&self, a: &A) -> Option<B>;
}

// ---------------------------------------------------------------------------
// Identity
// ---------------------------------------------------------------------------

/// Identity projection: `A → A`.
#[derive(Debug, Clone, Copy)]
pub struct OpId;

impl<A: Clone> Op<A, A> for OpId {
    fn apply(&self, a: &A) -> Option<A> {
        Some(a.clone())
    }
}

// ---------------------------------------------------------------------------
// Tuple projections
// ---------------------------------------------------------------------------

/// First element of a tuple: `(A, B) → A`.
#[derive(Debug, Clone, Copy)]
pub struct OpFst;

impl<A: Clone, B> Op<(A, B), A> for OpFst {
    fn apply(&self, a: &(A, B)) -> Option<A> {
        Some(a.0.clone())
    }
}

/// Second element of a tuple: `(A, B) → B`.
#[derive(Debug, Clone, Copy)]
pub struct OpSnd;

impl<A, B: Clone> Op<(A, B), B> for OpSnd {
    fn apply(&self, a: &(A, B)) -> Option<B> {
        Some(a.1.clone())
    }
}

// ---------------------------------------------------------------------------
// Result projections
// ---------------------------------------------------------------------------

/// Ok projection: `Result<T, E> → T`. Returns `None` on `Err`.
#[derive(Debug, Clone, Copy)]
pub struct OpOk;

impl<T: Clone, E> Op<Result<T, E>, T> for OpOk {
    fn apply(&self, a: &Result<T, E>) -> Option<T> {
        a.as_ref().ok().cloned()
    }
}

/// Err projection: `Result<T, E> → E`. Returns `None` on `Ok`.
#[derive(Debug, Clone, Copy)]
pub struct OpErr;

impl<T, E: Clone> Op<Result<T, E>, E> for OpErr {
    fn apply(&self, a: &Result<T, E>) -> Option<E> {
        a.as_ref().err().cloned()
    }
}

// ---------------------------------------------------------------------------
// Option projection
// ---------------------------------------------------------------------------

/// Some projection: `Option<T> → T`. Returns `None` on `None`.
#[derive(Debug, Clone, Copy)]
pub struct OpSome;

impl<T: Clone> Op<Option<T>, T> for OpSome {
    fn apply(&self, a: &Option<T>) -> Option<T> {
        a.clone()
    }
}

// ---------------------------------------------------------------------------
// Composition
// ---------------------------------------------------------------------------

/// Composition of two projections: first apply `F`, then apply `G`.
///
/// `OpComp<OpOk, OpFst, (A, B)>` on `Result<(A, B), E>` yields `A`:
/// first extract the `Ok` value `(A, B)`, then extract the first element `A`.
pub struct OpComp<F, G, B> {
    pub(crate) first: F,
    pub(crate) second: G,
    _phantom: PhantomData<fn() -> B>,
}

impl<F: Clone, G: Clone, B> Clone for OpComp<F, G, B> {
    fn clone(&self) -> Self {
        OpComp {
            first: self.first.clone(),
            second: self.second.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<F: Copy, G: Copy, B> Copy for OpComp<F, G, B> {}

impl<F: Debug, G: Debug, B> Debug for OpComp<F, G, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OpComp")
            .field("first", &self.first)
            .field("second", &self.second)
            .finish()
    }
}

impl<F, G, B> OpComp<F, G, B> {
    pub fn new(first: F, second: G) -> Self {
        OpComp {
            first,
            second,
            _phantom: PhantomData,
        }
    }
}

impl<A, B, C, F, G> Op<A, C> for OpComp<F, G, B>
where
    F: Op<A, B>,
    G: Op<B, C>,
    B: Send + Sync + 'static,
{
    fn apply(&self, a: &A) -> Option<C> {
        let b = self.first.apply(a)?;
        self.second.apply(&b)
    }
}

// ---------------------------------------------------------------------------
// Index projection
// ---------------------------------------------------------------------------

/// Index projection: `Vec<T> → T`. Returns `None` if index is out of bounds.
#[derive(Debug, Clone, Copy)]
pub struct OpIndex {
    pub index: usize,
}

impl<T: Clone> Op<Vec<T>, T> for OpIndex {
    fn apply(&self, a: &Vec<T>) -> Option<T> {
        a.get(self.index).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_id() {
        assert_eq!(OpId.apply(&42), Some(42));
    }

    #[test]
    fn op_fst_snd() {
        let t = (1, "hello");
        assert_eq!(OpFst.apply(&t), Some(1));
        assert_eq!(OpSnd.apply(&t), Some("hello"));
    }

    #[test]
    fn op_ok_err() {
        let ok: Result<i32, String> = Ok(42);
        let err: Result<i32, String> = Err("bad".into());
        assert_eq!(OpOk.apply(&ok), Some(42));
        assert_eq!(OpOk.apply(&err), None);
        assert_eq!(OpErr.apply(&err), Some("bad".to_string()));
        assert_eq!(OpErr.apply(&ok), None);
    }

    #[test]
    fn op_comp_ok_fst() {
        let val: Result<(i32, String), bool> = Ok((42, "hi".into()));
        let proj: OpComp<OpOk, OpFst, (i32, String)> = OpComp::new(OpOk, OpFst);
        assert_eq!(proj.apply(&val), Some(42));
    }

    #[test]
    fn op_comp_chain() {
        let val: Result<(i32, String), bool> = Ok((42, "hi".into()));
        let proj: OpComp<OpOk, OpSnd, (i32, String)> = OpComp::new(OpOk, OpSnd);
        assert_eq!(proj.apply(&val), Some("hi".to_string()));
    }

    #[test]
    fn op_comp_fails_on_err() {
        let val: Result<(i32, String), bool> = Err(false);
        let proj: OpComp<OpOk, OpFst, (i32, String)> = OpComp::new(OpOk, OpFst);
        assert_eq!(proj.apply(&val), None);
    }

    #[test]
    fn op_index() {
        let v = vec![10, 20, 30];
        assert_eq!(OpIndex { index: 1 }.apply(&v), Some(20));
        assert_eq!(OpIndex { index: 5 }.apply(&v), None);
    }

    #[test]
    fn op_some() {
        assert_eq!(OpSome.apply(&Some(42)), Some(42));
        assert_eq!(OpSome.apply(&None::<i32>), None);
    }
}
