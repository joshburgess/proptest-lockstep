use std::fmt::Debug;
use std::marker::PhantomData;

use crate::env::{TypedEnv, VarKey};
use crate::op::{Op, OpComp};
use crate::phase::SymVar;

/// A generalized variable: a symbolic variable `SymVar<X>` paired with
/// a projection `O: Op<X, Y>` that extracts a value of type `Y` from
/// the stored value of type `X`.
///
/// # Example
///
/// If `Open` returns `Result<(FileHandle, PathBuf), FsErr>`, and you need
/// just the `FileHandle` for a subsequent `Close`:
///
/// ```ignore
/// let open_var: SymVar<Result<(FileHandle, PathBuf), FsErr>> = /* ... */;
/// let handle = GVar::new(open_var, OpOk).then(OpFst);
/// // Type: GVar<Result<(FileHandle, PathBuf), FsErr>, FileHandle, OpComp<OpOk, OpFst, (FileHandle, PathBuf)>>
/// ```
pub struct GVar<X: 'static, Y: 'static, O: Op<X, Y>> {
    pub(crate) var: SymVar<X>,
    pub(crate) op: O,
    _phantom: PhantomData<fn() -> Y>,
}

impl<X: 'static, Y: 'static, O: Op<X, Y>> GVar<X, Y, O> {
    pub fn new(var: SymVar<X>, op: O) -> Self {
        GVar {
            var,
            op,
            _phantom: PhantomData,
        }
    }

    /// Chain another projection: if this `GVar` projects `X → Y`, and
    /// `next: P` projects `Y → Z`, the result projects `X → Z`.
    pub fn then<Z: 'static, P: Op<Y, Z>>(self, next: P) -> GVar<X, Z, OpComp<O, P, Y>>
    where
        Y: Send + Sync,
    {
        GVar::new(self.var, OpComp::new(self.op, next))
    }

    /// The raw symbolic variable ID.
    pub fn var_id(&self) -> usize {
        self.var.id
    }
}

impl<X: 'static, Y: 'static, O: Op<X, Y>> Clone for GVar<X, Y, O> {
    fn clone(&self) -> Self {
        GVar {
            var: self.var,
            op: self.op.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<X: 'static, Y: 'static, O: Op<X, Y>> Debug for GVar<X, Y, O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GVar")
            .field("var", &self.var)
            .field("op", &self.op)
            .finish()
    }
}

/// Resolve a `GVar` against a `TypedEnv`, applying the projection chain.
///
/// Returns `None` if:
/// - The variable is not present in the environment.
/// - The projection fails (e.g., `OpOk` on an `Err` value).
pub fn resolve_gvar<X: Clone + 'static, Y: 'static, O: Op<X, Y>>(
    gvar: &GVar<X, Y, O>,
    env: &TypedEnv,
) -> Option<Y> {
    let key = VarKey::<X>::new(gvar.var.id);
    let x = env.get(key)?;
    gvar.op.apply(x)
}

/// Resolve a `GVar` against a model environment where the stored type
/// differs from the GVar's `X` (the real return type).
///
/// This is the model-side counterpart of `resolve_gvar`. When actions use
/// opaque handles, the model environment stores `ModelReturn` while the
/// `GVar` is parameterized by `RealReturn`. This function lets you look
/// up the model value using the model type `M`, and apply a model-side
/// projection `P` to extract the needed value.
///
/// # Example
///
/// ```ignore
/// // GVar is typed as GVar<OpenReal, FileHandle, HandleProj>
/// // Model env stores OpenModel = Result<(MockHandle, String), FsErr>
/// // We want MockHandle from the model env:
/// let mock_handle = resolve_model_gvar::<OpenModel, MockHandle, _>(
///     a.handle.var_id(),
///     &OpComp::new(OpOk, OpFst),
///     env,
/// );
/// ```
pub fn resolve_model_gvar<M: Clone + 'static, Y: 'static, P: Op<M, Y>>(
    var_id: usize,
    model_op: &P,
    env: &TypedEnv,
) -> Option<Y> {
    let key = VarKey::<M>::new(var_id);
    let m = env.get(key)?;
    model_op.apply(m)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{OpFst, OpId, OpOk, OpSnd};

    #[test]
    fn identity_projection() {
        let mut env = TypedEnv::new();
        env.insert(0, 42i32);
        let var = SymVar::<i32>::new(0);
        let gvar = GVar::new(var, OpId);
        assert_eq!(resolve_gvar(&gvar, &env), Some(42));
    }

    #[test]
    fn ok_fst_projection() {
        let mut env = TypedEnv::new();
        let val: Result<(i32, String), bool> = Ok((42, "hello".into()));
        env.insert(0, val);

        let var = SymVar::<Result<(i32, String), bool>>::new(0);
        let gvar = GVar::new(var, OpOk).then(OpFst);
        assert_eq!(resolve_gvar(&gvar, &env), Some(42));
    }

    #[test]
    fn ok_snd_projection() {
        let mut env = TypedEnv::new();
        let val: Result<(i32, String), bool> = Ok((42, "hello".into()));
        env.insert(0, val);

        let var = SymVar::<Result<(i32, String), bool>>::new(0);
        let gvar = GVar::new(var, OpOk).then(OpSnd);
        assert_eq!(resolve_gvar(&gvar, &env), Some("hello".to_string()));
    }

    #[test]
    fn projection_fails_on_err() {
        let mut env = TypedEnv::new();
        let val: Result<(i32, String), bool> = Err(false);
        env.insert(0, val);

        let var = SymVar::<Result<(i32, String), bool>>::new(0);
        let gvar = GVar::new(var, OpOk).then(OpFst);
        assert_eq!(resolve_gvar(&gvar, &env), None);
    }

    #[test]
    fn missing_variable() {
        let env = TypedEnv::new();
        let var = SymVar::<i32>::new(99);
        let gvar = GVar::new(var, OpId);
        assert_eq!(resolve_gvar(&gvar, &env), None);
    }

    // -- resolve_model_gvar tests --

    #[test]
    fn model_gvar_resolves_different_type() {
        // Simulates: real env stores Result<(u64, String), bool>,
        // model env stores Result<(i32, String), bool> at same var ID
        let mut env = TypedEnv::new();
        let model_val: Result<(i32, String), bool> = Ok((7, "path".into()));
        env.insert(0, model_val);

        let proj = OpComp::new(OpOk, OpFst);
        assert_eq!(
            resolve_model_gvar::<Result<(i32, String), bool>, i32, _>(0, &proj, &env),
            Some(7)
        );
    }

    #[test]
    fn model_gvar_missing_variable() {
        let env = TypedEnv::new();
        assert_eq!(
            resolve_model_gvar::<i32, i32, _>(99, &OpId, &env),
            None
        );
    }

    #[test]
    fn model_gvar_projection_fails() {
        let mut env = TypedEnv::new();
        let val: Result<(i32, String), bool> = Err(false);
        env.insert(0, val);

        let proj = OpComp::new(OpOk, OpFst);
        assert_eq!(
            resolve_model_gvar::<Result<(i32, String), bool>, i32, _>(0, &proj, &env),
            None
        );
    }
}
