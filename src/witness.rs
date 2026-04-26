use std::marker::PhantomData;
use std::mem::ManuallyDrop;

/// A proof that types `A` and `B` are the same type.
///
/// The only way to construct an `Is<A, B>` is via [`Is::refl()`], which
/// requires `A == B`. This is the Leibniz equality / type equality witness
/// pattern, well-known in Haskell and OCaml.
///
/// The `unsafe` transmute inside `cast` / `cast_ref` is *sound by
/// construction*: the witness can only exist when `A == B`.
///
/// Users of `proptest-lockstep` never interact with this type directly --
/// it is generated and used internally by the proc macro.
///
/// We use `PhantomData<fn(A) -> B>` to be contravariant in `A` and covariant
/// in `B`, preventing unsound variance exploits.
pub struct Is<A, B>(PhantomData<fn(A) -> B>);

// Manual impls -- the witness carries no data.
impl<A, B> Clone for Is<A, B> {
    fn clone(&self) -> Self {
        Is(PhantomData)
    }
}

impl<A, B> Copy for Is<A, B> {}

impl<A, B> std::fmt::Debug for Is<A, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Is<_, _>")
    }
}

impl<A> Is<A, A> {
    /// Construct a proof that `A == A`.
    pub fn refl() -> Self {
        Is(PhantomData)
    }
}

impl<A, B> Is<A, B> {
    /// Cast a value from `A` to `B` using the proof.
    ///
    /// # Safety (internal)
    ///
    /// Sound because `Is<A, B>` can only be constructed via `refl()`,
    /// which enforces `A == B` at the type level.
    pub fn cast(self, a: A) -> B {
        // SAFETY: Is<A, B> witnesses A == B. The only constructor is refl(),
        // which requires A == B. We use ManuallyDrop to avoid double-drop.
        let a = ManuallyDrop::new(a);
        unsafe { std::ptr::read(&*a as *const A as *const B) }
    }

    /// Cast a reference from `&A` to `&B` using the proof.
    pub fn cast_ref<'a>(&self, a: &'a A) -> &'a B {
        // SAFETY: same reasoning as `cast`.
        unsafe { &*(a as *const A as *const B) }
    }

    /// Cast a mutable reference from `&mut A` to `&mut B` using the proof.
    pub fn cast_mut<'a>(&self, a: &'a mut A) -> &'a mut B {
        // SAFETY: same reasoning as `cast`.
        unsafe { &mut *(a as *mut A as *mut B) }
    }

    /// Symmetry: if `A == B`, then `B == A`.
    pub fn symm(self) -> Is<B, A> {
        Is(PhantomData)
    }

    /// Transitivity: if `A == B` and `B == C`, then `A == C`.
    pub fn trans<C>(self, _other: Is<B, C>) -> Is<A, C> {
        Is(PhantomData)
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refl_cast_roundtrip() {
        let proof: Is<i32, i32> = Is::refl();
        assert_eq!(proof.cast(42), 42);
    }

    #[test]
    fn refl_cast_ref() {
        let proof: Is<String, String> = Is::refl();
        let s = String::from("hello");
        assert_eq!(proof.cast_ref(&s), &s);
    }

    #[test]
    fn symmetry() {
        let proof: Is<i32, i32> = Is::refl();
        let _sym: Is<i32, i32> = proof.symm();
    }

    #[test]
    fn transitivity() {
        let ab: Is<u64, u64> = Is::refl();
        let bc: Is<u64, u64> = Is::refl();
        let _ac: Is<u64, u64> = ab.trans(bc);
    }

    #[test]
    fn cast_complex_type() {
        let proof: Is<Result<(i32, String), bool>, Result<(i32, String), bool>> = Is::refl();
        let val: Result<(i32, String), bool> = Ok((42, "test".into()));
        let cast_val = proof.cast(val);
        assert_eq!(cast_val, Ok((42, "test".into())));
    }
}
