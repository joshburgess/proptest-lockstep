use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;

/// Phase distinction via GATs.
///
/// During generation, everything is `Symbolic` — variables are opaque tokens.
/// During execution, everything is `Concrete` — variables hold real values.
/// The compiler enforces the boundary: no real values leak into generation,
/// no symbolic tokens survive into execution.
pub trait Phase: Clone + Debug + 'static {
    type Var<T: 'static>;
}

// ---------------------------------------------------------------------------
// Symbolic phase
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Symbolic;

/// An opaque token representing a value of type `T` that will be produced
/// at runtime. During generation, we only know the *identity* of the variable,
/// not its value.
pub struct SymVar<T: 'static> {
    pub(crate) id: usize,
    _phantom: PhantomData<T>,
}

impl<T: 'static> Clone for SymVar<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: 'static> std::fmt::Debug for SymVar<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymVar").field("id", &self.id).finish()
    }
}

impl<T: 'static> SymVar<T> {
    pub fn new(id: usize) -> Self {
        SymVar {
            id,
            _phantom: PhantomData,
        }
    }

    pub fn id(&self) -> usize {
        self.id
    }
}

impl<T: 'static> PartialEq for SymVar<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T: 'static> Eq for SymVar<T> {}

impl<T: 'static> Hash for SymVar<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<T: 'static> Copy for SymVar<T> {}

impl Phase for Symbolic {
    type Var<T: 'static> = SymVar<T>;
}

// ---------------------------------------------------------------------------
// Concrete phase
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Concrete;

/// A wrapper holding a real value of type `T`, used during test execution.
pub struct ConVar<T: 'static>(pub T);

impl<T: 'static> Clone for ConVar<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        ConVar(self.0.clone())
    }
}

impl<T: 'static> std::fmt::Debug for ConVar<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ConVar").field(&self.0).finish()
    }
}

impl Phase for Concrete {
    type Var<T: 'static> = ConVar<T>;
}
