use std::any::{Any, TypeId};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::marker::PhantomData;

/// A typed key into a [`TypedEnv`].
pub struct VarKey<T: 'static> {
    pub(crate) id: usize,
    _phantom: PhantomData<T>,
}

impl<T: 'static> VarKey<T> {
    pub fn new(id: usize) -> Self {
        VarKey {
            id,
            _phantom: PhantomData,
        }
    }

    pub fn id(&self) -> usize {
        self.id
    }
}

impl<T: 'static> Clone for VarKey<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: 'static> Copy for VarKey<T> {}

impl<T: 'static> Debug for VarKey<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VarKey")
            .field("id", &self.id)
            .field("type", &std::any::type_name::<T>())
            .finish()
    }
}

impl<T: 'static> PartialEq for VarKey<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T: 'static> Eq for VarKey<T> {}

impl<T: 'static> std::hash::Hash for VarKey<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

// ---------------------------------------------------------------------------
// Boxed, cloneable Any
// ---------------------------------------------------------------------------

/// Wrapper around a type-erased cloneable value.
///
/// Uses `Box<dyn Any + Send>` so that `TypedEnv` is `Send`, which is
/// required for concurrent lockstep testing (sharing the env across
/// Shuttle threads via `Arc<Mutex<TypedEnv>>`).
struct Entry {
    value: Box<dyn Any + Send>,
    clone_fn: fn(&(dyn Any + Send)) -> Box<dyn Any + Send>,
}

impl Entry {
    fn new<T: Clone + Send + 'static>(value: T) -> Self {
        Entry {
            value: Box::new(value),
            clone_fn: |any| {
                let val = any.downcast_ref::<T>().expect("Entry type mismatch in clone_fn");
                Box::new(val.clone())
            },
        }
    }

    fn clone_entry(&self) -> Self {
        Entry {
            value: (self.clone_fn)(&*self.value),
            clone_fn: self.clone_fn,
        }
    }

    fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        self.value.downcast_ref::<T>()
    }
}

// ---------------------------------------------------------------------------
// TypedEnv
// ---------------------------------------------------------------------------

/// A heterogeneous variable environment.
///
/// Stores values of different types keyed by `(id, TypeId)`. This is the
/// only runtime downcast in the system -- it's inside the library boundary,
/// invisible to users.
pub struct TypedEnv {
    inner: HashMap<(usize, TypeId), Entry>,
    ids: HashSet<usize>,
    next_id: usize,
}

impl Clone for TypedEnv {
    fn clone(&self) -> Self {
        TypedEnv {
            inner: self
                .inner
                .iter()
                .map(|(k, v)| (*k, v.clone_entry()))
                .collect(),
            ids: self.ids.clone(),
            next_id: self.next_id,
        }
    }
}

impl Debug for TypedEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypedEnv")
            .field("next_id", &self.next_id)
            .field("len", &self.inner.len())
            .finish()
    }
}

impl TypedEnv {
    pub fn new() -> Self {
        TypedEnv {
            inner: HashMap::new(),
            ids: HashSet::new(),
            next_id: 0,
        }
    }

    /// Allocate a new variable with the given value, returning its key.
    ///
    /// The `Send` bound is required so that `TypedEnv` is `Send`, which
    /// enables concurrent lockstep testing via Shuttle. Most practical
    /// return types (`Result`, `Option<String>`, numeric types, etc.) are
    /// `Send`. Types like `Rc<T>` are not -- use `Arc<T>` instead.
    pub fn alloc<T: Clone + Send + 'static>(&mut self, value: T) -> VarKey<T> {
        let id = self.next_id;
        self.next_id += 1;
        let key = (id, TypeId::of::<T>());
        self.inner.insert(key, Entry::new(value));
        self.ids.insert(id);
        VarKey::new(id)
    }

    /// Insert a value at a specific ID. Used when the ID is determined
    /// externally (e.g., from the symbolic variable's ID).
    pub fn insert<T: Clone + Send + 'static>(&mut self, id: usize, value: T) {
        let key = (id, TypeId::of::<T>());
        self.inner.insert(key, Entry::new(value));
        self.ids.insert(id);
        if id >= self.next_id {
            self.next_id = id + 1;
        }
    }

    /// Retrieve a reference to the value for the given key.
    pub fn get<T: 'static>(&self, key: VarKey<T>) -> Option<&T> {
        let map_key = (key.id, TypeId::of::<T>());
        self.inner.get(&map_key)?.downcast_ref::<T>()
    }

    /// Check whether a variable with the given key exists.
    pub fn contains<T: 'static>(&self, key: VarKey<T>) -> bool {
        let map_key = (key.id, TypeId::of::<T>());
        self.inner.contains_key(&map_key)
    }

    /// Check whether a variable with the given raw ID exists (type-erased).
    pub fn contains_raw(&self, id: usize) -> bool {
        self.ids.contains(&id)
    }

    pub fn next_id(&self) -> usize {
        self.next_id
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl Default for TypedEnv {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_get() {
        let mut env = TypedEnv::new();
        let k = env.alloc(42i32);
        assert_eq!(env.get(k), Some(&42));
    }

    #[test]
    fn insert_and_get() {
        let mut env = TypedEnv::new();
        env.insert(5, "hello".to_string());
        let k: VarKey<String> = VarKey::new(5);
        assert_eq!(env.get(k), Some(&"hello".to_string()));
    }

    #[test]
    fn contains() {
        let mut env = TypedEnv::new();
        let k = env.alloc(true);
        assert!(env.contains(k));
        assert!(!env.contains(VarKey::<bool>::new(999)));
    }

    #[test]
    fn contains_raw() {
        let mut env = TypedEnv::new();
        let k = env.alloc(42i32);
        assert!(env.contains_raw(k.id));
        assert!(!env.contains_raw(999));
    }

    #[test]
    fn type_safety() {
        let mut env = TypedEnv::new();
        env.insert(0, 42i32);
        let wrong_key: VarKey<String> = VarKey::new(0);
        assert!(env.get(wrong_key).is_none());
    }

    #[test]
    fn heterogeneous() {
        let mut env = TypedEnv::new();
        let k1 = env.alloc(42i32);
        let k2 = env.alloc("hello".to_string());
        let k3 = env.alloc(true);
        assert_eq!(env.get(k1), Some(&42));
        assert_eq!(env.get(k2), Some(&"hello".to_string()));
        assert_eq!(env.get(k3), Some(&true));
        assert_eq!(env.len(), 3);
    }

    #[test]
    fn clone_env() {
        let mut env = TypedEnv::new();
        let k = env.alloc(42i32);
        let env2 = env.clone();
        assert_eq!(env2.get(k), Some(&42));
    }
}
