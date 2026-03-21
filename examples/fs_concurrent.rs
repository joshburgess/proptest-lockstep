#![allow(dead_code)]
//! Concurrent file system lockstep test with linearizability checking.
//!
//! Demonstrates linearizability checking with opaque handles:
//! - `FileHandle` (real) vs `MockHandle` (model) — different types
//! - GVar projections resolve handles from `Result<(Handle, Path), Err>`
//! - The linearizability checker uses generation-time var IDs to ensure
//!   correct variable resolution across interleaving candidates
//!
//! Run with: `cargo test --example fs_concurrent --features concurrent`

use std::any::Any;
use std::collections::HashMap;

use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

use proptest_lockstep::prelude::*;

// ============================================================================
// Domain types (duplicated from file_system — examples can't import each other)
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FileHandle(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MockHandle(usize);

#[derive(Debug, Clone, PartialEq)]
pub enum FsErr {
    NotFound,
    AlreadyOpen,
    BadHandle,
}

// ============================================================================
// System under test
// ============================================================================

#[derive(Debug)]
pub struct RealFs {
    files: HashMap<String, String>,
    open: HashMap<FileHandle, String>,
    next: usize,
}

impl RealFs {
    fn new() -> Self { RealFs { files: HashMap::new(), open: HashMap::new(), next: 0 } }

    fn open(&mut self, path: &str) -> Result<(FileHandle, String), FsErr> {
        if self.open.values().any(|p| p == path) { return Err(FsErr::AlreadyOpen); }
        let h = FileHandle(self.next);
        self.next += 1;
        self.open.insert(h.clone(), path.into());
        Ok((h, path.into()))
    }

    fn write(&mut self, h: &FileHandle, data: &str) -> Result<(), FsErr> {
        let path = self.open.get(h).ok_or(FsErr::BadHandle)?.clone();
        self.files.insert(path, data.into());
        Ok(())
    }

    fn close(&mut self, h: &FileHandle) -> Result<(), FsErr> {
        self.open.remove(h).map(|_| ()).ok_or(FsErr::BadHandle)
    }

    fn read(&self, path: &str) -> Result<String, FsErr> {
        self.files.get(path).cloned().ok_or(FsErr::NotFound)
    }
}

// ============================================================================
// Model
// ============================================================================

#[derive(Debug, Clone)]
pub struct MockFs {
    files: HashMap<String, String>,
    open: HashMap<MockHandle, String>,
    next: usize,
}

impl MockFs {
    fn new() -> Self { MockFs { files: HashMap::new(), open: HashMap::new(), next: 0 } }

    fn open(&mut self, path: &str) -> Result<(MockHandle, String), FsErr> {
        if self.open.values().any(|p| p == path) { return Err(FsErr::AlreadyOpen); }
        let h = MockHandle(self.next);
        self.next += 1;
        self.open.insert(h.clone(), path.into());
        Ok((h, path.into()))
    }

    fn write(&mut self, h: &MockHandle, data: &str) -> Result<(), FsErr> {
        let path = self.open.get(h).ok_or(FsErr::BadHandle)?.clone();
        self.files.insert(path, data.into());
        Ok(())
    }

    fn close(&mut self, h: &MockHandle) -> Result<(), FsErr> {
        self.open.remove(h).map(|_| ()).ok_or(FsErr::BadHandle)
    }

    fn read(&self, path: &str) -> Result<String, FsErr> {
        self.files.get(path).cloned().ok_or(FsErr::NotFound)
    }
}

// ============================================================================
// Type aliases
// ============================================================================

type OpenReal = Result<(FileHandle, String), FsErr>;
type OpenModel = Result<(MockHandle, String), FsErr>;
type HandleProj = OpComp<OpOk, OpFst, (FileHandle, String)>;
type ModelHandleProj = OpComp<OpOk, OpFst, (MockHandle, String)>;

// ============================================================================
// Actions
// ============================================================================

#[proptest_lockstep::lockstep_actions(state = MockFs)]
pub mod fs {
    #[action(
        real_return = "Result<(FileHandle, String), FsErr>",
        model_return = "Result<(MockHandle, String), FsErr>",
        bridge = "ResultBridge<TupleBridge<Opaque<FileHandle, MockHandle>, Transparent<String>>, Transparent<FsErr>>",
    )]
    pub struct Open { pub path: String }

    #[action(
        real_return = "Result<(), FsErr>",
        bridge = "ResultBridge<Transparent<()>, Transparent<FsErr>>",
        uses = [handle],
    )]
    pub struct Write {
        pub handle: GVar<OpenReal, FileHandle, HandleProj>,
        pub data: String,
    }

    #[action(
        real_return = "Result<(), FsErr>",
        bridge = "ResultBridge<Transparent<()>, Transparent<FsErr>>",
        uses = [handle],
    )]
    pub struct Close {
        pub handle: GVar<OpenReal, FileHandle, HandleProj>,
    }

    #[action(
        real_return = "Result<String, FsErr>",
        bridge = "ResultBridge<Transparent<String>, Transparent<FsErr>>",
    )]
    pub struct Read { pub path: String }
}

// ============================================================================
// Interpreters
// ============================================================================

#[derive(Debug, Clone)]
pub struct FsLockstep;

impl fs::FsModelInterp for FsLockstep {
    type State = MockFs;

    fn open(s: &mut MockFs, a: &fs::Open, _: &TypedEnv) -> OpenModel {
        s.open(&a.path)
    }

    fn write(s: &mut MockFs, a: &fs::Write, env: &TypedEnv) -> Result<(), FsErr> {
        match resolve_model_gvar::<OpenModel, MockHandle, ModelHandleProj>(
            a.handle.var_id(),
            &OpComp::new(OpOk, OpFst),
            env,
        ) {
            Some(h) => s.write(&h, &a.data),
            None => Err(FsErr::BadHandle),
        }
    }

    fn close(s: &mut MockFs, a: &fs::Close, env: &TypedEnv) -> Result<(), FsErr> {
        match resolve_model_gvar::<OpenModel, MockHandle, ModelHandleProj>(
            a.handle.var_id(),
            &OpComp::new(OpOk, OpFst),
            env,
        ) {
            Some(h) => s.close(&h),
            None => Err(FsErr::BadHandle),
        }
    }

    fn read(s: &mut MockFs, a: &fs::Read, _: &TypedEnv) -> Result<String, FsErr> {
        s.read(&a.path)
    }
}

impl fs::FsSutInterp for FsLockstep {
    type Sut = RealFs;

    fn open(s: &mut RealFs, a: &fs::Open, _: &TypedEnv) -> OpenReal {
        s.open(&a.path)
    }

    fn write(s: &mut RealFs, a: &fs::Write, env: &TypedEnv) -> Result<(), FsErr> {
        match resolve_gvar(&a.handle, env) {
            Some(h) => s.write(&h, &a.data),
            None => Err(FsErr::BadHandle),
        }
    }

    fn close(s: &mut RealFs, a: &fs::Close, env: &TypedEnv) -> Result<(), FsErr> {
        match resolve_gvar(&a.handle, env) {
            Some(h) => s.close(&h),
            None => Err(FsErr::BadHandle),
        }
    }

    fn read(s: &mut RealFs, a: &fs::Read, _: &TypedEnv) -> Result<String, FsErr> {
        s.read(&a.path)
    }
}

// ============================================================================
// LockstepModel
// ============================================================================

impl LockstepModel for FsLockstep {
    type ModelState = MockFs;
    type Sut = RealFs;

    fn init_model() -> MockFs { MockFs::new() }
    fn init_sut() -> RealFs { RealFs::new() }

    fn gen_action(_state: &MockFs, env: &TypedEnv) -> BoxedStrategy<Box<dyn AnyAction>> {
        let paths = vec!["a.txt", "b.txt", "c.txt"];

        let handles: Vec<SymVar<OpenReal>> = (0..env.next_id())
            .filter(|id| env.contains(VarKey::<OpenReal>::new(*id)))
            .map(|id| SymVar::new(id))
            .collect();

        let ps = proptest::sample::select(paths.clone());
        let mut strats: Vec<BoxedStrategy<Box<dyn AnyAction>>> = vec![
            ps.clone().prop_map(|p| fs::open(fs::Open { path: p.into() })).boxed(),
            ps.prop_map(|p| fs::read(fs::Read { path: p.into() })).boxed(),
        ];

        if !handles.is_empty() {
            let hs = handles.clone();
            strats.push(
                (proptest::sample::select(hs), "[a-z]{1,10}")
                    .prop_map(|(v, d)| fs::write(fs::Write {
                        handle: GVar::new(v, OpOk).then(OpFst),
                        data: d,
                    })).boxed(),
            );
            strats.push(
                proptest::sample::select(handles)
                    .prop_map(|v| fs::close(fs::Close {
                        handle: GVar::new(v, OpOk).then(OpFst),
                    })).boxed(),
            );
        }

        proptest::strategy::Union::new(strats).boxed()
    }

    fn precondition(_: &MockFs, action: &dyn AnyAction, env: &TypedEnv) -> bool {
        for var_id in &action.used_vars() {
            if let Some(result) = env.get(VarKey::<OpenReal>::new(*var_id)) {
                if result.is_err() { return false; }
            }
        }
        true
    }

    fn step_model(state: &mut MockFs, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        fs::dispatch_model::<FsLockstep>(state, action, env)
    }

    fn step_sut(sut: &mut RealFs, action: &dyn AnyAction, env: &TypedEnv) -> Box<dyn Any> {
        fs::dispatch_sut::<FsLockstep>(sut, action, env)
    }
}

// ============================================================================
// ConcurrentLockstepModel — opt-in for linearizability
// ============================================================================

#[cfg(feature = "concurrent")]
impl proptest_lockstep::concurrent::ConcurrentLockstepModel for FsLockstep {
    fn step_sut_send(
        sut: &mut RealFs,
        action: &dyn AnyAction,
        env: &TypedEnv,
    ) -> Box<dyn Any + Send> {
        fs::dispatch_sut_send::<FsLockstep>(sut, action, env)
    }
}

fn main() {
    println!("Run with `cargo test --example fs_concurrent --features concurrent`");
}

#[cfg(all(test, feature = "concurrent"))]
mod tests {
    use super::*;
    use proptest_lockstep::concurrent::{
        lockstep_concurrent, lockstep_linearizable,
        ConcurrentConfig, SplitStrategy,
    };

    #[test]
    fn concurrent_fs_crash_absence() {
        lockstep_concurrent::<FsLockstep>(ConcurrentConfig {
            iterations: 50,
            prefix_len: 3,
            branch_len: 3,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }

    #[test]
    fn concurrent_fs_linearizable() {
        // Linearizability with opaque handles: the checker must use
        // generation-time var IDs to correctly resolve GVar projections
        // across different interleaving candidates.
        lockstep_linearizable::<FsLockstep>(ConcurrentConfig {
            iterations: 30,
            prefix_len: 3,
            branch_len: 2,
            branch_count: 2,
            split_strategy: SplitStrategy::RoundRobin,
            ..Default::default()
        });
    }
}
