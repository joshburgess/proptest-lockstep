// Should fail: opaque_types maps to wrong model type
use proptest_lockstep::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Model;

#[derive(Debug, Clone, PartialEq)]
struct RealHandle(u64);

#[derive(Debug, Clone, PartialEq)]
struct MockHandle(u64);

#[derive(Debug, Clone, PartialEq)]
struct WrongHandle(u64);

#[proptest_lockstep::lockstep_actions(state = Model)]
pub mod actions {
    #[action(
        real_return = "RealHandle",
        model_return = "MockHandle",
        opaque_types = { RealHandle => WrongHandle },
    )]
    pub struct Create;
}

fn main() {}
