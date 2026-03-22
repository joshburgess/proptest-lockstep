// Should fail: real_return and model_return differ but no opaque_types
use proptest_lockstep::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Model;

#[derive(Debug, Clone, PartialEq)]
struct RealHandle(u64);

#[derive(Debug, Clone, PartialEq)]
struct MockHandle(u64);

#[proptest_lockstep::lockstep_actions(state = Model)]
pub mod actions {
    #[action(
        real_return = "RealHandle",
        model_return = "MockHandle",
    )]
    pub struct Create;
}

fn main() {}
