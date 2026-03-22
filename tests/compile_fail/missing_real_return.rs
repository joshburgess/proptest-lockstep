// Should fail: missing real_return attribute
use proptest_lockstep::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Model;

#[proptest_lockstep::lockstep_actions(state = Model)]
pub mod actions {
    #[action(bridge = "Transparent<i32>")]
    pub struct Get;
}

fn main() {}
