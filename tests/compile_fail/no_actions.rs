// Should fail: module with no #[action] structs
use proptest_lockstep::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Model;

#[proptest_lockstep::lockstep_actions(state = Model)]
pub mod actions {
    pub struct NotAnAction;
}

fn main() {}
