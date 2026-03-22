// Should fail: unknown attribute key
use proptest_lockstep::prelude::*;

#[derive(Debug, Clone, PartialEq)]
struct Model;

#[proptest_lockstep::lockstep_actions(state = Model)]
pub mod actions {
    #[action(real_return = "i32", foobar = "baz")]
    pub struct Get;
}

fn main() {}
