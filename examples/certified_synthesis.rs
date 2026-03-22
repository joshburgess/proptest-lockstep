#![allow(dead_code)]
//! Certified bridge synthesis demonstration.
//!
//! Shows that bridges produced by the proc macro's `derive_bridge`
//! are certified — each bridge type implements `CertifiedLockstepBridge`,
//! which links to the corresponding Lean soundness proof.
//!
//! The `verify_certified` function is a compile-time check: if a
//! bridge type doesn't have a certificate, the code won't compile.
//!
//! Run with: `cargo test --example certified_synthesis`

use proptest_lockstep::bridge::*;
use proptest_lockstep::certified::{CertifiedLockstepBridge, verify_certified};

fn main() {
    println!("Run with `cargo test --example certified_synthesis`");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Transparent bridges are certified.
    #[test]
    fn transparent_is_certified() {
        let desc = verify_certified::<Transparent<String>>();
        assert!(desc.contains("certified"));
    }

    /// Opaque bridges are certified.
    #[test]
    fn opaque_is_certified() {
        let desc = verify_certified::<Opaque<u64, u32>>();
        assert!(desc.contains("certified"));
    }

    /// Composed bridges (ResultBridge<TupleBridge<Opaque, Transparent>, Transparent>)
    /// are certified — the certification composes through the bridge algebra.
    #[test]
    fn composed_bridge_is_certified() {
        type MyBridge = ResultBridge<
            TupleBridge<Opaque<u64, u32>, Transparent<String>>,
            Transparent<bool>,
        >;
        let desc = verify_certified::<MyBridge>();
        assert!(desc.contains("certified"));
    }

    /// OptionBridge is certified.
    #[test]
    fn option_bridge_is_certified() {
        let desc = verify_certified::<OptionBridge<Transparent<i32>>>();
        assert!(desc.contains("certified"));
    }

    /// VecBridge is certified.
    #[test]
    fn vec_bridge_is_certified() {
        let desc = verify_certified::<VecBridge<Transparent<String>>>();
        assert!(desc.contains("certified"));
    }

    /// UnitBridge is certified.
    #[test]
    fn unit_bridge_is_certified() {
        let desc = verify_certified::<UnitBridge>();
        assert!(desc.contains("certified"));
    }

    /// Print all synthesis descriptions.
    #[test]
    fn print_certificates() {
        println!("Transparent<String>: {}", Transparent::<String>::synthesis_description());
        println!("Opaque<u64, u32>:    {}", Opaque::<u64, u32>::synthesis_description());
        println!("ResultBridge:        {}", <ResultBridge<Transparent<i32>, Transparent<bool>>>::synthesis_description());
        println!("TupleBridge:         {}", <TupleBridge<Transparent<i32>, Transparent<bool>>>::synthesis_description());
        println!("OptionBridge:        {}", <OptionBridge<Transparent<i32>>>::synthesis_description());
        println!("VecBridge:           {}", <VecBridge<Transparent<i32>>>::synthesis_description());
        println!("UnitBridge:          {}", UnitBridge::synthesis_description());
    }
}
