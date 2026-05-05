#![allow(dead_code)]
//! Certified bridge synthesis demonstration.
//!
//! Shows that bridges carry machine-verifiable certificates linking
//! them to Lean soundness proofs. Each certificate contains the
//! theorem name, Lean file path, construction method, and a
//! structural hash for cross-checking.
//!
//! Run with: `cargo test --example certified_synthesis`

use proptest_lockstep::bridge::*;
use proptest_lockstep::certified::{CertifiedLockstepBridge, verify_certified, BridgeCertificate};

fn main() {
    println!("Run with `cargo test --example certified_synthesis`");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transparent_certificate() {
        let cert = verify_certified::<Transparent<String>>();
        assert_eq!(cert.theorem, "certified_transparent_sound");
        assert_eq!(cert.lean_file, "Metatheory/CertifiedSynthesis.lean");
        assert!(cert.construction.contains("transparent"));
        assert_ne!(cert.structural_hash, 0);
    }

    #[test]
    fn opaque_certificate() {
        let cert = verify_certified::<Opaque<u64, u32>>();
        assert_eq!(cert.theorem, "certified_opaque_sound");
        assert!(cert.construction.contains("opaque"));
    }

    #[test]
    fn composed_bridge_certificate() {
        type MyBridge = ResultBridge<
            TupleBridge<Opaque<u64, u32>, Transparent<String>>,
            Transparent<bool>,
        >;
        let cert = verify_certified::<MyBridge>();
        assert_eq!(cert.theorem, "certified_sum_ok");
        // Structural hash incorporates sub-bridge hashes
        assert_ne!(cert.structural_hash, verify_certified::<Transparent<bool>>().structural_hash);
    }

    #[test]
    fn structural_hashes_are_unique() {
        let transparent = verify_certified::<Transparent<String>>();
        let opaque = verify_certified::<Opaque<u64, u32>>();
        let option = verify_certified::<OptionBridge<Transparent<i32>>>();
        let vec = verify_certified::<VecBridge<Transparent<i32>>>();
        let unit = verify_certified::<UnitBridge>();

        // All primitive hashes should differ
        let hashes = vec![
            transparent.structural_hash,
            opaque.structural_hash,
            option.structural_hash,
            vec.structural_hash,
            unit.structural_hash,
        ];
        for i in 0..hashes.len() {
            for j in (i + 1)..hashes.len() {
                assert_ne!(
                    hashes[i], hashes[j],
                    "Hash collision between bridge types"
                );
            }
        }
    }

    #[test]
    fn composed_hash_differs_from_components() {
        let result_cert = verify_certified::<ResultBridge<Transparent<i32>, Transparent<bool>>>();
        let tuple_cert = verify_certified::<TupleBridge<Transparent<i32>, Transparent<bool>>>();

        // ResultBridge and TupleBridge with same components should have different hashes
        assert_ne!(result_cert.structural_hash, tuple_cert.structural_hash);
    }

    #[test]
    fn certificate_display() {
        let cert = verify_certified::<Transparent<String>>();
        let display = format!("{}", cert);
        assert!(display.contains("certified_transparent_sound"));
        assert!(display.contains("CertifiedSynthesis.lean"));
        assert!(display.contains("0x"));
    }

    #[test]
    fn print_all_certificates() {
        println!("Transparent<String>:  {}", verify_certified::<Transparent<String>>());
        println!("Opaque<u64, u32>:     {}", verify_certified::<Opaque<u64, u32>>());
        println!("ResultBridge:         {}", verify_certified::<ResultBridge<Transparent<i32>, Transparent<bool>>>());
        println!("TupleBridge:          {}", verify_certified::<TupleBridge<Transparent<i32>, Transparent<bool>>>());
        println!("OptionBridge:         {}", verify_certified::<OptionBridge<Transparent<i32>>>());
        println!("VecBridge:            {}", verify_certified::<VecBridge<Transparent<i32>>>());
        println!("UnitBridge:           {}", verify_certified::<UnitBridge>());
    }
}
