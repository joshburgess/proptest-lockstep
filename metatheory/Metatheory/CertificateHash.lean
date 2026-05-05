/-
  Certificate Hash Verification

  Implements FNV-1a hashing in Lean and proves that the hash values
  for each bridge type match the constants embedded in the Rust
  `BridgeCertificate`. This closes the gap between the Rust-computed
  hashes and the Lean proofs -- the hashes are now verified on both sides.

  The cross-verification protocol:
  1. Lean computes `fnv1a "Transparent"` and proves it equals `0xd0e945b97c0c46d1`
  2. Rust's `BridgeCertificate` for `Transparent<T>` contains `0xd0e945b97c0c46d1`
  3. Both sides agree on the hash → the certificate links to the correct proof
-/

import Metatheory.CertifiedSynthesis

-- =========================================================================
-- FNV-1a hash implementation
-- =========================================================================

/-- FNV-1a offset basis (64-bit). -/
def fnv_offset_basis : UInt64 := 0xcbf29ce484222325

/-- FNV-1a prime (64-bit). -/
def fnv_prime : UInt64 := 0x100000001b3

/-- FNV-1a hash of a single byte. -/
def fnv_step (hash : UInt64) (byte : UInt8) : UInt64 :=
  (hash ^^^ byte.toUInt64) * fnv_prime

/-- FNV-1a hash of a byte list. -/
def fnv1a (bytes : List UInt8) : UInt64 :=
  bytes.foldl fnv_step fnv_offset_basis

/-- Convert a string to its UTF-8 byte representation. -/
def string_to_bytes (s : String) : List UInt8 :=
  s.toUTF8.toList

/-- FNV-1a hash of a string. -/
def fnv1a_string (s : String) : UInt64 :=
  fnv1a (string_to_bytes s)

-- =========================================================================
-- Verified hash constants
-- =========================================================================

/-- Hash for "Transparent" -- must match Rust's `fnv1a_hash(b"Transparent")`. -/
def hash_transparent : UInt64 := fnv1a_string "Transparent"

/-- Hash for "Opaque". -/
def hash_opaque : UInt64 := fnv1a_string "Opaque"

/-- Hash for "ResultBridge". -/
def hash_result_bridge : UInt64 := fnv1a_string "ResultBridge"

/-- Hash for "TupleBridge". -/
def hash_tuple_bridge : UInt64 := fnv1a_string "TupleBridge"

/-- Hash for "OptionBridge". -/
def hash_option_bridge : UInt64 := fnv1a_string "OptionBridge"

/-- Hash for "VecBridge". -/
def hash_vec_bridge : UInt64 := fnv1a_string "VecBridge"

/-- Hash for "UnitBridge". -/
def hash_unit_bridge : UInt64 := fnv1a_string "UnitBridge"

-- =========================================================================
-- Verification: Lean hashes match Rust constants
-- =========================================================================

/--
  **Transparent hash verification.**
  The Lean-computed FNV-1a hash of "Transparent" equals the constant
  embedded in the Rust `BridgeCertificate` for `Transparent<T>`.
-/
theorem transparent_hash_verified :
    hash_transparent = (0xd0e945b97c0c46d1 : UInt64) := by native_decide

/-- **Opaque hash verification.** -/
theorem opaque_hash_verified :
    hash_opaque = (0x66d852e3c020e79e : UInt64) := by native_decide

/-- **ResultBridge hash verification.** -/
theorem result_bridge_hash_verified :
    hash_result_bridge = (0xec942b90aa831451 : UInt64) := by native_decide

/-- **TupleBridge hash verification.** -/
theorem tuple_bridge_hash_verified :
    hash_tuple_bridge = (0xa294df1dde196004 : UInt64) := by native_decide

/-- **OptionBridge hash verification.** -/
theorem option_bridge_hash_verified :
    hash_option_bridge = (0x81b187977a037601 : UInt64) := by native_decide

/-- **VecBridge hash verification.** -/
theorem vec_bridge_hash_verified :
    hash_vec_bridge = (0x40c9aea80867e530 : UInt64) := by native_decide

/-- **UnitBridge hash verification.** -/
theorem unit_bridge_hash_verified :
    hash_unit_bridge = (0x2cdc75cea11137a6 : UInt64) := by native_decide

-- =========================================================================
-- All hashes are distinct
-- =========================================================================

/--
  **Hash uniqueness**: all primitive bridge hashes are distinct.
  This ensures certificates can't be confused.
-/
theorem all_hashes_distinct :
    hash_transparent ≠ hash_opaque
    ∧ hash_transparent ≠ hash_result_bridge
    ∧ hash_transparent ≠ hash_tuple_bridge
    ∧ hash_transparent ≠ hash_option_bridge
    ∧ hash_transparent ≠ hash_vec_bridge
    ∧ hash_transparent ≠ hash_unit_bridge
    ∧ hash_opaque ≠ hash_result_bridge
    ∧ hash_opaque ≠ hash_tuple_bridge
    ∧ hash_opaque ≠ hash_option_bridge
    ∧ hash_opaque ≠ hash_vec_bridge
    ∧ hash_opaque ≠ hash_unit_bridge
    ∧ hash_result_bridge ≠ hash_tuple_bridge
    ∧ hash_result_bridge ≠ hash_option_bridge
    ∧ hash_result_bridge ≠ hash_vec_bridge
    ∧ hash_result_bridge ≠ hash_unit_bridge
    ∧ hash_tuple_bridge ≠ hash_option_bridge
    ∧ hash_tuple_bridge ≠ hash_vec_bridge
    ∧ hash_tuple_bridge ≠ hash_unit_bridge
    ∧ hash_option_bridge ≠ hash_vec_bridge
    ∧ hash_option_bridge ≠ hash_unit_bridge
    ∧ hash_vec_bridge ≠ hash_unit_bridge := by native_decide
