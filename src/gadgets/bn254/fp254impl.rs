use std::str::FromStr;

use num_bigint::BigUint;
use num_traits::Zero;

use super::super::bigint::{self, BigIntWires};
use crate::{math::montgomery::calculate_montgomery_constants, Circuit, Gate};

/// Core trait for BN254 field implementation with 254-bit prime field arithmetic
/// Provides constants and operations for field elements in Montgomery form
pub trait Fp254Impl {
    /// The prime modulus for the field
    const MODULUS: &'static str;

    /// Montgomery constant R = 2^254
    const MONTGOMERY_R: &'static str =
        "28948022309329048855892746252171976963317496166410141009864396001978282409984";

    /// MODULUS^-1 modulo R  
    const MONTGOMERY_M_INVERSE: &'static str;

    /// R^-1 modulo MODULUS
    const MONTGOMERY_R_INVERSE: &'static str;

    /// Number of bits in field elements
    const N_BITS: usize;

    /// (MODULUS+1)/4 for square root operations
    const MODULUS_ADD_1_DIV_4: &'static str =
        "5472060717959818805561601436314318772174077789324455915672259473661306552146";

    /// Convert modulus string to BigUint
    fn modulus_as_biguint() -> BigUint {
        BigUint::from_str(Self::MODULUS).unwrap()
    }

    /// Convert Montgomery R to BigUint
    fn montgomery_r_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_R).unwrap()
    }

    /// Convert Montgomery modulus inverse to BigUint
    fn montgomery_m_inverse_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_M_INVERSE).unwrap()
    }

    /// Convert Montgomery R inverse to BigUint
    fn montgomery_r_inverse_as_biguint() -> BigUint {
        BigUint::from_str(Self::MONTGOMERY_R_INVERSE).unwrap()
    }

    /// Calculate 2^N_BITS - MODULUS
    fn not_modulus_as_biguint() -> BigUint {
        let p = Self::modulus_as_biguint();
        let a = BigUint::from(2u32).pow(Self::N_BITS.try_into().unwrap());
        a - p
    }

    /// Half of the modulus for efficient division by 2
    fn half_modulus() -> BigUint;

    /// One third of the modulus for division by 6
    fn one_third_modulus() -> BigUint;

    /// Two thirds of the modulus for division by 6
    fn two_third_modulus() -> BigUint;

    /// Validate Montgomery constants are correct
    fn validate_montgomery_constants() -> bool {
        let modulus = Self::modulus_as_biguint();
        let r = Self::montgomery_r_as_biguint();
        let (r_inv_calc, m_inv_calc) = calculate_montgomery_constants(modulus.clone(), r.clone());

        let r_inv_expected = Self::montgomery_r_inverse_as_biguint();
        let m_inv_expected = Self::montgomery_m_inverse_as_biguint();

        r_inv_calc == r_inv_expected && m_inv_calc == m_inv_expected
    }

    fn add(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);

        let mut wires1 = bigint::add_generic(circuit, a, b);
        let u = wires1.pop().unwrap();

        let mut wires2 =
            bigint::add_constant_generic(circuit, &wires1, &Self::not_modulus_as_biguint());

        wires2.pop();

        let v = bigint::less_than_constant(circuit, &wires1, &Self::modulus_as_biguint());
        let s = circuit.issue_wire();

        circuit.add_gate(Gate::and_variant(u, v, s, [true, false, false]));

        bigint::select(circuit, &wires1, &wires2, s)
    }

    /// Field subtraction: (a - b) mod p
    fn sub(_circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        todo!()
    }

    /// Field negation: (-a) mod p
    fn neg(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }

    /// Field doubling: (2 * a) mod p
    fn double(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }

    /// Field halving: (a / 2) mod p
    fn half(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }

    /// Montgomery multiplication: (a * b * R^-1) mod p
    fn mul_montgomery(_circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        todo!()
    }

    /// Montgomery squaring: (a * a * R^-1) mod p
    fn square_montgomery(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        Self::mul_montgomery(_circuit, a, a)
    }

    /// Montgomery reduction: converts from Montgomery form to normal form
    fn montgomery_reduce(_circuit: &mut Circuit, x: &BigIntWires) -> BigIntWires {
        assert_eq!(x.len(), 2 * Self::N_BITS);
        todo!()
    }

    /// Modular inverse using extended Euclidean algorithm
    fn inverse(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }

    /// Modular inverse in Montgomery form
    fn inverse_montgomery(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }

    /// Exponentiation by constant in Montgomery form
    fn exp_by_constant_montgomery(
        _circuit: &mut Circuit,
        a: &BigIntWires,
        _exp: &BigUint,
    ) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::*;

    struct TestField;

    impl Fp254Impl for TestField {
        const MODULUS: &'static str =
            "21888242871839275222246405745257275088548364400416034343698204186575808495617";
        const MONTGOMERY_M_INVERSE: &'static str = "18446744073709551615";
        const MONTGOMERY_R_INVERSE: &'static str = "1";
        const N_BITS: usize = 254;

        fn half_modulus() -> BigUint {
            Self::modulus_as_biguint() / 2u32
        }

        fn one_third_modulus() -> BigUint {
            Self::modulus_as_biguint() / 3u32
        }

        fn two_third_modulus() -> BigUint {
            Self::modulus_as_biguint() * 2u32 / 3u32
        }
    }

    fn test_field_add_operation(a_val: &BigUint, b_val: &BigUint, expected: &BigUint) {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, TestField::N_BITS, true, false);
        let b = BigIntWires::new(&mut circuit, TestField::N_BITS, true, false);
        let result = TestField::add(&mut circuit, &a, &b);

        assert_eq!(result.len(), TestField::N_BITS);

        result.iter().for_each(|bit| {
            circuit.make_wire_output(*bit);
        });

        let a_input = a.get_wire_bits_fn(a_val).unwrap();
        let b_input = b.get_wire_bits_fn(b_val).unwrap();
        let get_expected_result_fn = result.get_wire_bits_fn(expected).unwrap();

        circuit.full_cycle_test(
            |id| a_input(id).or_else(|| b_input(id)),
            get_expected_result_fn,
        );
    }

    #[test]
    fn test_modulus_conversion() {
        let modulus = TestField::modulus_as_biguint();
        assert!(!modulus.is_zero());
        assert!(modulus.bits() <= 254);
    }

    #[test]
    fn test_not_modulus() {
        let not_mod = TestField::not_modulus_as_biguint();
        let modulus = TestField::modulus_as_biguint();
        let power_of_two = BigUint::from(2u32).pow(254);

        assert_eq!(not_mod + modulus, power_of_two);
    }

    #[test]
    fn test_add_zero_zero() {
        let a = BigUint::from(0u32);
        let b = BigUint::from(0u32);
        let expected = BigUint::from(0u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_zero_one() {
        let a = BigUint::from(0u32);
        let b = BigUint::from(1u32);
        let expected = BigUint::from(1u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_one_one() {
        let a = BigUint::from(1u32);
        let b = BigUint::from(1u32);
        let expected = BigUint::from(2u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_small_numbers() {
        let a = BigUint::from(42u32);
        let b = BigUint::from(58u32);
        let expected = BigUint::from(100u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_modular_reduction() {
        let modulus = TestField::modulus_as_biguint();
        let a = &modulus - 1u32;
        let b = BigUint::from(2u32);
        let expected = BigUint::from(1u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_modular_reduction_exact() {
        let modulus = TestField::modulus_as_biguint();
        let a = &modulus - 1u32;
        let b = BigUint::from(1u32);
        let expected = BigUint::from(0u32);
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_large_numbers() {
        let modulus = TestField::modulus_as_biguint();
        let a = &modulus / 2u32;
        let b = &modulus / 3u32;
        let expected = (&modulus / 2u32 + &modulus / 3u32) % &modulus;
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_both_near_modulus() {
        let modulus = TestField::modulus_as_biguint();
        let a = &modulus - 100u32;
        let b = &modulus - 200u32;
        let expected = (&modulus - 100u32 + &modulus - 200u32) % &modulus;
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    fn test_add_maximum_values() {
        let modulus = TestField::modulus_as_biguint();
        let a = &modulus - 1u32;
        let b = &modulus - 1u32;
        let expected = (&modulus - 1u32 + &modulus - 1u32) % &modulus;
        test_field_add_operation(&a, &b, &expected);
    }

    #[test]
    #[should_panic(expected = "assertion `left == right` failed")]
    fn test_add_wrong_size_input_a() {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, TestField::N_BITS - 1, true, false);
        let b = BigIntWires::new(&mut circuit, TestField::N_BITS, true, false);
        TestField::add(&mut circuit, &a, &b);
    }

    #[test]
    #[should_panic(expected = "assertion `left == right` failed")]
    fn test_add_wrong_size_input_b() {
        let mut circuit = Circuit::default();
        let a = BigIntWires::new(&mut circuit, TestField::N_BITS, true, false);
        let b = BigIntWires::new(&mut circuit, TestField::N_BITS - 1, true, false);
        TestField::add(&mut circuit, &a, &b);
    }
}
