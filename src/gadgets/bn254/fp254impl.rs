use std::str::FromStr;

use ark_ff::AdditiveGroup;
use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::super::bigint::{self, BigIntWires};
use crate::{Circuit, Gate, math::montgomery::calculate_montgomery_constants};

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

    fn add_constant(circuit: &mut Circuit, a: &BigIntWires, b: &ark_bn254::Fq) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        if b.is_zero() {
            return a.clone();
        }

        let mut wires_1 = bigint::add_constant_generic(circuit, a, &BigUint::from(*b));
        let u = wires_1.pop().unwrap();
        let mut wires_2 =
            bigint::add_constant_generic(circuit, &wires_1, &Self::not_modulus_as_biguint());

        wires_2.pop();

        let v = bigint::less_than_constant(circuit, &wires_1, &Self::modulus_as_biguint());

        let s = circuit.issue_wire();

        circuit.add_gate(Gate::and_variant(u, v, s, [true, false, false]));

        bigint::select(circuit, &wires_1, &wires_2, s)
    }

    /// Field subtraction: (a - b) mod p
    fn sub(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);

        let neg_b = Self::neg(circuit, b);
        Self::add(circuit, a, &neg_b)
    }

    /// Field negation: (-a) mod p
    fn neg(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        a.iter().for_each(|wire_id| {
            circuit.add_gate(Gate::not(*wire_id));
        });

        Self::add_constant(
            circuit,
            a,
            &(ark_bn254::Fq::from(1) - ark_bn254::Fq::from(Self::not_modulus_as_biguint())),
        )
    }

    /// Field doubling: (2 * a) mod p
    fn double(_circuit: &mut Circuit, _a: &BigIntWires) -> BigIntWires {
        todo!()
        //assert_eq!(a.len(), Self::N_BITS);

        //let shift_wire = circuit.issue_wire();
        //circuit.add_gate(Gate::constant(shift_wire, false));

        //let mut aa = a.clone();
        //let u = aa.pop().unwrap();
        //let mut shifted_wires = vec![shift_wire];
        //shifted_wires.extend(aa);

        //let c = Self::not_modulus_as_biguint();
        //let mut wires_2 = bigint::add_constant_generic(circuit, &shifted_wires, &c);
        //wires_2.pop();

        //let v = bigint::less_than_constant(circuit, &shifted_wires, &Self::modulus_as_biguint());
        //let s = circuit.issue_wire();

        //circuit.add_gate(Gate::and_variant(u, v, s, [true, false, false]));

        //bigint::select(circuit, &shifted_wires, &wires_2, s)
    }

    /// Field halving: (a / 2) mod p
    fn half(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        let selector = a.get(0).unwrap();
        let wires_1 = bigint::half(circuit, a);
        let wires_2 = bigint::add_constant_generic(circuit, &wires_1, &Self::half_modulus());

        bigint::select(circuit, &wires_2, &wires_1, selector)
    }

    /// Montgomery multiplication: (a * b * R^-1) mod p
    fn mul_montgomery(_circuit: &mut Circuit, _a: &BigIntWires, _b: &BigIntWires) -> BigIntWires {
        todo!()
        //assert_eq!(a.len(), Self::N_BITS);
        //assert_eq!(b.len(), Self::N_BITS);

        //let mul_result = bigint::mul::mul_karatsuba_generic(circuit, a, b);
        //Self::montgomery_reduce(circuit, &mul_result)
    }

    /// Montgomery squaring: (a * a * R^-1) mod p
    fn square_montgomery(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        Self::mul_montgomery(circuit, a, a)
    }

    /// Montgomery reduction: converts from Montgomery form to normal form
    fn montgomery_reduce(_circuit: &mut Circuit, _x: &BigIntWires) -> BigIntWires {
        todo!()
        //assert_eq!(x.len(), 2 * Self::N_BITS);

        //// Extract low and high parts of x
        //let mut x_low_bits = Vec::new();
        //let mut x_high_bits = Vec::new();

        //for i in 0..254 {
        //    x_low_bits.push(x.get(i).unwrap());
        //}
        //for i in 254..x.len() {
        //    x_high_bits.push(x.get(i).unwrap());
        //}

        //let x_low = BigIntWires { bits: x_low_bits };
        //let x_high = BigIntWires { bits: x_high_bits };

        //let q = bigint::mul::mul_by_constant_modulo_power_two(
        //    circuit,
        //    &x_low,
        //    &Self::montgomery_m_inverse_as_biguint(),
        //    254,
        //);

        //let sub = bigint::mul::mul_by_constant(circuit, &q, &Self::modulus_as_biguint());

        //// Extract high part of sub (bits 254..508)
        //let mut sub_high_bits = Vec::new();
        //for i in 254..sub.len().min(508) {
        //    if let Some(bit) = sub.get(i) {
        //        sub_high_bits.push(bit);
        //    }
        //}
        //let sub_high = BigIntWires {
        //    bits: sub_high_bits,
        //};

        //let bound_check = bigint::greater_than(circuit, &sub_high, &x_high);

        //// Create modulus wires for conditional subtraction
        //let mut modulus_bits = Vec::new();
        //let modulus_biguint = Self::modulus_as_biguint();
        //let modulus_bitvec =
        //    bigint::bits_from_biguint_with_len(&modulus_biguint, Self::N_BITS).unwrap();
        //for i in 0..Self::N_BITS {
        //    let wire = circuit.issue_wire();
        //    circuit.add_gate(Gate::constant(wire, modulus_bitvec[i]));
        //    modulus_bits.push(wire);
        //}
        //let modulus_wires = BigIntWires { bits: modulus_bits };

        //let subtract_if_too_much = bigint::select(
        //    circuit,
        //    &modulus_wires,
        //    &BigIntWires::new(circuit, Self::N_BITS, false, false),
        //    bound_check,
        //);

        //let new_sub = bigint::sub_generic_without_borrow(circuit, &sub_high, &subtract_if_too_much);
        //bigint::sub_generic_without_borrow(circuit, &x_high, &new_sub)
    }

    /// Modular inverse using extended Euclidean algorithm
    fn inverse(_circuit: &mut Circuit, _a: &BigIntWires) -> BigIntWires {
        todo!()
        //assert_eq!(a.len(), Self::N_BITS);

        //let wires_1 = bigint::odd_part_generic(circuit, a);
        //let odd_part = wires_1[0..Self::N_BITS].to_vec();
        //let even_part = wires_1[Self::N_BITS..2 * Self::N_BITS].to_vec();

        //let neg_odd_part = Self::neg(circuit, &odd_part);
        //let mut u = Self::half(circuit, &neg_odd_part);
        //let mut v = odd_part;
        //let mut k = bigint::constant_wires(circuit, &BigUint::from(1u32), Self::N_BITS);
        //let mut r = bigint::constant_wires(circuit, &BigUint::from(1u32), Self::N_BITS);
        //let mut s = bigint::constant_wires(circuit, &BigUint::from(2u32), Self::N_BITS);

        //for _ in 0..2 * Self::N_BITS {
        //    let not_x1 = u.get(0).unwrap();
        //    let not_x2 = v.get(0).unwrap();
        //    let x3 = bigint::greater_than(circuit, &u, &v);

        //    let p2 = circuit.issue_wire();
        //    circuit.add_gate(Gate::and_variant(not_x1, not_x2, p2, [false, true, false]));

        //    let p3 = circuit.issue_wire();
        //    let wires_2 = circuit.issue_wire();
        //    circuit.add_gate(Gate::and(not_x1, not_x2, wires_2));
        //    circuit.add_gate(Gate::and(wires_2, x3, p3));

        //    let p4 = circuit.issue_wire();
        //    let not_x3 = circuit.issue_wire();
        //    circuit.add_gate(Gate::not(x3, not_x3));
        //    circuit.add_gate(Gate::and(wires_2, not_x3, p4));

        //    // part1
        //    let u1 = Self::half(circuit, &u);
        //    let v1 = v.clone();
        //    let r1 = r.clone();
        //    let s1 = Self::double(circuit, &s);
        //    let k1 = bigint::add_constant_generic(circuit, &k, &BigUint::from(1u32));

        //    // part2
        //    let u2 = u.clone();
        //    let v2 = Self::half(circuit, &v);
        //    let r2 = Self::double(circuit, &r);
        //    let s2 = s.clone();
        //    let k2 = bigint::add_constant_generic(circuit, &k, &BigUint::from(1u32));

        //    // part3
        //    let u3 = bigint::sub_generic(circuit, &u1, &v2);
        //    let v3 = v.clone();
        //    let r3 = Self::add(circuit, &r, &s);
        //    let s3 = Self::double(circuit, &s);
        //    let k3 = bigint::add_constant_generic(circuit, &k, &BigUint::from(1u32));

        //    // part4
        //    let u4 = u.clone();
        //    let v4 = bigint::sub_generic(circuit, &v2, &u1);
        //    let r4 = Self::double(circuit, &r);
        //    let s4 = Self::add(circuit, &r, &s);
        //    let k4 = bigint::add_constant_generic(circuit, &k, &BigUint::from(1u32));

        //    // calculate new u
        //    let wire_u_1 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &u1, not_x1);
        //    let wire_u_2 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &u2, p2);
        //    let wire_u_3 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &u3, p3);
        //    let wire_u_4 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &u4, p4);

        //    let add_u_1 = bigint::add_generic(circuit, &wire_u_1, &wire_u_2);
        //    let add_u_2 = bigint::add_generic(circuit, &add_u_1, &wire_u_3);
        //    let new_u = bigint::add_generic(circuit, &add_u_2, &wire_u_4);

        //    // calculate new v
        //    let wire_v_1 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &v1, not_x1);
        //    let wire_v_2 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &v2, p2);
        //    let wire_v_3 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &v3, p3);
        //    let wire_v_4 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &v4, p4);

        //    let add_v_1 = bigint::add_generic(circuit, &wire_v_1, &wire_v_2);
        //    let add_v_2 = bigint::add_generic(circuit, &add_v_1, &wire_v_3);
        //    let new_v = bigint::add_generic(circuit, &add_v_2, &wire_v_4);

        //    // calculate new r
        //    let wire_r_1 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &r1, not_x1);
        //    let wire_r_2 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &r2, p2);
        //    let wire_r_3 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &r3, p3);
        //    let wire_r_4 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &r4, p4);

        //    let add_r_1 = bigint::add_generic(circuit, &wire_r_1, &wire_r_2);
        //    let add_r_2 = bigint::add_generic(circuit, &add_r_1, &wire_r_3);
        //    let new_r = bigint::add_generic(circuit, &add_r_2, &wire_r_4);

        //    // calculate new s
        //    let wire_s_1 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &s1, not_x1);
        //    let wire_s_2 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &s2, p2);
        //    let wire_s_3 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &s3, p3);
        //    let wire_s_4 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &s4, p4);

        //    let add_s_1 = bigint::add_generic(circuit, &wire_s_1, &wire_s_2);
        //    let add_s_2 = bigint::add_generic(circuit, &add_s_1, &wire_s_3);
        //    let new_s = bigint::add_generic(circuit, &add_s_2, &wire_s_4);

        //    // calculate new k
        //    let wire_k_1 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &k1, not_x1);
        //    let wire_k_2 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &k2, p2);
        //    let wire_k_3 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &k3, p3);
        //    let wire_k_4 =
        //        bigint::select_generic(circuit, &bigint::zero_wires(Self::N_BITS), &k4, p4);

        //    let add_k_1 = bigint::add_generic(circuit, &wire_k_1, &wire_k_2);
        //    let add_k_2 = bigint::add_generic(circuit, &add_k_1, &wire_k_3);
        //    let new_k = bigint::add_generic(circuit, &add_k_2, &wire_k_4);

        //    // set new values
        //    let v_equals_one = bigint::equal_constant(circuit, &v, &BigUint::from(1u32));
        //    u = bigint::select(circuit, &u, &new_u, v_equals_one);
        //    v = bigint::select(circuit, &v, &new_v, v_equals_one);
        //    r = bigint::select(circuit, &r, &new_r, v_equals_one);
        //    s = bigint::select(circuit, &s, &new_s, v_equals_one);
        //    k = bigint::select(circuit, &k, &new_k, v_equals_one);
        //}

        //// divide result by even part
        //let mut even_part = even_part;
        //for _ in 0..Self::N_BITS {
        //    let updated_s = Self::half(circuit, &s);
        //    let updated_even_part = Self::half(circuit, &even_part);
        //    let selector = Self::equal_constant(circuit, &even_part, &ark_bn254::Fq::from(1u32));
        //    s = bigint::select(circuit, &s, &updated_s, selector);
        //    even_part = bigint::select(circuit, &even_part, &updated_even_part, selector);
        //}

        //// divide result by 2^k
        //for _ in 0..2 * Self::N_BITS {
        //    let updated_s = Self::half(circuit, &s);
        //    let updated_k = Self::add_constant(circuit, &k, &ark_bn254::Fq::from(-1i32));
        //    let selector = Self::equal_constant(circuit, &k, &ark_bn254::Fq::ZERO);
        //    s = bigint::select(circuit, &s, &updated_s, selector);
        //    k = bigint::select(circuit, &k, &updated_k, selector);
        //}

        //s
    }

    /// Modular inverse in Montgomery form
    fn inverse_montgomery(_circuit: &mut Circuit, _a: &BigIntWires) -> BigIntWires {
        todo!()
        //assert_eq!(a.len(), Self::N_BITS);

        //let b = Self::inverse(circuit, a);
        //let r_squared = Self::montgomery_r_as_biguint()
        //    * Self::montgomery_r_as_biguint()
        //    * Self::montgomery_r_as_biguint();
        //let constant = ark_bn254::Fq::from(r_squared % Self::modulus_as_biguint());

        //bigint::mul_by_constant_montgomery_generic(circuit, &b, &BigUint::from(constant))
    }

    /// Exponentiation by constant in Montgomery form
    fn exp_by_constant_montgomery(
        _circuit: &mut Circuit,
        _a: &BigIntWires,
        _exp: &BigUint,
    ) -> BigIntWires {
        todo!()
        //assert_eq!(a.len(), Self::N_BITS);

        //if exp.is_zero() {
        //    return bigint::constant_wires(circuit, &BigUint::from(1u32), Self::N_BITS);
        //}

        //if exp.is_one() {
        //    return a.to_vec();
        //}

        //let b_bits = bigint::bits_from_biguint(exp);
        //let len = b_bits.len();
        //let mut i = len - 1;
        //while !b_bits[i] {
        //    i -= 1;
        //}

        //let mut result = a.to_vec();
        //for b_bit in b_bits.iter().rev().skip(len - i) {
        //    let result_square = Self::square_montgomery(circuit, &result);
        //    if *b_bit {
        //        result = Self::mul_montgomery(circuit, a, &result_square);
        //    } else {
        //        result = result_square;
        //    }
        //}

        //result
    }
}
