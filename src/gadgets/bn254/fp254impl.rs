use std::str::FromStr;

use ark_ff::AdditiveGroup;
use num_bigint::BigUint;
use num_traits::{One, Zero};

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

        let not_a = BigIntWires::new(circuit, a.len(), false, false);
        not_a.iter().zip(a.iter()).for_each(|(not_a, a_i)| {
            circuit.add_gate(Gate::nand(*a_i, *a_i, *not_a));
        });

        Self::add_constant(
            circuit,
            &not_a,
            &(ark_bn254::Fq::from(1) - ark_bn254::Fq::from(Self::not_modulus_as_biguint())),
        )
    }

    /// Field doubling: (2 * a) mod p
    fn double(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        let shift_wire = circuit.get_false_wire_constant();

        let mut shifted_a = a.clone();
        let u = shifted_a.pop().unwrap();
        shifted_a.insert(0, shift_wire);

        let mut wires_2 =
            bigint::add_constant_generic(circuit, &shifted_a, &Self::not_modulus_as_biguint());
        wires_2.pop();

        let v = bigint::less_than_constant(circuit, &shifted_a, &Self::modulus_as_biguint());

        let s = circuit.issue_wire();
        circuit.add_gate(Gate::and_variant(u, v, s, [true, false, false]));

        bigint::select(circuit, &shifted_a, &wires_2, s)
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
    fn mul_montgomery(circuit: &mut Circuit, a: &BigIntWires, b: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);

        let mul_result = bigint::mul_karatsuba_generic(circuit, a, b);
        Self::montgomery_reduce(circuit, &mul_result)
    }

    /// Montgomery squaring: (a * a * R^-1) mod p
    fn square_montgomery(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        Self::mul_montgomery(circuit, a, a)
    }

    /// Montgomery reduction: converts from Montgomery form to normal form
    fn montgomery_reduce(circuit: &mut Circuit, x: &BigIntWires) -> BigIntWires {
        assert_eq!(x.len(), 2 * Self::N_BITS);

        let (x_low, x_high) = x.clone().split_at(254);

        let q = bigint::mul_by_constant_modulo_power_two(
            circuit,
            &x_low,
            &Self::montgomery_m_inverse_as_biguint(),
            254,
        );

        let sub = bigint::mul_by_constant(circuit, &q, &Self::modulus_as_biguint())
            .split_at(254)
            .1
            .truncate(254);

        let bound_check = bigint::greater_than(circuit, &sub, &x_high);

        let modulus_as_biguint =
            BigIntWires::new_constant(circuit, x.len(), &Self::modulus_as_biguint()).unwrap();

        let subtract_if_too_much =
            bigint::self_or_zero_generic(circuit, &modulus_as_biguint, bound_check);

        let new_sub = bigint::sub_generic_without_borrow(circuit, &sub, &subtract_if_too_much);

        bigint::sub_generic_without_borrow(circuit, &x_high, &new_sub)
    }

    /// Modular inverse using extended Euclidean algorithm
    fn inverse(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        let wires_1 = circuit.extend(bigint::odd_part(a.clone()));
        let odd_part = wires_1[0..Self::N_BITS].to_vec();
        let mut even_part = wires_1[Self::N_BITS..2 * Self::N_BITS].to_vec();

        // initialize value for wires
        let neg_odd_part = circuit.extend(Self::neg(odd_part.clone()));
        let mut u = circuit.extend(U254::half(neg_odd_part));
        let mut v = odd_part;
        let mut k = Fq::wires_set(ark_bn254::Fq::ONE);
        let mut r = Fq::wires_set(ark_bn254::Fq::ONE);
        let mut s = Fq::wires_set(ark_bn254::Fq::from(2));

        for _ in 0..2 * Self::N_BITS {
            let not_x1 = u[0].clone();
            let not_x2 = v[0].clone();
            //let x1 = new_wirex();
            //let x2 = new_wirex();
            //circuit.add(Gate::not(x1x.clone(), x1.clone()));
            //circuit.add(Gate::not(x2x.clone(), x2.clone()));
            let x3 = circuit.extend(U254::greater_than(u.clone(), v.clone()))[0].clone();

            //let p1 = x1.clone();
            //let not_x1 = new_wirex();
            //circuit.add(Gate::not(x1.clone(), not_x1.clone()));
            let p2 = new_wirex();
            circuit.add(Gate::and_variant(
                not_x1.clone(),
                not_x2.clone(),
                p2.clone(),
                [0, 1, 0],
            ));
            let p3 = new_wirex();
            //let not_x2 = new_wirex();
            //circuit.add(Gate::not(x2, not_x2.clone()));
            let wires_2 = new_wirex();
            circuit.add(Gate::and(not_x1.clone(), not_x2.clone(), wires_2.clone()));
            circuit.add(Gate::and(wires_2.clone(), x3.clone(), p3.clone()));
            let p4 = new_wirex();
            let not_x3 = new_wirex();
            circuit.add(Gate::not(x3.clone(), not_x3.clone()));
            circuit.add(Gate::and(wires_2, not_x3, p4.clone()));

            //part1
            let u1 = circuit.extend(U254::half(u.clone()));
            let v1 = v.clone();
            let r1 = r.clone();
            let s1 = circuit.extend(U254::double_without_overflow(s.clone()));
            let k1 = circuit.extend(U254::add_constant_without_carry(
                k.clone(),
                &BigUint::from_str("1").unwrap(),
            ));

            // part2
            let u2 = u.clone();
            let v2 = circuit.extend(U254::half(v.clone()));
            let r2 = circuit.extend(U254::double_without_overflow(r.clone()));
            let s2 = s.clone();
            let k2 = circuit.extend(U254::add_constant_without_carry(
                k.clone(),
                &BigUint::from_str("1").unwrap(),
            ));

            // part3
            let u3 = circuit.extend(U254::sub_without_borrow(u1.clone(), v2.clone()));
            let v3 = v.clone();
            let r3 = circuit.extend(U254::add_without_carry(r.clone(), s.clone()));
            let s3 = circuit.extend(U254::double_without_overflow(s.clone()));
            let k3 = circuit.extend(U254::add_constant_without_carry(
                k.clone(),
                &BigUint::from_str("1").unwrap(),
            ));

            // part4
            let u4 = u.clone();
            let v4 = circuit.extend(U254::sub_without_borrow(v2.clone(), u1.clone()));
            let r4 = circuit.extend(U254::double_without_overflow(r.clone()));
            let s4 = circuit.extend(U254::add_without_carry(r.clone(), s.clone()));
            let k4 = circuit.extend(U254::add_constant_without_carry(
                k.clone(),
                &BigUint::from_str("1").unwrap(),
            ));

            // calculate new u
            let wire_u_1 = circuit.extend(U254::self_or_zero_inv(u1.clone(), not_x1.clone()));
            let wire_u_2 = circuit.extend(U254::self_or_zero(u2.clone(), p2.clone()));
            let wire_u_3 = circuit.extend(U254::self_or_zero(u3.clone(), p3.clone()));
            let wire_u_4 = circuit.extend(U254::self_or_zero(u4.clone(), p4.clone()));

            let add_u_1 = circuit.extend(U254::add_without_carry(wire_u_1, wire_u_2));
            let add_u_2 = circuit.extend(U254::add_without_carry(add_u_1, wire_u_3));
            let new_u = circuit.extend(U254::add_without_carry(add_u_2, wire_u_4));

            // calculate new v
            let wire_v_1 = circuit.extend(U254::self_or_zero_inv(v1.clone(), not_x1.clone()));
            let wire_v_2 = circuit.extend(U254::self_or_zero(v2.clone(), p2.clone()));
            let wire_v_3 = circuit.extend(U254::self_or_zero(v3.clone(), p3.clone()));
            let wire_v_4 = circuit.extend(U254::self_or_zero(v4.clone(), p4.clone()));

            let add_v_1 = circuit.extend(U254::add_without_carry(wire_v_1, wire_v_2));
            let add_v_2 = circuit.extend(U254::add_without_carry(add_v_1, wire_v_3));
            let new_v = circuit.extend(U254::add_without_carry(add_v_2, wire_v_4));

            // calculate new r
            let wire_r_1 = circuit.extend(U254::self_or_zero_inv(r1.clone(), not_x1.clone()));
            let wire_r_2 = circuit.extend(U254::self_or_zero(r2.clone(), p2.clone()));
            let wire_r_3 = circuit.extend(U254::self_or_zero(r3.clone(), p3.clone()));
            let wire_r_4 = circuit.extend(U254::self_or_zero(r4.clone(), p4.clone()));

            let add_r_1 = circuit.extend(U254::add_without_carry(wire_r_1, wire_r_2));
            let add_r_2 = circuit.extend(U254::add_without_carry(add_r_1, wire_r_3));
            let new_r = circuit.extend(U254::add_without_carry(add_r_2, wire_r_4));

            // calculate new s
            let wire_s_1 = circuit.extend(U254::self_or_zero_inv(s1.clone(), not_x1.clone()));
            let wire_s_2 = circuit.extend(U254::self_or_zero(s2.clone(), p2.clone()));
            let wire_s_3 = circuit.extend(U254::self_or_zero(s3.clone(), p3.clone()));
            let wire_s_4 = circuit.extend(U254::self_or_zero(s4.clone(), p4.clone()));

            let add_s_1 = circuit.extend(U254::add_without_carry(wire_s_1, wire_s_2));
            let add_s_2 = circuit.extend(U254::add_without_carry(add_s_1, wire_s_3));
            let new_s = circuit.extend(U254::add_without_carry(add_s_2, wire_s_4));

            // calculate new k
            let wire_k_1 = circuit.extend(U254::self_or_zero_inv(k1.clone(), not_x1.clone()));
            let wire_k_2 = circuit.extend(U254::self_or_zero(k2.clone(), p2.clone()));
            let wire_k_3 = circuit.extend(U254::self_or_zero(k3.clone(), p3.clone()));
            let wire_k_4 = circuit.extend(U254::self_or_zero(k4.clone(), p4.clone()));

            let add_k_1 = circuit.extend(U254::add_without_carry(wire_k_1, wire_k_2));
            let add_k_2 = circuit.extend(U254::add_without_carry(add_k_1, wire_k_3));
            let new_k = circuit.extend(U254::add_without_carry(add_k_2, wire_k_4));

            // set new values

            let v_equals_one = circuit.extend(U254::equal_constant(
                v.clone(),
                &BigUint::from_str("1").unwrap(),
            ))[0]
                .clone();
            u = circuit.extend(U254::select(u, new_u, v_equals_one.clone()));
            v = circuit.extend(U254::select(v.clone(), new_v, v_equals_one.clone()));
            r = circuit.extend(U254::select(r, new_r, v_equals_one.clone()));
            s = circuit.extend(U254::select(s.clone(), new_s, v_equals_one.clone()));
            k = circuit.extend(U254::select(k, new_k, v_equals_one.clone()));
        }

        // divide result by even part
        for _ in 0..Self::N_BITS {
            let updated_s = circuit.extend(Self::half(s.clone()));
            let updated_even_part = circuit.extend(Self::half(even_part.clone()));
            let selector = circuit
                .extend(Self::equal_constant(even_part.clone(), ark_bn254::Fq::ONE))[0]
                .clone();
            s = circuit.extend(U254::select(s.clone(), updated_s, selector.clone()));
            even_part =
                circuit.extend(U254::select(even_part, updated_even_part, selector.clone()));
        }

        // divide result by 2^k
        for _ in 0..2 * Self::N_BITS {
            let updated_s = circuit.extend(Self::half(s.clone()));
            let updated_k = circuit.extend(Self::add_constant(k.clone(), ark_bn254::Fq::from(-1)));
            let selector = circuit.extend(Self::equal_constant(k.clone(), ark_bn254::Fq::ZERO));
            s = circuit.extend(U254::select(s, updated_s, selector[0].clone()));
            k = circuit.extend(U254::select(k, updated_k, selector[0].clone()));
        }
        circuit.add_wires(s.clone());
        circuit
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
