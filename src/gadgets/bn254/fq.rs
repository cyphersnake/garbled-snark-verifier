use std::str::FromStr;

use ark_ff::{Field, PrimeField, UniformRand};
use bitvec::vec::BitVec;
use num_bigint::BigUint;

use super::super::{bigint::BigIntWires, bn254::fp254impl::Fp254Impl};
use crate::{
    core::wire,
    gadgets::{self, bigint},
    Circuit, WireId,
};

/// BN254 base field Fq implementation
pub struct Fq;

impl Fp254Impl for Fq {
    const MODULUS: &'static str =
        "21888242871839275222246405745257275088696311157297823662689037894645226208583";
    const MONTGOMERY_M_INVERSE: &'static str =
        "4759646384140481320982610724935209484903937857060724391493050186936685796471";
    const MONTGOMERY_R_INVERSE: &'static str =
        "18289368484950178621272022062020525048389989670507786348948026221581485535495";
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

impl Fq {
    /// Create new field element wires
    pub fn new_bn(circuit: &mut Circuit, is_input: bool, is_output: bool) -> BigIntWires {
        BigIntWires::new(circuit, Self::N_BITS, is_input, is_output)
    }

    pub fn get_wire_bits_fn(
        wires: &BigIntWires,
        value: &ark_bn254::Fq,
    ) -> Result<impl Fn(WireId) -> Option<bool> + use<>, gadgets::bigint::Error> {
        wires.get_wire_bits_fn(&BigUint::from(value.into_bigint()))
    }

    pub fn as_montgomery(a: ark_bn254::Fq) -> ark_bn254::Fq {
        a * ark_bn254::Fq::from(Self::montgomery_r_as_biguint())
    }

    pub fn from_montgomery(a: ark_bn254::Fq) -> ark_bn254::Fq {
        a / ark_bn254::Fq::from(Self::montgomery_r_as_biguint())
    }

    pub fn to_bits(u: ark_bn254::Fq) -> Vec<bool> {
        let mut bytes = BigUint::from(u).to_bytes_le();
        bytes.extend(vec![0_u8; 32 - bytes.len()]);
        let mut bits = Vec::new();
        for byte in bytes {
            for i in 0..8 {
                bits.push(((byte >> i) & 1) == 1)
            }
        }
        bits.pop();
        bits.pop();
        bits
    }

    pub fn from_bits(bits: Vec<bool>) -> ark_bn254::Fq {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit { one.clone() } else { zero.clone() };
        }
        ark_bn254::Fq::from(u)
    }

    pub fn wires(circuit: &mut Circuit) -> BigIntWires {
        BigIntWires::new(circuit, Self::N_BITS, false, false)
    }

    // Check if field element is quadratic non-residue in Montgomery form
    pub fn is_qnr_montgomery(circuit: &mut Circuit, x: BigIntWires) -> WireId {
        // y = x^((p - 1)/2)
        let y = Fq::exp_by_constant_montgomery(
            circuit,
            &x,
            &BigUint::from(ark_bn254::Fq::MODULUS_MINUS_ONE_DIV_TWO),
        );

        let neg_one_mont =
            BigIntWires::new_constant(circuit, Self::N_BITS, &BigUint::from(-ark_bn254::Fq::ONE))
                .unwrap();

        bigint::equal(circuit, &y, &neg_one_mont)
    }

    /// Square root in Montgomery form (assuming input is quadratic residue)
    pub fn sqrt_montgomery(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        Self::exp_by_constant_montgomery(
            circuit,
            a,
            &BigUint::from_str(Self::MODULUS_ADD_1_DIV_4).unwrap(),
        )
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::AdditiveGroup;
    use rand::Rng;

    use super::*;
    use crate::test_utils::trng;

    fn rnd() -> ark_bn254::Fq {
        ark_bn254::Fq::from(trng().random::<u128>())
    }

    #[test]
    fn test_fq_random() {
        let u = rnd();
        println!("u: {u:?}");
        let b = Fq::to_bits(u);
        let v = Fq::from_bits(b);
        println!("v: {v:?}");
        assert_eq!(u, v);
    }

    #[test]
    fn test_fq_add() {
        let mut circuit = Circuit::default();

        let a = Fq::new_bn(&mut circuit, true, false);
        let b = Fq::new_bn(&mut circuit, true, false);

        let c = Fq::add(&mut circuit, &a, &b);
        c.mark_as_output(&mut circuit);

        let a_v = rnd();
        let b_v = rnd();

        let a_input = Fq::get_wire_bits_fn(&a, &a_v).unwrap();
        let b_input = Fq::get_wire_bits_fn(&b, &b_v).unwrap();
        let c_output = Fq::get_wire_bits_fn(&c, &(a_v + b_v)).unwrap();

        circuit
            .simple_evaluate(|wire_id| (a_input)(wire_id).or((b_input)(wire_id)))
            .unwrap()
            .for_each(|(wire_id, value)| {
                assert_eq!((c_output)(wire_id), Some(value));
            });
    }

    //#[test]
    //fn test_fq_add_constant() {
    //    let a = Fq::random();
    //    let b = Fq::random();
    //    let circuit = Fq::add_constant(Fq::wires_set(a), b);
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, a + b);
    //}

    //#[test]
    //fn test_fq_neg() {
    //    let a = Fq::random();
    //    let circuit = Fq::neg(Fq::wires_set(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, -a);
    //}

    //#[test]
    //fn test_fq_sub() {
    //    let a = Fq::random();
    //    let b = Fq::random();
    //    let circuit = Fq::sub(Fq::wires_set(a), Fq::wires_set(b));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, a - b);
    //}

    //#[test]
    //fn test_fq_double() {
    //    let a = Fq::random();
    //    let circuit = Fq::double(Fq::wires_set(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, a + a);
    //}

    //#[test]
    //fn test_fq_half() {
    //    let a = Fq::random();
    //    let circuit = Fq::half(Fq::wires_set(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c + c, a);
    //}

    //#[test]
    //fn test_fq_triple() {
    //    let a = Fq::random();
    //    let circuit = Fq::triple(Fq::wires_set(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, a + a + a);
    //}

    //#[test]
    //fn test_fq_mul_montgomery() {
    //    let a = Fq::random();
    //    let b = Fq::random();
    //    let circuit = Fq::mul_montgomery(
    //        Fq::wires_set(Fq::as_montgomery(a)),
    //        Fq::wires_set(Fq::as_montgomery(b)),
    //    );
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, Fq::as_montgomery(a * b));
    //}

    //#[test]
    //fn test_fq_mul_by_constant_montgomery() {
    //    let a = Fq::random();
    //    let b = Fq::random();
    //    let c = ark_bn254::Fq::ONE;
    //    let d = ark_bn254::Fq::ZERO;

    //    let circuit =
    //        Fq::mul_by_constant_montgomery(Fq::wires_set_montgomery(a), Fq::as_montgomery(b));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let e = Fq::from_wires(circuit.0);
    //    assert_eq!(e, Fq::as_montgomery(a * b));

    //    let circuit =
    //        Fq::mul_by_constant_montgomery(Fq::wires_set_montgomery(a), Fq::as_montgomery(c));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let e = Fq::from_wires(circuit.0);
    //    assert_eq!(e, Fq::as_montgomery(a * c));

    //    let circuit =
    //        Fq::mul_by_constant_montgomery(Fq::wires_set_montgomery(a), Fq::as_montgomery(d));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let e = Fq::from_wires(circuit.0);
    //    assert_eq!(e, Fq::as_montgomery(a * d));
    //}

    //#[test]
    //fn test_fq_square_montgomery() {
    //    let a = Fq::random();
    //    let circuit = Fq::square_montgomery(Fq::wires_set_montgomery(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, Fq::as_montgomery(a * a));
    //}

    //#[test]
    //fn test_fq_inverse_montgomery() {
    //    let a = Fq::random();
    //    let circuit = Fq::inverse_montgomery(Fq::wires_set_montgomery(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c, Fq::as_montgomery(a.inverse().unwrap()));
    //}

    //#[test]
    //fn test_fq_div6() {
    //    let a = Fq::random();
    //    let circuit = Fq::div6(Fq::wires_set(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }

    //    let c = Fq::from_wires(circuit.0);
    //    assert_eq!(c + c + c + c + c + c, a);
    //}

    //#[test]
    //#[serial]
    //#[ignore]
    //fn test_fq_exp_by_constant_montgomery() {
    //    use ark_ff::PrimeField;
    //    let ut = |b: BigUint| {
    //        let a = Fq::random();
    //        let b = ark_bn254::Fq::from(b);
    //        let expect_a_to_power_of_b = a.pow(b.into_bigint());

    //        let circuit =
    //            Fq::exp_by_constant_montgomery(Fq::wires_set_montgomery(a), BigUint::from(b));
    //        circuit.gate_counts().print();
    //        for mut gate in circuit.1 {
    //            gate.evaluate();
    //        }
    //        let c = Fq::from_montgomery_wires(circuit.0);
    //        assert_eq!(expect_a_to_power_of_b, c);
    //    };
    //    ut(BigUint::from(0u8));
    //    ut(BigUint::from(1u8));
    //    ut(BigUint::from(u32::rand(&mut test_rng())));
    //    ut(BigUint::from_str(Fq::MODULUS_ADD_1_DIV_4).unwrap());
    //    ut(BigUint::from(ark_bn254::Fq::MODULUS_MINUS_ONE_DIV_TWO));
    //}

    //#[test]
    //#[serial]
    //fn test_fq_exp_by_constant_montgomery_evaluate() {
    //    use ark_ff::PrimeField;
    //    let ut = |b: BigUint| {
    //        let a = Fq::random();
    //        let b = ark_bn254::Fq::from(b);
    //        let expect_a_to_power_of_b = a.pow(b.into_bigint());

    //        let (c, gc) = Fq::exp_by_constant_montgomery_evaluate(
    //            Fq::wires_set_montgomery(a),
    //            BigUint::from(b),
    //        );
    //        gc.print();
    //        assert_eq!(expect_a_to_power_of_b, Fq::from_montgomery_wires(c));
    //    };
    //    ut(BigUint::from(0u8));
    //    ut(BigUint::from(1u8));
    //    ut(BigUint::from(u32::rand(&mut test_rng())));
    //    ut(BigUint::from_str(Fq::MODULUS_ADD_1_DIV_4).unwrap());
    //    ut(BigUint::from(ark_bn254::Fq::MODULUS_MINUS_ONE_DIV_TWO));
    //}

    //#[test]
    //fn test_fq_sqrt_montgomery() {
    //    let a = Fq::random();
    //    let aa = a * a;
    //    let circuit = Fq::sqrt_montgomery(Fq::wires_set_montgomery(aa));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let c = Fq::from_montgomery_wires(circuit.0);
    //    let la = match a.legendre().is_qnr() {
    //        true => -a,
    //        false => a,
    //    };
    //    assert_eq!(c, la);
    //}

    //#[test]
    //fn test_fq_is_qnr_montgomery() {
    //    use num_traits::One;
    //    let a = Fq::random();
    //    println!("{}", a.legendre().is_qnr());
    //    let circuit = Fq::is_qnr_montgomery(Fq::wires_set_montgomery(a));
    //    circuit.gate_counts().print();
    //    for mut gate in circuit.1 {
    //        gate.evaluate();
    //    }
    //    let is_qnr = Fq::from_montgomery_wires(circuit.0);
    //    assert_eq!(is_qnr.is_one(), a.legendre().is_qnr());
    //}
}
