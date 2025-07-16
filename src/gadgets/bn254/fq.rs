use std::str::FromStr;

use ark_ff::{Field, PrimeField};
use num_bigint::BigUint;

use super::super::{bigint::BigIntWires, bn254::fp254impl::Fp254Impl};
use crate::circuit::Circuit;

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
    pub fn new_wires(circuit: &mut Circuit, is_input: bool, is_output: bool) -> BigIntWires {
        BigIntWires::new(circuit, Self::N_BITS, is_input, is_output)
    }

    // Check if field element is quadratic non-residue in Montgomery form
    //        let mut circuit = Circuit::empty();
    //    // y = x^((p - 1)/2)
    //    let exp = BigUint::from(ark_bn254::Fq::MODULUS_MINUS_ONE_DIV_TWO);
    //    let y = circuit.extend(Fq::exp_by_constant_montgomery(x.clone(), exp));

    //    let neg_one = -ark_bn254::Fq::ONE;
    //    let neg_one_mont = Fq::wires_set_montgomery(neg_one);

    //    let is_qnr = circuit.extend(U254::equal(y, neg_one_mont));

    //    circuit.add_wires(is_qnr);
    //    circuit
    pub fn is_qnr_montgomery(circuit: &mut Circuit, x: &BigIntWires) -> BigIntWires {
        assert_eq!(x.len(), Self::N_BITS);

        //y = x^((p - 1)/2)
        let exp = BigUint::from(ark_bn254::Fq::MODULUS_MINUS_ONE_DIV_TWO);
        let _y = Fq::exp_by_constant_montgomery(circuit, x, &exp);

        let neg_one = -ark_bn254::Fq::ONE;
        let _neg_one_mont = Fq::wires_set_montgomery(neg_one);

        todo!()
    }

    pub fn wires_set_montgomery(_u: ark_bn254::Fq) -> BigIntWires {
        todo!()
    }

    /// Square root in Montgomery form (assuming input is quadratic residue)
    pub fn sqrt_montgomery(circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);

        // sqrt(a) = a^((p+1)/4) for p ≡ 3 (mod 4)
        let exp = BigUint::from_str(Self::MODULUS_ADD_1_DIV_4).unwrap();
        Self::exp_by_constant_montgomery(circuit, a, &exp)
    }

    /// Division by 6 in field
    pub fn div6(_circuit: &mut Circuit, a: &BigIntWires) -> BigIntWires {
        assert_eq!(a.len(), Self::N_BITS);
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fq_constants() {
        let modulus = Fq::modulus_as_biguint();
        assert_eq!(modulus.bits(), 254);

        // Verify Montgomery constants
        assert!(Fq::validate_montgomery_constants());
    }

    #[test]
    fn test_fq_modulus_properties() {
        let half = Fq::half_modulus();
        let one_third = Fq::one_third_modulus();

        let modulus = Fq::modulus_as_biguint();

        // For modulus division, we expect (half * 2) + 1 = modulus for odd modulus
        assert_eq!(half * 2u32 + 1u32, modulus);
        // For thirds, precision may be lost in integer division
        assert!(one_third.clone() * 3u32 <= modulus);
        assert!(one_third * 3u32 + 2u32 >= modulus);
    }

    #[test]
    fn test_new_wires() {
        assert_eq!(
            Fq::new_wires(&mut Circuit::default(), false, false).len(),
            254
        );
    }
}
