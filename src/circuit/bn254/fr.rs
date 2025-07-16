use num_bigint::BigUint;

use crate::circuit::{Circuit, bigint::BigIntWires, bn254::fp254impl::Fp254Impl};

/// BN254 scalar field Fr implementation  
pub struct Fr;

impl Fp254Impl for Fr {
    const MODULUS: &'static str =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    const MONTGOMERY_M_INVERSE: &'static str =
        "5441563794177615591428663161977496376097281981129373443346157590346630955009";
    const MONTGOMERY_R_INVERSE: &'static str =
        "17773755579518009376303681366703133516854333631346829854655645366227550102839";
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

impl Fr {
    /// Create new scalar field element wires
    pub fn new_wires(circuit: &mut Circuit, is_input: bool, is_output: bool) -> BigIntWires {
        BigIntWires::new(circuit, Self::N_BITS, is_input, is_output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fr_constants() {
        let modulus = Fr::modulus_as_biguint();
        assert_eq!(modulus.bits(), 254);

        // Verify Montgomery constants
        assert!(Fr::validate_montgomery_constants());
    }

    #[test]
    fn test_fr_modulus_properties() {
        let half = Fr::half_modulus();
        let one_third = Fr::one_third_modulus();

        let modulus = Fr::modulus_as_biguint();

        // For modulus division, we expect (half * 2) + 1 = modulus for odd modulus
        assert_eq!(half * 2u32 + 1u32, modulus);
        // For thirds, precision may be lost in integer division
        assert!(one_third.clone() * 3u32 <= modulus);
        assert!(one_third * 3u32 + 2u32 >= modulus);
    }

    #[test]
    fn test_new_wires() {
        let wires = Fr::new_wires(&mut Circuit::default(), false, false);
        assert_eq!(wires.len(), 254);
    }
}
