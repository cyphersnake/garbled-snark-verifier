#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateType {
    And = 0,
    Nand = 1,
    Nimp = 2,
    Imp = 3, // a => b
    Ncimp = 4,
    Cimp = 5, // b => a
    Nor = 6,
    Or = 7,
    Xor,
    Xnor,
    Not,
}

impl GateType {
    pub const fn f(&self) -> fn(bool, bool) -> bool {
        match self {
            GateType::And => |a, b| a & b,
            GateType::Nand => |a, b| !(a & b),

            GateType::Nimp => |a, b| a & !b,
            GateType::Imp => |a, b| !a | b,

            GateType::Ncimp => |a, b| !a & b,
            GateType::Cimp => |a, b| !b | a,

            GateType::Nor => |a, b| !(a | b),
            GateType::Or => |a, b| a | b,

            GateType::Xor => |a, b| a ^ b,
            GateType::Xnor => |a, b| !(a ^ b),

            GateType::Not => |a, _| !a,
        }
    }

    pub fn is_free(&self) -> bool {
        matches!(self, Self::Xor | Self::Xnor | Self::Not)
    }

    pub fn is_output_wire_is_marked_not(&self) -> bool {
        match self {
            GateType::Not => true,
            GateType::Xnor => true,

            GateType::Nand => false,
            GateType::Nor => false,
            GateType::And => false,
            GateType::Cimp => false,
            GateType::Imp => false,
            GateType::Ncimp => false,
            GateType::Nimp => false,
            GateType::Or => false,
            GateType::Xor => false,
        }
    }

    /// Get 4-bit truth table for the gate (bit0=f(0,0), bit1=f(0,1), bit2=f(1,0), bit3=f(1,1))
    pub fn truth_table(&self) -> u8 {
        let f = self.f();
        let mut tt = 0u8;
        if f(false, false) {
            tt |= 1;
        } // bit 0
        if f(false, true) {
            tt |= 2;
        } // bit 1
        if f(true, false) {
            tt |= 4;
        } // bit 2
        if f(true, true) {
            tt |= 8;
        } // bit 3
        tt
    }

    /// Map 4-bit truth table to (alpha_a, alpha_b, alpha_c), odd-parity only
    pub fn alphas(&self) -> (bool, bool, bool) {
        let tt = self.truth_table();
        assert_eq!(tt.count_ones() % 2, 1, "Truth table must have odd parity");

        alphas(tt)
    }
}

const fn alphas(tt: u8) -> (bool, bool, bool) {
    let f00 = (tt & 1) != 0;
    let f01 = ((tt >> 1) & 1) != 0;
    let f10 = ((tt >> 2) & 1) != 0;

    let alpha_a = f01 ^ f00; // formula (2)
    let alpha_b = f10 ^ f00;
    let alpha_c = f00 ^ (alpha_a & alpha_b); // formula (2)

    (alpha_a, alpha_b, alpha_c)
}

#[cfg(test)]
mod tests {
    use super::*;
    /// Checks that alphas(tt) satisfies the exact formula (3) Half-Gates
    /// for all 2-input gates of odd parity (8 pieces out of 16).
    #[test]
    fn alphas_satisfy_equation_3_for_all_odd_parity_gates() {
        for tt in 0u8..16 {
            if tt.count_ones() & 1 == 0 {
                continue;
            }

            // calculate α-parameters with the function under the test
            let (alpha_a, alpha_b, alpha_c) = alphas(tt);

            // check equivalence (3) on each of the 4 sets of inputs (a,b)
            for (a, b) in [(false, false), (false, true), (true, false), (true, true)] {
                // source value from truth-table: bits are in the order 00 → 01 → 10 → 11
                let idx = (a as u8) << 1 | (b as u8);
                let f_ab = ((tt >> idx) & 1) != 0;

                // right side of formula (3)
                let g_ab = (a ^ alpha_a) & (b ^ alpha_b) ^ alpha_c;

                assert!(
                    f_ab == g_ab,
                    "Equation (3) failed for tt={:#06b}, inputs ({},{}) \
                 ⇒ expected {}, got {} (α= {:?})",
                    tt,
                    a as u8,
                    b as u8,
                    f_ab,
                    g_ab,
                    (alpha_a, alpha_b, alpha_c)
                );
            }
        }
    }

    #[test]
    fn test_truth_tables() {
        // AND: f(0,0)=0, f(0,1)=0, f(1,0)=0, f(1,1)=1 -> 0b1000 = 8
        assert_eq!(GateType::And.truth_table(), 8);

        // OR: f(0,0)=0, f(0,1)=1, f(1,0)=1, f(1,1)=1 -> 0b1110 = 14
        assert_eq!(GateType::Or.truth_table(), 14);

        // XOR: f(0,0)=0, f(0,1)=1, f(1,0)=1, f(1,1)=0 -> 0b0110 = 6
        assert_eq!(GateType::Xor.truth_table(), 6);

        // NAND: f(0,0)=1, f(0,1)=1, f(1,0)=1, f(1,1)=0 -> 0b0111 = 7
        assert_eq!(GateType::Nand.truth_table(), 7);
    }

    #[test]
    fn test_odd_parity_gates() {
        // Half-gates only work with odd-parity gates
        let odd_parity_gates = [
            GateType::And,
            GateType::Nand,
            GateType::Nimp,
            GateType::Imp,
            GateType::Ncimp,
            GateType::Cimp,
            GateType::Nor,
            GateType::Or,
        ];

        for gate in odd_parity_gates {
            let tt = gate.truth_table();
            assert_eq!(tt.count_ones() % 2, 1, "{gate:?} should have odd parity");
        }
    }
}
