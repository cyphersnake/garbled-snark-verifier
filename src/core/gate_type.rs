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
    pub fn f(&self) -> fn(bool, bool) -> bool {
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
}
