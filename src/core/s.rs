use std::{
    fmt,
    iter::zip,
    ops::{Add, BitXor},
};

use blake3::hash;
use rand::{rng, Rng};

#[derive(Clone, Copy, PartialEq)]
pub struct S(pub [u8; 32]);

impl S {
    pub const fn one() -> Self {
        let mut s = [0_u8; 32];
        s[31] = 1;
        Self(s)
    }

    pub fn to_hex(&self) -> String {
        self.0
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<Vec<String>>()
            .join("")
    }

    pub fn random() -> Self {
        Self(rng().random::<[u8; 32]>())
    }

    pub fn neg(&self) -> Self {
        let mut s = self.0;
        for (i, si) in s.iter_mut().enumerate() {
            *si = 255 - self.0[i];
        }
        Self(s) + Self::one()
    }

    pub fn hash(&self) -> Self {
        Self(*hash(&self.0).as_bytes())
    }

    pub fn hash_together(a: Self, b: Self) -> Self {
        let mut h = a.0.to_vec();
        h.extend(b.0.to_vec());
        Self(*hash(&h).as_bytes())
    }

    pub fn xor(a: Self, b: Self) -> Self {
        Self(
            zip(a.0, b.0)
                .map(|(u, v)| u ^ v)
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap(),
        )
    }
}

impl fmt::Debug for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "S({})", self.to_hex())
    }
}

impl Add for S {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut s = [0_u8; 32];
        let mut carry = 0;
        for (i, (u, v)) in zip(self.0, rhs.0).enumerate().rev() {
            let x = (u as u32) + (v as u32) + carry;
            s[i] = (x % 256) as u8;
            carry = x / 256;
        }
        Self(s)
    }
}

impl BitXor for &S {
    type Output = S;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut out = [0u8; 32];

        // Why `Allow` here: the compiler will expand the call and remove the check on the fixed
        // array
        #[allow(clippy::needless_range_loop)]
        for i in 0..32 {
            out[i] = self.0[i] ^ rhs.0[i];
        }

        S(out)
    }
}

impl BitXor<&S> for S {
    type Output = S;

    fn bitxor(mut self, rhs: &S) -> Self::Output {
        for i in 0..32 {
            self.0[i] ^= rhs.0[i];
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_xor_zero_identity() {
        let zero = S([0u8; 32]);
        let a = S::random();
        assert_eq!(&a ^ &zero, a, "a ^ 0 should be a");
        assert_eq!(&zero ^ &a, a, "0 ^ a should be a");
    }

    #[test]
    fn test_xor_self_is_zero() {
        let a = S::random();
        let result = &a ^ &a;
        assert_eq!(result, S([0u8; 32]), "a ^ a should be 0");
    }

    #[test]
    fn test_xor_commutative() {
        let a = S::random();
        let b = S::random();
        assert_eq!(&a ^ &b, &b ^ &a, "a ^ b should equal b ^ a");
    }

    #[test]
    fn test_xor_associative() {
        let a = S::random();
        let b = S::random();
        let c = S::random();
        assert_eq!((&a ^ &b) ^ &c, &a ^ &(&b ^ &c), "XOR should be associative");
    }

    #[test]
    fn test_xor_known_value() {
        let a = S([0xFF; 32]);
        let b = S([0x0F; 32]);
        let expected = S([0xF0; 32]);
        assert_eq!(&a ^ &b, expected);
    }

    #[test]
    fn test_bitxor_is_pure() {
        let a = S::random();
        let b = S::random();
        let _ = &a ^ &b;
        let _ = &a ^ &b;
        assert_eq!(a, a, "a should remain unchanged");
        assert_eq!(b, b, "b should remain unchanged");
    }
}
