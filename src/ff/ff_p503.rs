//! Finite field for SIKEp503
//!
//! Implementation of the finite field of order SIKE_P503_P used in SIKEp503

use crate::constants::cs_p503::SIKE_P503_P;
use crate::ff::FiniteField;

use hex;

use once_cell::sync::Lazy;

use std::fmt::Debug;

use rug::{integer::Order::MsfBe, Integer};

static P503_PRIME: Lazy<Integer> = Lazy::new(|| Integer::from_str_radix(SIKE_P503_P, 16).unwrap());

/// Finite field defined by the prime number SIKE_P503_P
#[derive(Clone, PartialEq)]
pub struct PrimeFieldP503 {
    val: Integer,
}

impl PrimeFieldP503 {
    /// Parse a string into and element of the finite field
    pub fn from_string(s: &str) -> Self {
        let val = Integer::from_str_radix(s, 16).unwrap();

        Self { val }
    }
}

impl Debug for PrimeFieldP503 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes = self.val.to_string_radix(16);
        write!(f, "{:?}", bytes)
    }
}

impl PrimeFieldP503 {
    #[inline]
    fn order() -> &'static Integer {
        &*P503_PRIME
    }
}

impl FiniteField for PrimeFieldP503 {
    #[inline]
    fn is_zero(&self) -> bool {
        self.val == Self::zero().val
    }

    #[inline]
    fn dimension() -> usize {
        1
    }

    #[inline]
    fn zero() -> Self {
        Self {
            val: Integer::new(),
        }
    }

    #[inline]
    fn one() -> Self {
        Self {
            val: Integer::from(1),
        }
    }

    #[inline]
    fn neg(&self) -> Self {
        Self {
            val: Integer::from(Self::order() - &self.val),
        }
    }

    #[inline]
    fn inv(&self) -> Self {
        Self {
            val: Integer::from(&self.val).invert(Self::order()).unwrap(),
        }
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        Self {
            val: Integer::from(&self.val + &other.val) % Self::order(),
        }
    }

    #[inline]
    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        Self {
            val: Integer::from(&self.val * &other.val) % Self::order(),
        }
    }

    #[inline]
    fn div(&self, other: &Self) -> Self {
        self.mul(&other.inv())
    }

    #[inline]
    fn equals(&self, other: &Self) -> bool {
        self.sub(&other).is_zero()
    }

    fn to_bytes(self) -> Vec<u8> {
        self.val.to_digits::<u8>(MsfBe)
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        let s = hex::encode(bytes);
        Self {
            val: Integer::from_str_radix(&s, 16).unwrap(),
        }
    }
}