//! Finite field for SIKEp610
//!
//! Implementation of the finite field of order SIKE_P610_P used in SIKEp610
extern crate num_bigint_dig as num_bigint;
use crate::constants::cs_p610::SIKE_P610_P;
use crate::ff::FiniteField;
use hex;

use once_cell::sync::Lazy;

use std::fmt::Debug;

use num_bigint::traits::ModInverse;
use num_bigint::BigInt;
use num_traits::{Num, One, Zero};
//use rug::{integer::Order::MsfBe, Integer};

// Parsing a constant value, tests ensure no panic
static P610_PRIME: Lazy<BigInt> =
    Lazy::new(|| <BigInt as Num>::from_str_radix(SIKE_P610_P, 16).unwrap());

/// Finite field defined by the prime number SIKE_P610_P
#[derive(Clone, PartialEq)]
pub struct PrimeFieldP610 {
    val: BigInt,
}

impl PrimeFieldP610 {
    /// Parse a string into and element of the finite field
    pub fn from_string(s: &str) -> Result<Self, String> {
        <BigInt as Num>::from_str_radix(&s, 16)
            .or_else(|_| Err(String::from("Cannot parse from string")))
            .and_then(|val| Ok(Self { val }))
    }
}

impl Debug for PrimeFieldP610 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes = self.val.to_str_radix(16);
        write!(f, "{:?}", bytes)
    }
}

impl PrimeFieldP610 {
    #[inline]
    fn order() -> &'static BigInt {
        &*P610_PRIME
    }
}

impl FiniteField for PrimeFieldP610 {
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
        Self { val: Zero::zero() }
    }

    #[inline]
    fn one() -> Self {
        Self { val: One::one() }
    }

    #[inline]
    fn neg(&self) -> Self {
        let x: BigInt = Self::order() - &self.val;
        Self { val: x }
    }

    #[inline]
    fn inv(&self) -> Result<Self, String> {
        let x: BigInt = self.val.clone();
        match x.mod_inverse(Self::order()) {
            Some(inv_x) => Ok(Self { val: inv_x }),
            None => Err(String::from("Cannot invert")),
        }
    }

    #[inline]
    fn add(&self, other: &Self) -> Self {
        let x: BigInt = &self.val + &other.val;
        let x: BigInt = x % Self::order();

        Self { val: x }
    }

    #[inline]
    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    #[inline]
    fn mul(&self, other: &Self) -> Self {
        let x: BigInt = &self.val * &other.val;
        let x: BigInt = x % Self::order();

        Self { val: x }
    }

    #[inline]
    fn div(&self, other: &Self) -> Result<Self, String> {
        Ok(self.mul(&other.inv()?))
    }

    #[inline]
    fn equals(&self, other: &Self) -> bool {
        self.sub(&other).is_zero()
    }

    fn into_bytes(self) -> Vec<u8> {
        let (_sign, r) = self.val.to_bytes_be();
        r
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        let s = hex::encode(bytes);

        <BigInt as Num>::from_str_radix(&s, 16)
            .or_else(|_| Err(String::from("Cannot parse from bytes")))
            .and_then(|val| Ok(Self { val }))
    }
}
