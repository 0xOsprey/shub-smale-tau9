//! Exact integer polynomials.
//!
//! Representation (canonical, so that derived `==` is exact value equality):
//!   * `Poly::S(v)`: coefficient vector (ascending degree, no trailing zero) of i128, used iff
//!     every coefficient fits in i128.
//!   * `Poly::B(v)`: same with `BigInt`, used iff at least one coefficient does NOT fit in i128.
//! All arithmetic is done with *checked* i128 operations; on any overflow the operation is
//! redone from scratch in BigInt and the result is normalised again.  There is no silent wrap.

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Poly {
    S(Vec<i128>),
    B(Vec<BigInt>),
}

#[inline]
pub fn mix(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xbf58476d1ce4e5b9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94d049bb133111eb);
    x ^= x >> 31;
    x
}

fn trim_i(v: &mut Vec<i128>) {
    while let Some(&0) = v.last() {
        v.pop();
    }
}

fn s_addsub(a: &[i128], b: &[i128], sub: bool) -> Option<Vec<i128>> {
    let n = a.len().max(b.len());
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        let x = if i < a.len() { a[i] } else { 0 };
        let y = if i < b.len() { b[i] } else { 0 };
        r.push(if sub { x.checked_sub(y)? } else { x.checked_add(y)? });
    }
    trim_i(&mut r);
    Some(r)
}

fn s_mul(a: &[i128], b: &[i128]) -> Option<Vec<i128>> {
    if a.is_empty() || b.is_empty() {
        return Some(vec![]);
    }
    let mut r = vec![0i128; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            if y == 0 {
                continue;
            }
            let t = x.checked_mul(y)?;
            r[i + j] = r[i + j].checked_add(t)?;
        }
    }
    trim_i(&mut r);
    Some(r)
}

impl Poly {
    pub fn zero() -> Poly {
        Poly::S(vec![])
    }
    pub fn one() -> Poly {
        Poly::S(vec![1])
    }
    pub fn x() -> Poly {
        Poly::S(vec![0, 1])
    }
    pub fn from_i128s(mut v: Vec<i128>) -> Poly {
        trim_i(&mut v);
        Poly::S(v)
    }
    pub fn from_bigs(mut v: Vec<BigInt>) -> Poly {
        while let Some(l) = v.last() {
            if l.is_zero() {
                v.pop();
            } else {
                break;
            }
        }
        let small: Option<Vec<i128>> = v.iter().map(|c| c.to_i128()).collect();
        match small {
            Some(s) => Poly::S(s),
            None => Poly::B(v),
        }
    }
    pub fn is_zero(&self) -> bool {
        match self {
            Poly::S(v) => v.is_empty(),
            Poly::B(v) => v.is_empty(),
        }
    }
    pub fn len(&self) -> usize {
        match self {
            Poly::S(v) => v.len(),
            Poly::B(v) => v.len(),
        }
    }
    pub fn degree(&self) -> Option<usize> {
        if self.is_zero() {
            None
        } else {
            Some(self.len() - 1)
        }
    }
    /// sign of the leading coefficient (0 for the zero polynomial)
    pub fn lc_sign(&self) -> i32 {
        match self {
            Poly::S(v) => v.last().map_or(0, |c| if *c > 0 { 1 } else { -1 }),
            Poly::B(v) => v.last().map_or(0, |c| if c.is_positive() { 1 } else { -1 }),
        }
    }
    pub fn to_bigs(&self) -> Vec<BigInt> {
        match self {
            Poly::S(v) => v.iter().map(|&c| BigInt::from(c)).collect(),
            Poly::B(v) => v.clone(),
        }
    }
    pub fn coeff_strings(&self) -> Vec<String> {
        match self {
            Poly::S(v) => v.iter().map(|c| c.to_string()).collect(),
            Poly::B(v) => v.iter().map(|c| c.to_string()).collect(),
        }
    }
    pub fn coeff_line(&self) -> String {
        if self.is_zero() {
            "0".to_string()
        } else {
            self.coeff_strings().join(" ")
        }
    }
    pub fn neg(&self) -> Poly {
        if let Poly::S(v) = self {
            let r: Option<Vec<i128>> = v.iter().map(|c| c.checked_neg()).collect();
            if let Some(r) = r {
                return Poly::S(r);
            }
        }
        Poly::from_bigs(self.to_bigs().into_iter().map(|c| -c).collect())
    }
    fn addsub(&self, o: &Poly, sub: bool) -> Poly {
        if let (Poly::S(a), Poly::S(b)) = (self, o) {
            if let Some(r) = s_addsub(a, b, sub) {
                return Poly::S(r);
            }
        }
        let a = self.to_bigs();
        let b = o.to_bigs();
        let n = a.len().max(b.len());
        let zero = BigInt::zero();
        let mut r = Vec::with_capacity(n);
        for i in 0..n {
            let x = a.get(i).unwrap_or(&zero);
            let y = b.get(i).unwrap_or(&zero);
            r.push(if sub { x - y } else { x + y });
        }
        Poly::from_bigs(r)
    }
    pub fn add(&self, o: &Poly) -> Poly {
        self.addsub(o, false)
    }
    pub fn sub(&self, o: &Poly) -> Poly {
        self.addsub(o, true)
    }
    pub fn mul(&self, o: &Poly) -> Poly {
        if let (Poly::S(a), Poly::S(b)) = (self, o) {
            if let Some(r) = s_mul(a, b) {
                return Poly::S(r);
            }
        }
        let a = self.to_bigs();
        let b = o.to_bigs();
        if a.is_empty() || b.is_empty() {
            return Poly::zero();
        }
        let mut r = vec![BigInt::zero(); a.len() + b.len() - 1];
        for (i, x) in a.iter().enumerate() {
            if x.is_zero() {
                continue;
            }
            for (j, y) in b.iter().enumerate() {
                if y.is_zero() {
                    continue;
                }
                r[i + j] += x * y;
            }
        }
        Poly::from_bigs(r)
    }
    /// Canonical representative of the class {f,-f}: the one with positive leading coefficient.
    /// Returns (rep, whether rep == -self).
    pub fn canon(&self) -> (Poly, bool) {
        if self.lc_sign() < 0 {
            (self.neg(), true)
        } else {
            (self.clone(), false)
        }
    }
    /// 64-bit hash of this polynomial (`neg`=true: hash of -self, computed without allocating
    /// where possible).  Used ONLY for table indexing / bucketing; identity is always exact.
    pub fn hash_with(&self, neg: bool) -> u64 {
        match self {
            Poly::S(v) => {
                if neg && v.iter().any(|&c| c == i128::MIN) {
                    return self.neg().hash_with(false);
                }
                let mut h = mix(v.len() as u64 ^ 0x1234_5678_9abc_def1);
                for &c in v {
                    let c = if neg { -c } else { c };
                    h = mix(h ^ (c as u64));
                    h = mix(h.wrapping_add((c >> 64) as u64));
                }
                h
            }
            Poly::B(v) => {
                if neg {
                    return self.neg().hash_with(false);
                }
                let mut h = mix(v.len() as u64 ^ 0xfedc_ba98_7654_3211);
                for c in v {
                    let bytes = c.to_signed_bytes_le();
                    h = mix(h ^ bytes.len() as u64);
                    for ch in bytes.chunks(8) {
                        let mut w = [0u8; 8];
                        w[..ch.len()].copy_from_slice(ch);
                        h = mix(h ^ u64::from_le_bytes(w));
                    }
                }
                h
            }
        }
    }
    #[inline]
    pub fn phash(&self) -> u64 {
        self.hash_with(false)
    }
    /// hash of the canonical representative of {self,-self}
    #[inline]
    pub fn class_hash(&self) -> u64 {
        self.hash_with(self.lc_sign() < 0)
    }
}

/// Poly with cached hash, for hash maps (Hash writes the cached value; Eq is exact).
#[derive(Clone)]
pub struct HP {
    pub h: u64,
    pub p: Poly,
}
impl PartialEq for HP {
    fn eq(&self, o: &HP) -> bool {
        self.h == o.h && self.p == o.p
    }
}
impl Eq for HP {}
impl std::hash::Hash for HP {
    fn hash<H: std::hash::Hasher>(&self, s: &mut H) {
        s.write_u64(self.h)
    }
}
#[derive(Default)]
pub struct IdH(u64);
impl std::hash::Hasher for IdH {
    fn write(&mut self, _: &[u8]) {
        unreachable!()
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = x
    }
    fn finish(&self) -> u64 {
        self.0
    }
}
pub type IdBuild = std::hash::BuildHasherDefault<IdH>;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn overflow_fallback_and_renormalise() {
        let two = Poly::from_i128s(vec![2]);
        let mut p = two.clone();
        for _ in 0..7 {
            p = p.mul(&p);
        } // 2^128
        assert!(matches!(p, Poly::B(_)));
        assert_eq!(p.coeff_line(), "340282366920938463463374607431768211456");
        let q = p.sub(&p);
        assert!(q.is_zero());
        // 2^128 - (2^128 - 1) == 1 must come back as S([1])
        let big_minus = p.sub(&Poly::one());
        assert!(matches!(big_minus, Poly::B(_)));
        assert_eq!(p.sub(&big_minus), Poly::one());
    }
    #[test]
    fn binomial_256() {
        // (x+1)^256 has middle coefficient C(256,128) > i128::MAX
        let mut p = Poly::from_i128s(vec![1, 1]);
        for _ in 0..8 {
            p = p.mul(&p);
        }
        assert_eq!(p.degree(), Some(256));
        let mut c = BigInt::from(1);
        for i in 0..128u32 {
            c = c * BigInt::from(256 - i) / BigInt::from(i + 1);
        }
        assert_eq!(p.to_bigs()[128], c);
        assert!(matches!(p, Poly::B(_)));
    }
    #[test]
    fn neg_min() {
        let p = Poly::from_i128s(vec![i128::MIN]);
        let n = p.neg();
        assert!(matches!(n, Poly::B(_)));
        assert_eq!(n.neg(), p);
        assert_eq!(p.hash_with(true), n.hash_with(false));
        assert_eq!(n.hash_with(true), p.hash_with(false));
        assert_eq!(p.class_hash(), n.class_hash());
    }
    #[test]
    fn class_hash_consistent() {
        let p = Poly::from_i128s(vec![3, -5, -2]);
        assert_eq!(p.class_hash(), p.neg().class_hash());
        assert_eq!(p.canon().0, p.neg().canon().0);
    }
}
