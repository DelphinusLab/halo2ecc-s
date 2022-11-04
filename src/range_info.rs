use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigUint;
use num_integer::Integer;
use std::marker::PhantomData;

use crate::utils::{bn_to_field, field_to_bn};

pub const COMMON_RANGE_BITS: usize = 18;
pub const W_CEIL_LEADING_CHUNKS: usize = 5;
pub const N_FLOOR_LEADING_CHUNKS: usize = 5;
pub const D_LEADING_CHUNKS: usize = 5;
pub const MAX_CHUNKS: usize = 5;
pub const LIMBS: usize = 3;
pub const LIMB_BITS: usize = MAX_CHUNKS * COMMON_RANGE_BITS;

pub const OVERFLOW_BITS: usize = 5;
pub const OVERFLOW_LIMIT: usize = 1 << OVERFLOW_BITS;
pub const OVERFLOW_THRESHOLD: usize = 1 << (OVERFLOW_BITS - 1);

#[derive(Copy, Clone)]
pub enum RangeClass {
    WCeilLeading = 1,
    NFloorLeading = 2,
    DLeading = 3,
    Common = 4,
}

#[derive(Debug, Clone)]
pub struct RangeInfo<N: FieldExt> {
    pub w_ceil_bits: usize,

    pub d_leading_bits: usize,
    pub w_ceil_leading_bits: usize,
    pub n_floor_leading_bits: usize,

    pub w_ceil_modulus: BigUint,
    pub n_modulus: BigUint,
    pub w_modulus: BigUint,
    pub common_range_mask: BigUint,
    pub limb_mask: BigUint,
    pub limb_modulus: BigUint,

    pub w_modulus_limbs_le: [N; LIMBS],
    pub limb_coeffs: [N; LIMBS],

    pub w_native: N,

    pub _phantom: PhantomData<N>,
}

impl<N: FieldExt> RangeInfo<N> {
    pub fn pre_check(&self) {
        // for pure_w_check, lcm(limb, native) >= w_ceil
        let limb_modulus = &self.limb_modulus;
        let lcm = self.n_modulus.lcm(&limb_modulus);
        assert!(lcm >= self.w_ceil_modulus);
    }

    pub fn d_bits<W: FieldExt>() -> usize {
        // a * b = w * d + rem

        // -- a <= w_ceil_bits + overflow_bits /\ b <= w_ceil_bits + overflow_bits
        // -> a * b <= w_ceil_bits * 2 + overflow_bits * 2 - 1

        // -- w * d + rem >= a * b
        // <- d_bits + w_ceil_bits - 2 = w_ceil_bits * 2 + overflow_bits * 2 - 1

        let w_max = field_to_bn(&-W::one());
        let w_ceil_bits = w_max.bits() as usize;
        let d_bits = w_ceil_bits + OVERFLOW_BITS * 2 + 1;
        assert!(d_bits + w_ceil_bits - 2 >= w_ceil_bits * 2 + OVERFLOW_BITS * 2 - 1);
        d_bits
    }

    pub fn new<W: FieldExt>() -> Self {
        let w_max = field_to_bn(&-W::one());
        let w_ceil_bits = w_max.bits() as usize;
        assert!(BigUint::from(1u64) << w_ceil_bits > w_max);
        assert!(BigUint::from(1u64) << (w_ceil_bits - 1) < w_max);
        let w_ceil_leading_bits = w_ceil_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            w_ceil_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            W_CEIL_LEADING_CHUNKS - 1
        );
        assert!(w_ceil_leading_bits != 0);

        let n_max = field_to_bn(&-N::one());
        let n_floor_bits = n_max.bits() as usize - 1;
        assert!(BigUint::from(1u64) << n_floor_bits < n_max);
        assert!(BigUint::from(1u64) << (n_floor_bits + 1) >= n_max);
        let n_floor_leading_bits = n_floor_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            n_floor_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            N_FLOOR_LEADING_CHUNKS - 1
        );
        assert!(n_floor_leading_bits != 0);

        let d_range_bits = Self::d_bits::<W>();
        let d_leading_bits = d_range_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            d_range_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            D_LEADING_CHUNKS - 1
        );
        assert!(d_leading_bits != 0);

        let limb_mask = (BigUint::from(1u64) << LIMB_BITS) - 1u64;
        let n_modulus = &n_max + 1u64;
        let w_modulus = &w_max + 1u64;
        let w_native = &w_modulus % &n_modulus;
        let w_modulus_limbs_le = (0..LIMBS)
            .into_iter()
            .map(|i| bn_to_field(&((&w_modulus >> (i * LIMB_BITS)) & &limb_mask)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let res = Self {
            w_ceil_bits,
            d_leading_bits,
            w_ceil_leading_bits,
            n_floor_leading_bits,

            w_ceil_modulus: BigUint::from(1u64) << w_ceil_bits,
            n_modulus,
            w_modulus,
            common_range_mask: BigUint::from((1u64 << COMMON_RANGE_BITS) - 1),
            limb_mask,
            limb_modulus: (BigUint::from(1u64) << LIMB_BITS),
            limb_coeffs: (0..LIMBS)
                .into_iter()
                .map(|i| bn_to_field(&(BigUint::from(1u64) << (i * LIMB_BITS))))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),

            w_modulus_limbs_le,
            w_native: bn_to_field::<N>(&w_native),

            _phantom: PhantomData,
        };

        res.pre_check();
        res
    }

    pub fn w_to_limb_n_le(&self, w: &BigUint) -> [N; LIMBS] {
        (0..LIMBS)
            .into_iter()
            .map(|i| bn_to_field(&((w >> (i * LIMB_BITS)) & &self.limb_mask)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn find_w_modulus_ceil(&self, times: usize) -> [N; LIMBS] {
        let max = (times + 1) * (BigUint::from(1u64) << self.w_ceil_bits);
        let (n, rem) = max.div_rem(&self.w_modulus);
        let n = if rem.gt(&BigUint::from(0u64)) {
            n + 1u64
        } else {
            n
        };

        let mut upper = n * &self.w_modulus;

        let mut limbs = vec![];
        for _ in 0..LIMBS - 1 {
            let rem = (&upper & &self.limb_mask) + times * &self.limb_modulus;
            upper = (upper - &rem) >> LIMB_BITS;
            limbs.push(bn_to_field::<N>(&rem));
        }
        limbs.push(bn_to_field::<N>(&upper));
        limbs.try_into().unwrap()
    }
}
