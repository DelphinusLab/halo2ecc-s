use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigUint;
use std::marker::PhantomData;

use crate::utils::field_to_bn;

pub const COMMON_RANGE_BITS: usize = 18;
pub const W_CEIL_LEADING_CHUNKS: usize = 5;
pub const N_FLOOR_LEADING_CHUNKS: usize = 5;
pub const D_LEADING_CHUNKS: usize = 5;
pub const MAX_CHUNKS: usize = 5;

pub const OVERFLOW_BITS: usize = 5;

#[derive(Copy, Clone)]
pub enum RangeClass {
    WCeilLeading = 1,
    NFloorLeading = 2,
    DLeading = 3,
    Common = 4,
}

#[derive(Debug, Clone)]
pub struct RangeInfo<N: FieldExt> {
    pub d_leading_bits: usize,
    pub w_ceil_leading_bits: usize,
    pub n_floor_leading_bits: usize,

    pub common_range_mask: BigUint,
    pub _phantom: PhantomData<N>,
}

impl<N: FieldExt> RangeInfo<N> {
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

        Self {
            d_leading_bits,
            w_ceil_leading_bits,
            n_floor_leading_bits,
            common_range_mask: BigUint::from((1u64 << COMMON_RANGE_BITS) - 1),
            _phantom: PhantomData,
        }
    }
}
