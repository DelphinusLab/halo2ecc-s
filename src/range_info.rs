use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigUint;
use num_integer::Integer;
use std::marker::PhantomData;

use crate::circuit::range_chip::COMMON_RANGE_BITS;
use crate::circuit::range_chip::RANGE_VALUE_DECOMPOSE;
use crate::context::OVERFLOW_BITS;
use crate::utils::bn_to_field;
use crate::utils::field_to_bn;

#[derive(Debug, Clone)]
pub struct RangeInfo<W: BaseExt, N: FieldExt> {
    pub limbs: u64,
    pub limb_bits: u64,

    pub w_ceil_leading_decompose: u64,
    pub n_floor_leading_decompose: u64,
    pub d_leading_decompose: u64,

    pub w_ceil_bits: u64,
    pub d_bits: u64,
    pub n_floor_bits: u64,

    pub d_leading_bits: u64,
    pub w_ceil_leading_bits: u64,
    pub n_floor_leading_bits: u64,

    pub w_ceil: BigUint,
    pub n_modulus: BigUint,
    pub w_modulus: BigUint,
    pub common_range_mask: BigUint,
    pub limb_mask: BigUint,
    pub limb_modulus: BigUint,
    pub max_d: BigUint,

    pub w_modulus_limbs_le_bn: Vec<BigUint>,
    pub w_modulus_limbs_le: Vec<N>,
    pub limb_coeffs: Vec<N>,
    pub limb_modulus_n: N,

    pub overflow_bits: u64,
    pub overflow_limit: u64,

    pub w_native: N,

    pub pure_w_check_limbs: u64,
    pub reduce_check_limbs: u64,
    pub mul_check_limbs: u64,
    pub w_modulus_of_ceil_times: Vec<Option<Vec<N>>>,

    pub _phantom: PhantomData<W>,
}

impl<W: BaseExt, N: FieldExt> RangeInfo<W, N> {
    fn bits_to_leading_bits_and_decompose(bits: u64, common_bits: u64) -> (u64, u64) {
        let common_limb_bits = RANGE_VALUE_DECOMPOSE * common_bits;
        let leading_bits = if bits % common_limb_bits == 0 {
            common_limb_bits
        } else {
            bits % common_limb_bits
        };

        // Ensure leading chunk can be placed in 2-line or 3-line range.
        assert!(leading_bits >= 2 * common_bits);
        assert!(leading_bits <= RANGE_VALUE_DECOMPOSE * common_bits);

        let leading_chunk_bits = leading_bits % common_bits;
        if leading_chunk_bits == 0 {
            (common_bits, leading_bits / common_bits)
        } else {
            (leading_chunk_bits, leading_bits / common_bits + 1)
        }
    }

    pub fn new(common_bits: u64, overflow_bits: u64) -> Self {
        // Add assert to make it easy to review.
        assert_eq!(common_bits, COMMON_RANGE_BITS);
        assert_eq!(overflow_bits, OVERFLOW_BITS);

        let w_max = field_to_bn(&-W::one());
        let w_ceil_bits = w_max.bits();
        assert!(BigUint::from(1u64) << w_ceil_bits > w_max);
        assert!(BigUint::from(1u64) << (w_ceil_bits - 1) <= w_max);
        let (w_ceil_leading_bits, w_ceil_leading_decompose) =
            Self::bits_to_leading_bits_and_decompose(w_ceil_bits, common_bits);

        let n_max = field_to_bn(&-N::one());
        let n_floor_bits = n_max.bits() - 1;
        assert!(BigUint::from(1u64) << n_floor_bits < n_max);
        assert!(BigUint::from(1u64) << (n_floor_bits + 1) >= n_max);
        let (n_floor_leading_bits, n_floor_leading_decompose) =
            Self::bits_to_leading_bits_and_decompose(n_floor_bits, common_bits);

        let d_bits = Self::d_bits(overflow_bits);
        let (d_leading_bits, d_leading_decompose) =
            Self::bits_to_leading_bits_and_decompose(d_bits, common_bits);

        let limb_bits = common_bits * RANGE_VALUE_DECOMPOSE;
        let limbs = (w_ceil_bits + limb_bits - 1) / limb_bits;

        let max_d = BigUint::from(1u64) << d_bits;
        let limb_mask = (BigUint::from(1u64) << limb_bits) - 1u64;
        let n_modulus = &n_max + 1u64;
        let w_modulus = &w_max + 1u64;
        let w_native = &w_modulus % &n_modulus;

        let w_modulus_limbs_le_bn = (0..limbs)
            .into_iter()
            .map(|i| ((&w_modulus >> (i * limb_bits)) & &limb_mask))
            .collect::<Vec<_>>();
        let w_modulus_limbs_le = w_modulus_limbs_le_bn
            .iter()
            .map(|x| bn_to_field(x))
            .collect::<Vec<_>>();

        let limb_modulus = BigUint::from(1u64) << limb_bits;
        let limb_modulus_n = bn_to_field(&limb_modulus);

        let overflow_limit = 1u64 << overflow_bits;
        let w_modulus_of_ceil_times = vec![None; overflow_limit as usize];

        let mut res = Self {
            d_bits,
            w_ceil_bits,
            n_floor_bits,

            d_leading_bits,
            w_ceil_leading_bits,
            n_floor_leading_bits,

            max_d,
            w_ceil: BigUint::from(1u64) << w_ceil_bits,
            n_modulus,
            w_modulus,
            common_range_mask: BigUint::from((1u64 << common_bits) - 1),
            limb_mask,
            limb_modulus,
            limb_coeffs: (0..limbs)
                .into_iter()
                .map(|i| bn_to_field(&(BigUint::from(1u64) << (i * limb_bits))))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),

            limb_modulus_n,
            w_modulus_limbs_le,
            w_modulus_limbs_le_bn,

            w_native: bn_to_field::<N>(&w_native),

            limbs,
            limb_bits,
            w_ceil_leading_decompose,
            n_floor_leading_decompose,
            d_leading_decompose,

            overflow_bits,
            overflow_limit,

            pure_w_check_limbs: (w_ceil_bits - n_floor_bits + limb_bits - 1) / limb_bits,
            mul_check_limbs: ((w_ceil_bits * 2 + overflow_bits * 2).max(d_bits + w_ceil_bits)
                - n_floor_bits
                + limb_bits
                - 1)
                / limb_bits,
            reduce_check_limbs: ((w_ceil_bits + overflow_bits).max(common_bits + w_ceil_bits)
                - n_floor_bits
                + limb_bits
                - 1)
                / limb_bits,
            w_modulus_of_ceil_times,

            _phantom: PhantomData,
        };

        for i in 1..overflow_limit {
            res.w_modulus_of_ceil_times[i as usize] = Some(res.find_w_modulus_of_ceil_times(i));
        }

        res.pre_check();
        res
    }

    fn pre_check(&self) {
        let common_modulus = 1u64 << COMMON_RANGE_BITS;

        {
            // is_pure_w_modulus():
            // lcm(limb, native) >= w_ceil
            let limb_check_modulus =
                BigUint::from(1u64) << (self.limb_bits * self.pure_w_check_limbs);
            let lcm = self.n_modulus.lcm(&limb_check_modulus);
            assert!(lcm >= self.w_ceil);
        }

        {
            // reduce():
            // a = d * w + rem
            let max_a = &self.w_ceil * (self.overflow_limit - 1) - 1u64;
            let max_d = (BigUint::from(1u64) << COMMON_RANGE_BITS) - 1u64;
            // For completeness of d
            // max(a) <= max(d) * w + min(rem)
            assert!(max_a <= &max_d * &self.w_modulus);
            // For soundness of d
            // lcm(limb ^ reduce_check_limbs, native) >= max(d) * w + max(rem)
            let limb_modulus = BigUint::from(1u64) << (self.limb_bits * self.reduce_check_limbs);
            let lcm = self.n_modulus.lcm(&limb_modulus);
            assert!(lcm >= &max_d * &self.w_modulus + &self.w_ceil);
            // In each limb_modulus check:
            // v * limb_modulus =
            //   d * w[i] + rem[i] - a[i] + last_v + overflow_limit * limb_modulus - borrowed[i]
            // For completeness of v
            // max(v) * limb_modulus >= max_d * max(w[i]) + max(rem[i]) + max(v) + overflow_limit * limb_modulus
            let max_v = &self.limb_modulus - 1u64;
            let max_wi = self
                .w_modulus_limbs_le_bn
                .iter()
                .reduce(|acc, x| acc.max(x))
                .unwrap();
            let max_rem = &self.limb_modulus - 1u64;
            assert!(
                &max_v * &self.limb_modulus
                    >= &max_d * max_wi
                        + &max_rem
                        + &max_v
                        + &self.overflow_limit * &self.limb_modulus
            );
            // Ensure no overflow
            // max(v) * limb_modulus < n_modulus
            // max_d * max(w[i]) + max(v) + overflow_limit * limb_modulus < n_modulus
            // overflow_limit * limb_modulus - overflow_limit >= max(a[i])
            assert!(&max_v * &self.limb_modulus < self.n_modulus);
            assert!(
                &max_d * max_wi + &max_rem + &max_v + &self.overflow_limit * &self.limb_modulus
                    < self.n_modulus
            );
            let max_ai = &self.limb_modulus * (self.overflow_limit - 1) - 1u64;
            assert!(&self.overflow_limit * &self.limb_modulus - &self.overflow_limit >= max_ai)
        }

        {
            // mul():
            // a * b = d * w + rem
            let max_a = &self.w_ceil * (self.overflow_limit - 1) - 1u64;
            let max_b = &max_a;
            let max_d = (BigUint::from(1u64) << self.d_bits) - 1u64;
            // For completeness of d
            // max(a) * max(b) <= max(d) * w + min(rem)
            assert!(&max_a * max_b <= &max_d * &self.w_modulus);
            // For soundness of d
            // lcm(limb_modulus ^ mul_check_limbs, native) >= max(d) * w + max(rem)
            let lcm = self
                .n_modulus
                .lcm(&(BigUint::from(1u64) << (self.limb_bits * self.mul_check_limbs)));
            let max_rem = &self.w_ceil - 1u64;
            assert!(lcm > &max_a * max_b);
            assert!(lcm > &max_d * &self.w_modulus + &max_rem);

            // On i-th mul_check_limbs,
            // borrow = limbs * limb_modulus + 2
            // v * limb_modulus =
            //   sum(j, a[j] * b[i-j]) - sum(j, d[j] * w[i-j]) - rem[i] + limb_modulus * borrow - borrowed[i]

            let borrow = &self.limbs * &self.limb_modulus + 2u64;
            // To avoid sub overflow
            // limb_modulus * borrow - borrow >= max(sum(j, d[j] * w[i-j])) + max(rem[i])
            // limb_modulus * borrow - borrow >= limbs * max(d[j]) * max(w[j]) + max(rem[i])
            let max_d_j = &self.limb_modulus - 1u64;
            let max_w_j = self
                .w_modulus_limbs_le_bn
                .iter()
                .reduce(|acc, x| acc.max(x))
                .unwrap();
            let max_rem_i = &self.limb_modulus - 1u64;
            assert!(
                &borrow * &self.limb_modulus - &borrow
                    >= self.limbs * max_d_j * max_w_j + max_rem_i
            );

            // For completeness of v
            // max(v) * limb_modulus >= max(sum(j, a[j] * b[i-j])) + limb_modulus * borrow
            // <- max(v) * limb_modulus >= limbs * max_a_j * max_b_j + limb_modulus * borrow
            let max_v = &self.limb_modulus * common_modulus - 1u64;
            let max_a_j = &self.limb_modulus * (self.overflow_limit - 1);
            let max_b_j = &max_a_j;
            assert!(&max_v * &self.limb_modulus >= &max_a_j * max_b_j * self.limbs + &self.limb_modulus * &borrow);

            // To avoid overflow
            // max(v) * limb_modulus < n_modulus
            assert!(&max_v * &self.limb_modulus < self.n_modulus);
        }

        // Algorithm limitation
        assert!(self.limbs >= 3);
    }

    pub fn d_bits(overflow_bits: u64) -> u64 {
        let w_max = field_to_bn(&-W::one());
        let w = &w_max + 1u64;
        let w_ceil_bits = w_max.bits();

        // a * b = w * d + rem
        let d_bits = w_ceil_bits + overflow_bits * 2 + 1;

        // To guarantee completeness of int_mul:
        // max(d) * w + min(rem) >= max(a) * max(b)
        let max_a = BigUint::from(1u64) << (w_ceil_bits + overflow_bits);
        let max_b = &max_a;
        assert!((BigUint::from(1u64) << d_bits) * w >= &max_a * max_b);

        d_bits
    }

    pub fn bn_to_limb_le_n(&self, w: &BigUint) -> Vec<N> {
        (0..self.limbs)
            .into_iter()
            .map(|i| bn_to_field(&((w >> (i * self.limb_bits)) & &self.limb_mask)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn bn_to_limb_le(&self, w: &BigUint) -> Vec<BigUint> {
        (0..self.limbs)
            .into_iter()
            .map(|i| ((w >> (i * self.limb_bits)) & &self.limb_mask))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    pub fn find_w_modulus_of_ceil_times(&self, times: u64) -> Vec<N> {
        let max = &self.w_ceil * times;
        let (n, rem) = max.div_rem(&self.w_modulus);
        let n = if rem.gt(&BigUint::from(0u64)) {
            n + 1u64
        } else {
            n
        };

        let mut upper = &self.w_modulus * n;

        let mut limbs = vec![];
        for _ in 0..self.limbs - 1 {
            let rem = (&upper & &self.limb_mask) + &self.limb_modulus * times;
            upper = (upper - &rem) >> self.limb_bits;
            limbs.push(bn_to_field::<N>(&rem));
            assert!(rem >= &self.limb_modulus * times - 1u64);
            assert!(rem < &self.limb_modulus * (times + 1));
        }

        assert!(upper >= (BigUint::from(1u64) << (self.w_ceil_bits % self.limb_bits)) * times);
        assert!(upper < (BigUint::from(1u64) << (self.w_ceil_bits % self.limb_bits)) * (times + 1));

        limbs.push(bn_to_field::<N>(&upper));
        limbs.try_into().unwrap()
    }
}

#[test]
fn test_range_info() {
    {
        use halo2_proofs::pairing::bn256::Fq;
        use halo2_proofs::pairing::bn256::Fr;

        let info = RangeInfo::<Fq, Fr>::new(18, 6);
        println!("info {:?}", info);
    }

    {
        use halo2_proofs::pairing::bls12_381::Fr as Bls12_381_Fr;
        use halo2_proofs::pairing::bn256::Fr;

        let info = RangeInfo::<Bls12_381_Fr, Fr>::new(18, 6);
        println!("info {:?}", info);
    }

    {
        use halo2_proofs::pairing::bls12_381::Fq as Bls12_381_Fq;
        use halo2_proofs::pairing::bn256::Fr;

        let info = RangeInfo::<Bls12_381_Fq, Fr>::new(18, 6);
        println!("info {:?}", info);
    }
}
