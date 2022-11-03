use crate::utils::{bn_to_field, field_to_bn, AssignedValue, Context};

use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn},
    poly::Rotation,
};
use num_bigint::BigUint;
use std::{marker::PhantomData, vec};

#[derive(Copy, Clone)]
enum RangeClass {
    WCeilLeading = 1,
    NFloorLeading = 2,
    DLeading = 3,
    Common = 4,
}

pub const COMMON_RANGE_BITS: usize = 18;
pub const W_CEIL_LEADING_CHUNKS: usize = 3;
pub const N_FLOOR_LEADING_CHUNKS: usize = 3;
pub const D_LEADING_CHUNKS: usize = 4;
pub const MAX_CHUNKS: usize = 5;

const CLASS_SHIFT_BITS: usize = 128;

#[derive(Clone, Debug)]
pub struct RangeGateConfig {
    pub range_table_column: TableColumn,
    pub block_first: Column<Fixed>,
    pub range_class: Column<Fixed>,
    pub value: Column<Advice>,
}

pub struct RangeInfo<W: BaseExt, N: FieldExt> {
    pub common_range_mask: BigUint,
    pub _phantom: PhantomData<(N, W)>,
}

pub struct RangeGate<W: BaseExt, N: FieldExt> {
    pub config: RangeGateConfig,
    pub info: RangeInfo<W, N>,
    pub _phantom: PhantomData<(N, W)>,
}

impl<W: BaseExt, N: FieldExt> RangeGate<W, N> {
    fn assign(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
        common_len: usize,
        class: Option<RangeClass>,
    ) -> Result<AssignedValue<N>, Error> {
        let mut offset = *ctx.range_offset;

        ctx.region.as_mut().assign_fixed(
            || "block",
            self.config.block_first,
            offset,
            || Ok(N::one()),
        )?;

        for i in 1..MAX_CHUNKS + 1 {
            ctx.region.as_mut().assign_fixed(
                || "block",
                self.config.block_first,
                offset + i,
                || Ok(N::zero()),
            )?;
        }

        let res = ctx.region.as_mut().assign_advice(
            || "value",
            self.config.value,
            offset,
            || Ok(bn_to_field(bn.unwrap())),
        )?;

        offset += 1;

        for i in 0..common_len {
            ctx.region.as_mut().assign_fixed(
                || "block",
                self.config.range_class,
                offset,
                || Ok(N::from(RangeClass::Common as u64)),
            )?;

            ctx.region.as_mut().assign_advice(
                || "value",
                self.config.value,
                offset,
                || {
                    Ok(bn_to_field(
                        &((bn.unwrap() >> (i * COMMON_RANGE_BITS)) & &self.info.common_range_mask),
                    ))
                },
            )?;

            offset += 1;
        }

        if class.is_some() {
            ctx.region.as_mut().assign_fixed(
                || "block",
                self.config.range_class,
                offset,
                || Ok(N::from(class.unwrap() as u64)),
            )?;

            ctx.region.as_mut().assign_advice(
                || "value",
                self.config.value,
                offset,
                || {
                    Ok(bn_to_field::<N>(
                        &((bn.unwrap() >> (common_len * COMMON_RANGE_BITS))
                            & &self.info.common_range_mask),
                    ))
                },
            )?;
        }

        *ctx.range_offset += MAX_CHUNKS + 1;

        Ok(AssignedValue(res))
    }
}

impl<W: BaseExt, N: FieldExt> RangeGate<W, N> {
    fn assign_common(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
    ) -> Result<AssignedValue<N>, Error> {
        self.assign(ctx, bn, 1, None)
    }

    fn assign_nonleading_limb(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
    ) -> Result<AssignedValue<N>, Error> {
        self.assign(ctx, bn, MAX_CHUNKS, None)
    }

    fn assign_w_ceil_leading_limb(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
    ) -> Result<AssignedValue<N>, Error> {
        self.assign(
            ctx,
            bn,
            W_CEIL_LEADING_CHUNKS - 1,
            Some(RangeClass::WCeilLeading),
        )
    }

    fn assign_n_floor_leading_limb(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
    ) -> Result<AssignedValue<N>, Error> {
        self.assign(
            ctx,
            bn,
            N_FLOOR_LEADING_CHUNKS - 1,
            Some(RangeClass::NFloorLeading),
        )
    }

    fn assign_d_leading_limb(
        &self,
        ctx: &mut Context<N>,
        bn: Option<&BigUint>,
    ) -> Result<AssignedValue<N>, Error> {
        self.assign(ctx, bn, D_LEADING_CHUNKS - 1, Some(RangeClass::DLeading))
    }
}

impl<W: BaseExt, N: FieldExt> RangeGate<W, N> {
    pub fn new(config: RangeGateConfig) -> Self {
        RangeGate {
            config,
            _phantom: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<N>) -> RangeGateConfig {
        let block_first = meta.fixed_column();
        let range_class = meta.fixed_column();
        let range_table_column = meta.lookup_table_column();
        let value = meta.advice_column();

        meta.enable_equality(value);

        meta.lookup("range check", |meta| {
            let class = meta.query_fixed(range_class, Rotation::cur());
            let is_block_first = meta.query_fixed(block_first, Rotation::cur());
            let v = meta.query_advice(value, Rotation::cur());

            let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));
            vec![(
                (class * Expression::Constant(class_shift) + v)
                    * (Expression::Constant(N::one()) - is_block_first),
                range_table_column,
            )]
        });

        meta.create_gate("block first sum", |meta| {
            let is_block_first = meta.query_fixed(block_first, Rotation::cur());
            let shift_unit = bn_to_field::<N>(&(BigUint::from(1u64) << COMMON_RANGE_BITS));
            let mut shift_acc = N::one();

            let mut acc = meta.query_advice(value, Rotation(1));
            for i in 1..MAX_CHUNKS as i32 {
                let c = meta.query_advice(value, Rotation(i + 1));
                shift_acc = shift_acc * &shift_unit;
                acc = acc + c * Expression::Constant(shift_acc);
            }

            vec![is_block_first * (acc - meta.query_advice(value, Rotation::cur()))]
        });

        RangeGateConfig {
            range_table_column,
            block_first,
            range_class,
            value,
        }
    }
}

impl<W: BaseExt, N: FieldExt> RangeGate<W, N> {
    pub fn init_table(
        &self,
        layouter: &mut impl Layouter<N>,
        integer_modulus: &BigUint,
    ) -> Result<(), Error> {
        let w_max = field_to_bn(&-W::one());
        let w_ceil_bits = w_max.bits() as usize;
        assert!(BigUint::from(1u64) << w_ceil_bits > w_max);
        assert!(BigUint::from(1u64) << (w_ceil_bits - 1) < w_max);
        let w_ceil_leading_range_bits = w_ceil_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            w_ceil_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            W_CEIL_LEADING_CHUNKS - 1
        );
        assert!(w_ceil_leading_range_bits != 0);

        let n_max = field_to_bn(&-N::one());
        let n_floor_bits = n_max.bits() as usize - 1;
        assert!(BigUint::from(1u64) << n_floor_bits < n_max);
        assert!(BigUint::from(1u64) << (n_floor_bits + 1) >= n_max);
        let n_floor_leading_range_bits = n_floor_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            n_floor_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            N_FLOOR_LEADING_CHUNKS - 1
        );
        assert!(n_floor_leading_range_bits != 0);

        let d_range_bits = get_d_range_bits_in_mul::<W, N>(integer_modulus);
        let d_leading_range_bits = d_range_bits % COMMON_RANGE_BITS;
        // limited by current implementation
        assert_eq!(
            d_range_bits / COMMON_RANGE_BITS % MAX_CHUNKS,
            D_LEADING_CHUNKS - 1
        );
        assert!(d_leading_range_bits != 0);

        let class_shift = bn_to_field::<N>(&(BigUint::from(1u64) << CLASS_SHIFT_BITS));
        layouter.assign_table(
            || "common range table",
            |mut table| {
                let mut offset = 0;

                table.assign_cell(
                    || "range table",
                    self.config.range_table_column,
                    offset,
                    || Ok(N::from(0u64)),
                )?;
                offset += 1;

                macro_rules! assign_range {
                    ($bits:expr, $class:expr) => {
                        let prefix = N::from($class as u64) * &class_shift;
                        for i in 0..1 << $bits {
                            table.assign_cell(
                                || "range table",
                                self.config.range_table_column,
                                offset,
                                || Ok(prefix + N::from(i as u64)),
                            )?;
                            offset += 1;
                        }
                    };
                }

                assign_range!(COMMON_RANGE_BITS, RangeClass::Common);
                assign_range!(d_leading_range_bits, RangeClass::DLeading);
                assign_range!(w_ceil_leading_range_bits, RangeClass::WCeilLeading);
                assign_range!(n_floor_leading_range_bits, RangeClass::NFloorLeading);

                Ok(())
            },
        )?;

        Ok(())
    }
}
