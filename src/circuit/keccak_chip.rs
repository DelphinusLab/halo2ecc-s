use crate::{
    assign::{AssignedCondition, AssignedValue},
    context::Context,
    gate::base_chip::BaseChipOps,
    pair,
    utils::{bn_to_field, field_to_bn},
};
use halo2_proofs::arithmetic::FieldExt;

const T: usize = 5;
const W: usize = 64;
pub const ABSORB_BITS_RATE: usize = 1088;

pub type AssignedState<N> = [[[AssignedCondition<N>; W]; T]; T];

const ROTATION_CONSTANTS: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

pub const N_R: usize = T * T - 1;

pub static ROUND_CONSTANTS: [u64; N_R] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

pub trait KeccakChipOps<N: FieldExt> {
    fn base_chip(&mut self) -> &mut dyn BaseChipOps<N>;
    fn init(&mut self) -> AssignedState<N> {
        let zero = AssignedCondition(self.base_chip().assign_constant(N::zero()));
        let state = [[[zero; W]; T]; T];
        state
    }

    fn theta(&mut self, state: &mut AssignedState<N>) {
        let mut c = state[0].clone();

        let prev = |x| (x + 4) % 5;
        let next = |x| (x + 1) % 5;

        for x in 0..T {
            let y = &state[x];
            let mut ci = y[0].clone();
            for i in 1..T {
                for z in 0..W {
                    ci[z] = self.base_chip().xor(&ci[z], &y[i][z]);
                }
            }
            c[x] = ci;
        }

        for x in 0..T {
            let mut di = c[next(x)].clone();
            di.rotate_left(1);
            for z in 0..W {
                di[z] = self.base_chip().xor(&c[prev(x)][z], &di[z]);
            }
            for y in 0..T {
                for z in 0..W {
                    state[x][y][z] = self.base_chip().xor(&state[x][y][z], &di[z]);
                }
            }
        }
    }

    fn rho(&mut self, state: &mut AssignedState<N>) {
        for x in 0..T {
            for y in 0..T {
                state[x][y].rotate_left(ROTATION_CONSTANTS[x][y]);
            }
        }
    }

    fn pi(&mut self, state: &mut AssignedState<N>) {
        let mut out = state.clone();

        for x in 0..T {
            for y in 0..T {
                out[y][(2 * x + 3 * y) % 5] = state[x][y].clone();
            }
        }

        *state = out;
    }

    fn xi(&mut self, state: &mut AssignedState<N>) {
        let next = |x: usize| (x + 1) % 5;
        let skip = |x: usize| (x + 2) % 5;

        let mut out = state.clone();

        for x in 0..T {
            for y in 0..T {
                for z in 0..W {
                    let t = self
                        .base_chip()
                        .not_and(&state[next(x)][y][z], &state[skip(x)][y][z]);
                    out[x][y][z] = self.base_chip().xor(&state[x][y][z], &t);
                }
            }
        }

        *state = out;
    }

    fn iota(&mut self, state: &mut AssignedState<N>, round: usize) {
        for z in 0..W {
            // xor_const(a, b) = if b is 0 { a } else { not(a) }
            if ROUND_CONSTANTS[round] & (1 << z) != 0 {
                state[0][0][z] = self.base_chip().not(&state[0][0][z]);
            }
        }
    }

    fn permute(&mut self, state: &mut AssignedState<N>) {
        for i in 0..N_R {
            self.theta(state);
            self.rho(state);
            self.pi(state);
            self.xi(state);
            self.iota(state, i);
        }
    }

    fn absorb(&mut self, state: &mut AssignedState<N>, input: &[AssignedCondition<N>]) {
        assert!(input.len() == ABSORB_BITS_RATE);
        let mut x = 0;
        let mut y = 0;
        for i in 0..ABSORB_BITS_RATE / W {
            for j in 0..W {
                state[x][y][j] = self.base_chip().xor(&input[i * W + j], &state[x][y][j]);
            }
            if x < 5 - 1 {
                x += 1;
            } else {
                y += 1;
                x = 0;
            }
        }
        self.permute(state);
    }

    // We don't care that decomposed value is larger than modulus, because the u256 should be used as scalar.
    fn decompose_scalar_as_u256_be(&mut self, s: &AssignedValue<N>) -> [AssignedCondition<N>; 256] {
        let one = N::one();
        let two = one + &one;
        let four = two + &two;

        let mut bits = vec![];

        let s_bn = field_to_bn(&s.val);
        let mut v = s.clone();

        for i in 0..256 / 2 {
            let b0 = if s_bn.bit(i * 2) { N::one() } else { N::zero() };
            let b1 = if s_bn.bit(i * 2 + 1) {
                N::one()
            } else {
                N::zero()
            };
            let b0 = self.base_chip().assign_bit(b0);
            let b1 = self.base_chip().assign_bit(b1);
            let v_next: N = bn_to_field(&(&s_bn >> (i * 2 + 2)));

            let cells = self.base_chip().one_line_with_last(
                vec![
                    pair!(v_next.clone(), four),
                    pair!(&b1.0, two),
                    pair!(&b0.0, one),
                ],
                pair!(&v, -one),
                None,
                (vec![], None),
            );

            v = cells.0[0];

            bits.push(b0);
            bits.push(b1);
        }

        self.base_chip().assert_constant(&v, N::zero());
        bits.reverse();
        bits.try_into().unwrap()
    }

    fn compose_u256_to_scalar_be(&mut self, s: &[AssignedCondition<N>]) -> AssignedValue<N> {
        assert!(s.len() == 256);
        let mut acc = self.base_chip().assign_constant(N::zero());

        let one = N::one();
        let two = one + &one;
        let four = two + &two;

        for i in 0..256 / 2 {
            let b0 = s[i * 2 + 1];
            let b1 = s[i * 2];

            acc = self
                .base_chip()
                .sum_with_constant(vec![(&b0.0, one), (&b1.0, two), (&acc, four)], None);
        }

        acc
    }

    fn hash(&mut self, input: &[AssignedValue<N>]) -> AssignedValue<N> {
        let assigned_one = AssignedCondition(self.base_chip().assign_constant(N::one()));
        let assigned_zero = AssignedCondition(self.base_chip().assign_constant(N::zero()));
        let mut state = self.init();

        let raw_len = input.len() * 256;
        let mut input_bits = vec![];
        for v in input {
            input_bits.extend_from_slice(&self.decompose_scalar_as_u256_be(v)[..]);
        }

        let aligned_len =
            (raw_len + 8 + ABSORB_BITS_RATE - 1) / ABSORB_BITS_RATE * ABSORB_BITS_RATE;
        let padding_len = aligned_len - raw_len;

        if padding_len == 8 {
            // padding 0x86
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_zero.clone());
        } else {
            // padding 0x06
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_zero.clone());

            // padding zero
            for _ in 0..padding_len - 16 {
                input_bits.push(assigned_zero.clone());
            }

            // padding 0x80
            input_bits.push(assigned_one.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
            input_bits.push(assigned_zero.clone());
        }

        for c in input_bits.chunks_exact(ABSORB_BITS_RATE) {
            self.absorb(&mut state, &c);
        }

        let res_bits = vec![state[0][0], state[1][0], state[2][0], state[3][0]].concat();
        self.compose_u256_to_scalar_be(&res_bits[..])
    }
}

impl<N: FieldExt> KeccakChipOps<N> for Context<N> {
    fn base_chip(&mut self) -> &mut dyn BaseChipOps<N> {
        self
    }
}
