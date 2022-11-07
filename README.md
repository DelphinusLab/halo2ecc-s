# halo2ecc-s
Re-implement an ecc circuits with halo2.

## Optimization Plan
1. Generate witness outside of synthesize.
2. Support multi-threading for witness generation.
3. Use 3 limbs for integer.
4. Reduce lookup.
