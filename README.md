# halo2ecc-s
Re-implement an ecc circuits with halo2.

## Optimizations
1. Generate witness outside of synthesize.
2. Support multi-threading for witness generation.
3. Use 3 limbs for bn256 Fp over Fr integer.
4. Reduce lookup.
5. Use select chip to reduce bisect points in MSM.

## Pairing
1. Support bn256 pairing check over bn256 Fr circuit. See `test_bn256_pairing_chip_over_bn256_fr` for usage.
2. Support bls12_381 pairing check over bn256 Fr circuit. See `test_bls12_381_pairing_chip_over_bn256_fr` for usage.
