# halo2ecc-s
Re-implement an ecc circuits with halo2.

## Optimizations
1. Generate witness outside of synthesize.
2. Support multi-threading for witness generation.
3. Use 3 limbs for integer.
4. Reduce lookup.

## Observation
1. I tried to optimize msm by group points like pippenger, but the benefit is small. The bottleneck is on the `pick_candidates` if the window size is large.

## TODO
1. Because `pick_candidates` is current bottleneck, I think `wnaf` can be used to reduce the select count.
   
