Done.

Created `AnalyticCombinatorics/PartB/Ch9/RandomStructures.lean` with:

- `BoltzmannProbability` over rational finite OGF truncations.
- Catalan/Boltzmann expected-size partial sums at `z = 1/4`, checked increasing for `0..10`.
- Largest-cycle count/fraction for permutations, including the `n = 4` `3-cycle or 4-cycle` check.
- Random mapping connected-component count recurrence, row-sum checks against `n^n`, and exact averages for `n = 1..5`.
- Prop-valued `MappingComponentsHalfLogAsymptotic` and `HasGaussianTail` interfaces.

Verification:

- `lake build AnalyticCombinatorics.PartB.Ch9.RandomStructures` passes.

Note: I also added the Ch9 import to `AnalyticCombinatorics.lean`. A full `lake build AnalyticCombinatorics` currently fails in existing/unrelated `AnalyticCombinatorics/PartA/Ch3/MultivariateGF.lean`.
