Implemented the fallback coefficient-level result.

What changed:
- Appended coefficient theorems in `AnalyticCombinatorics/Examples/CyclicPermutations.lean`.
- Proved the zero coefficient:
  `labelCycCount_Atom_egf_coeff_zero`.
- Proved the positive coefficient formula:
  `labelCycCount_Atom_egf_coeff_pos`.
- Proved the all-`n` coefficient formula:
  `labelCycCount_Atom_egf_coeff`.
- Proved equality with the explicit formal series:
  `labelCycCount_Atom_egf_coeffs`.

I did not state the requested `-PowerSeries.log (1 - PowerSeries.X)` theorem because this Mathlib checkout has `PowerSeries.exp` but no `PowerSeries.log` API in `Mathlib/RingTheory/PowerSeries`.

Verification:
- `lake env lean AnalyticCombinatorics/Examples/CyclicPermutations.lean`
- `lake build`

Both pass. No new `sorry`s or `axiom`s were introduced.
