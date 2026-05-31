import AnalyticCombinatorics.Ch2.EGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sum

/-!
# Ch2 §II.1 — The labelled sum

Flajolet & Sedgewick, Part A, Chapter II. The combinatorial sum (disjoint union)
is the same construction for labelled and unlabelled classes (it reuses
`CombClass.sum`); only the translation to the EGF differs:

  **`(A + B)(z) = A(z) + B(z)`**.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- **Labelled sum rule** (F&S §II.1): `(A + B)(z) = A(z) + B(z)` for EGFs. -/
theorem CombClass.egf_sum (A B : CombClass) :
    (A.sum B).egf = A.egf + B.egf := by
  ext n
  rw [map_add, CombClass.coeff_egf, CombClass.coeff_egf, CombClass.coeff_egf,
    CombClass.counts_sum]
  push_cast
  ring

end AnalyticCombinatorics.Ch1
