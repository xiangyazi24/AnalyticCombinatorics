import AnalyticCombinatorics.Ch1.OGF.Defs

/-!
# Ch1 §I.2 — The combinatorial sum (disjoint union) construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, first admissible construction.
If `A = B + C` is the disjoint union of two combinatorial classes (an object of
size `n` is a `B`-object of size `n` *or* a `C`-object of size `n`), then the
counting sequences add, `Aₙ = Bₙ + Cₙ`, and hence the OGFs add:

  **`(B + C)(z) = B(z) + C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` identity `counts_sum`; the
generating-function identity `ogf_sum` is its image under `ogfSeq`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The combinatorial sum `B + C`: objects of size `n` are the disjoint union of
the size-`n` objects of `B` and of `C` (F&S §I.2). -/
def CombClass.sum (C D : CombClass) : CombClass where
  Obj n := C.Obj n ⊕ D.Obj n
  finObj _ := inferInstance

/-- Counting sequences add: `(B + C)ₙ = Bₙ + Cₙ`. The genuine combinatorial fact,
from `Fintype.card_sum`. -/
@[simp] lemma CombClass.counts_sum (C D : CombClass) (n : ℕ) :
    (C.sum D).counts n = C.counts n + D.counts n :=
  Fintype.card_sum

/-- **Sum rule** (F&S Theorem I.1): `(B + C)(z) = B(z) + C(z)`. -/
theorem CombClass.ogf_sum (C D : CombClass) :
    (C.sum D).ogf = C.ogf + D.ogf := by
  ext n
  simp [CombClass.counts_sum]

end AnalyticCombinatorics.Ch1
