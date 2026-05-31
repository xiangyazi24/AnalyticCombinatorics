import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Ch1 §I.6 — The pointing construction Θ

Flajolet & Sedgewick, Part A, Chapter I. The *pointing* of a class `C`,
`Θ(C)`, distinguishes one of the `n` atoms of a size-`n` object: a pointed object
is a `C`-object together with a choice of one of its `n` atoms. Hence
`Θ(C)ₙ = n·Cₙ`, and the OGF is

  **`Θ(C)(z) = z·C'(z)`**

(the operator `z d/dz`). We model the pointed objects by `C.Obj n × Fin n`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The pointing construction `Θ(C)` (F&S §I.6): a size-`n` object is a `C`-object
together with a distinguished atom (one of its `n` atoms), modelled as
`C.Obj n × Fin n`. -/
def CombClass.pointing (C : CombClass) : CombClass where
  Obj n := C.Obj n × Fin n
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_pointing (C : CombClass) (n : ℕ) :
    C.pointing.counts n = C.counts n * n := by
  change Fintype.card (C.Obj n × Fin n) = _
  rw [Fintype.card_prod, Fintype.card_fin]
  rfl

/-- **Pointing rule** (F&S §I.6): `Θ(C)(z) = z·C'(z)`. -/
theorem CombClass.ogf_pointing (C : CombClass) :
    C.pointing.ogf = X * PowerSeries.derivativeFun C.ogf := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_pointing]
  cases n with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, CombClass.coeff_ogf]
    push_cast
    ring

end AnalyticCombinatorics.Ch1
