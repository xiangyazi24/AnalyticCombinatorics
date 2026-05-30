import AnalyticCombinatorics.Ch1.OGF.Compositions
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Ch1 §I.3 — The sequence formula, demonstrated on integer compositions

Flajolet & Sedgewick, Part A, Chapter I, §I.3. The symbolic method predicts that
the sequence construction translates to `SEQ(C)(z) = 1/(1 - C(z))`. Here we verify
that prediction end-to-end for the running example `compositions = SEQ(ℙ)`:

* `ogf_posInt` — the OGF of the positive integers is `ℙ(z) = z/(1-z)`, in the form
  `ℙ(z)·(1 - z) = z`.
* `ogf_compositions_eq_seq_posInt` — **`C(z)·(1 - ℙ(z)) = 1`**, i.e.
  `C(z) = 1/(1 - ℙ(z))`, the sequence formula for compositions.

Both are obtained from the two independently-computed closed forms
(`ogf_posInt` here and `ogf_compositions` in `Compositions.lean`) by power-series
algebra and cancellation of the unit `1 - z`; neither assumes the convolution
recursion. The fully-general transfer `SEQ(C)(z) = (1 - C(z))⁻¹` for an arbitrary
class is left to a later milestone (it needs a first-part decomposition bijection
on `Composition`).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.coeff_ogf_posInt (n : ℕ) :
    coeff n CombClass.posInt.ogf = (if 0 < n then 1 else 0 : ℚ) := by
  rw [CombClass.coeff_ogf, CombClass.counts_posInt]
  split <;> simp

/-- **OGF of the positive integers** (F&S §I.3): `ℙ(z) = z/(1 - z)`, stated as
`ℙ(z)·(1 - z) = z`. -/
theorem CombClass.ogf_posInt :
    CombClass.posInt.ogf * (1 - X) = X := by
  have expand : CombClass.posInt.ogf * (1 - X)
      = CombClass.posInt.ogf - CombClass.posInt.ogf * X := by ring
  rw [expand]
  ext n
  rcases n with _ | m
  · simp [map_sub, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, coeff_X]
  · rw [map_sub, coeff_succ_mul_X, CombClass.coeff_ogf_posInt, CombClass.coeff_ogf_posInt,
      coeff_X]
    rcases m with _ | k <;> simp

private lemma one_sub_X_ne_zero : (1 - X : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have h2 : constantCoeff (R := ℚ) (1 - X) = constantCoeff (R := ℚ) 0 := by rw [h]
  simp at h2

/-- **The sequence formula for compositions** (F&S §I.3): the OGF of integer
compositions equals `1/(1 - ℙ(z))`, the symbolic-method prediction for
`SEQ(ℙ)`. Stated as `C(z)·(1 - ℙ(z)) = 1`. -/
theorem CombClass.ogf_compositions_eq_seq_posInt :
    CombClass.compositions.ogf * (1 - CombClass.posInt.ogf) = 1 := by
  apply mul_right_cancel₀ one_sub_X_ne_zero
  calc CombClass.compositions.ogf * (1 - CombClass.posInt.ogf) * (1 - X)
      = CombClass.compositions.ogf
          * ((1 - X) - CombClass.posInt.ogf * (1 - X)) := by ring
    _ = CombClass.compositions.ogf * ((1 - X) - X) := by rw [CombClass.ogf_posInt]
    _ = CombClass.compositions.ogf * (1 - 2 * X) := by ring
    _ = 1 - X := CombClass.ogf_compositions
    _ = 1 * (1 - X) := by ring

end AnalyticCombinatorics.Ch1
