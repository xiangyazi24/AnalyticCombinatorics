import AnalyticCombinatorics.Ch1.OGF.Defs
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The exponential generating function of a counting sequence `a : ℕ → ℕ`:
`A(z) = ∑ₙ aₙ zⁿ/n!`, a formal power series over `ℚ` (F&S §II.1). -/
noncomputable def egfSeq (a : ℕ → ℕ) : ℚ⟦X⟧ := mk fun n => (a n : ℚ) / (n.factorial : ℚ)

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

/-- The exponential generating function of a (labelled) combinatorial class. -/
noncomputable def CombClass.egf (C : CombClass) : ℚ⟦X⟧ := egfSeq C.counts

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

/-! ### Permutations -/

/-- The class of permutations (F&S §II.1): a size-`n` object is a permutation of
its `n` labels. -/
def CombClass.permutations : CombClass where
  Obj n := Equiv.Perm (Fin n)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_permutations (n : ℕ) :
    CombClass.permutations.counts n = n.factorial := by
  change Fintype.card (Equiv.Perm (Fin n)) = _
  rw [Fintype.card_perm, Fintype.card_fin]

/-- **EGF of permutations** (F&S §II.1): `P(z) = 1/(1 - z)`, as `P(z)·(1 - z) = 1`. -/
theorem CombClass.egf_permutations :
    CombClass.permutations.egf * (1 - X) = 1 := by
  have hcoeff : ∀ n, coeff n CombClass.permutations.egf = 1 := fun n => by
    rw [CombClass.coeff_egf, CombClass.counts_permutations,
      div_self (by exact_mod_cast Nat.factorial_ne_zero n)]
  have hconst : constantCoeff (R := ℚ) CombClass.permutations.egf = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; exact hcoeff 0
  have expand : CombClass.permutations.egf * (1 - X)
      = CombClass.permutations.egf - CombClass.permutations.egf * X := by ring
  rw [expand]
  ext n
  rcases n with _ | m
  · simp [coeff_zero_eq_constantCoeff, hconst, map_mul, constantCoeff_X]
  · rw [map_sub, coeff_succ_mul_X, hcoeff, hcoeff, coeff_one, if_neg (Nat.succ_ne_zero m)]
    simp

/-! ### The set class -/

/-- The "set" class (F&S §II.1): one object of each size — the labelled atom of the
`SET` construction. -/
def CombClass.setClass : CombClass where
  Obj _ := Unit
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_setClass (n : ℕ) : CombClass.setClass.counts n = 1 := by
  change Fintype.card Unit = _
  simp

/-- **EGF of the set class** (F&S §II.1): `E(z) = e^z`. -/
theorem CombClass.egf_setClass : CombClass.setClass.egf = PowerSeries.exp ℚ := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_setClass, PowerSeries.coeff_exp]
  simp

end AnalyticCombinatorics.Ch1
