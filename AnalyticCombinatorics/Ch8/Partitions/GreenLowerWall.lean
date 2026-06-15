import AnalyticCombinatorics.Ch8.Partitions.ITERGreenT
import AnalyticCombinatorics.Ch8.Partitions.KhatRes

/-!
# Green potential bounds (renewal route B capstone support)

`greenT` (ITERGreenT) is the finite-horizon expected window occupation under the substochastic
residual kernel `Kres` (row sum `1 − cmass ≤ 1`).  This file banks the elementary upper bound
`greenT ≤ T` (each residual iterate of the window indicator is `≤ 1`).  The matching lower bound
`greenT ≥ c√T` (`greenT_lower_fixed_window`) is the lone analytic wall (see `DOCTRINE-walls.md`).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
/-- Each residual iterate of the window indicator is `≤ 1` (substochastic `Kres`). -/
lemma KresIter_le_one (t : ℕ) :
    ∀ x y, (KresAct P rnk W)^[t] (goodIndic rnk W) x y ≤ 1 := by
  induction t with
  | zero =>
      intro x y
      simp only [Function.iterate_zero, id_eq, goodIndic]
      split <;> norm_num
  | succ t ih =>
      intro x y
      rw [Function.iterate_succ', Function.comp_apply]
      calc KresAct P rnk W ((KresAct P rnk W)^[t] (goodIndic rnk W)) x y
          = ∑ a, ∑ b, Kres P rnk W x y a b
              * (KresAct P rnk W)^[t] (goodIndic rnk W) a b := rfl
        _ ≤ ∑ a, ∑ b, Kres P rnk W x y a b * 1 := by
            refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
            exact mul_le_mul_of_nonneg_left (ih a b) (Kres_nonneg P rnk W hPnn hPmass x y a b)
        _ = ∑ a, ∑ b, Kres P rnk W x y a b := by simp
        _ = 1 - cmass P rnk W x y := Kres_sum P rnk W hPnn hPmass x y
        _ ≤ 1 := by linarith [cmass_nonneg P rnk W hPnn x y]

include hPnn hPmass in
/-- `greenT ≤ T`: the finite-horizon window occupation is at most the horizon. -/
lemma greenT_le_T (T : ℕ) (x y : α) : greenT P rnk W T x y ≤ (T : ℝ) := by
  unfold greenT
  calc ∑ t ∈ Finset.range T, (KresAct P rnk W)^[t] (goodIndic rnk W) x y
      ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => KresIter_le_one P rnk W hPnn hPmass t x y)
    _ = (T : ℝ) := by simp

end AnalyticCombinatorics.Ch8.Partitions.Erdos
