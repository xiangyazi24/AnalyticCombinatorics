import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# Conditioned residual kernel

`Kres` is the substochastic residual product kernel whose row mass is `1 - cmass`.
This file normalizes it to a stochastic conditioned-residual kernel.  Rows with
`cmass = 1` are parked at the current pair; the analytic application only uses
the `cmass < 1` rows, but the parked rows make the pair kernel stochastic
globally.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The conditioned residual kernel, in four-coordinate form. -/
def KhatRes (x y a b : α) : ℝ :=
  if cmass P rnk W x y < 1 then
    Kres P rnk W x y a b / (1 - cmass P rnk W x y)
  else if a = x ∧ b = y then 1 else 0

/-- The conditioned residual kernel as a kernel on pair states. -/
def KhatResPair (xy zw : α × α) : ℝ :=
  KhatRes P rnk W xy.1 xy.2 zw.1 zw.2

/-- Point mass at a pair. -/
def pairDelta (i j : α) : α × α → ℝ :=
  fun xy => if xy = (i, j) then 1 else 0

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
lemma Kres_sum (x y : α) :
    ∑ a, ∑ b, Kres P rnk W x y a b = 1 - cmass P rnk W x y := by
  calc
    ∑ a, ∑ b, Kres P rnk W x y a b
        = ∑ a, Lres P rnk W x y a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact Kres_left_marginal P rnk W hPnn hPmass x y a
    _ = 1 - cmass P rnk W x y := Lres_sum P rnk W hPmass x y

include hPnn hPmass in
lemma KhatRes_nonneg (x y a b : α) :
    0 ≤ KhatRes P rnk W x y a b := by
  unfold KhatRes
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    exact div_nonneg (Kres_nonneg P rnk W hPnn hPmass x y a b) (by linarith)
  · simp only [if_neg h]
    split <;> norm_num

include hPnn hPmass in
lemma KhatRes_sum_of_cmass_lt {x y : α} (h : cmass P rnk W x y < 1) :
    ∑ a, ∑ b, KhatRes P rnk W x y a b = 1 := by
  have hden : 1 - cmass P rnk W x y ≠ 0 := by linarith
  unfold KhatRes
  simp only [if_pos h]
  simp_rw [← Finset.sum_div]
  rw [Kres_sum P rnk W hPnn hPmass x y, div_self hden]

include hPnn hPmass in
lemma KhatRes_sum (x y : α) :
    ∑ a, ∑ b, KhatRes P rnk W x y a b = 1 := by
  by_cases h : cmass P rnk W x y < 1
  · exact KhatRes_sum_of_cmass_lt P rnk W hPnn hPmass h
  · unfold KhatRes
    simp only [if_neg h]
    have hinner :
        ∀ a : α, (∑ b : α, if a = x ∧ b = y then (1 : ℝ) else 0) =
          if a = x then 1 else 0 := by
      intro a
      by_cases ha : a = x
      · subst a
        simp
      · simp [ha]
    simp_rw [hinner]
    simp

include hPnn hPmass in
lemma KhatResPair_nonneg (xy zw : α × α) :
    0 ≤ KhatResPair P rnk W xy zw := by
  exact KhatRes_nonneg P rnk W hPnn hPmass xy.1 xy.2 zw.1 zw.2

include hPnn hPmass in
lemma KhatResPair_sum (xy : α × α) :
    ∑ zw, KhatResPair P rnk W xy zw = 1 := by
  cases xy with
  | mk x y =>
      rw [Fintype.sum_prod_type]
      simpa [KhatResPair] using KhatRes_sum P rnk W hPnn hPmass x y

lemma pairDelta_nonneg (i j : α) (xy : α × α) :
    0 ≤ pairDelta i j xy := by
  unfold pairDelta
  split <;> norm_num

lemma pairDelta_sum (i j : α) :
    ∑ xy, pairDelta i j xy = 1 := by
  simp [pairDelta]

lemma Cpart_eq_zero_of_not_GoodW {x y z : α} (hxy : ¬ GoodW rnk W x y) :
    Cpart P rnk W x y z = 0 := by
  simp [Cpart, hxy]

lemma cmass_eq_zero_of_not_GoodW {x y : α} (hxy : ¬ GoodW rnk W x y) :
    cmass P rnk W x y = 0 := by
  simp [cmass, Cpart_eq_zero_of_not_GoodW P rnk W hxy]

lemma Kres_eq_prod_of_not_GoodW {x y a b : α} (hxy : ¬ GoodW rnk W x y) :
    Kres P rnk W x y a b = P x a * P y b := by
  have hc : cmass P rnk W x y = 0 := cmass_eq_zero_of_not_GoodW P rnk W hxy
  simp [Kres, Lres, Rres, Cpart_eq_zero_of_not_GoodW P rnk W hxy, hc]

lemma KhatRes_eq_prod_of_not_GoodW {x y a b : α} (hxy : ¬ GoodW rnk W x y) :
    KhatRes P rnk W x y a b = P x a * P y b := by
  have hc : cmass P rnk W x y = 0 := cmass_eq_zero_of_not_GoodW P rnk W hxy
  simp [KhatRes, Kres_eq_prod_of_not_GoodW P rnk W hxy, hc]

#print axioms KhatResPair_sum

end AnalyticCombinatorics.Ch8.Partitions.Erdos
