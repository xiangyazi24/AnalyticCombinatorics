import AnalyticCombinatorics.Ch8.Partitions.GreenForm

/-!
# Dirichlet-form representation of `greenQ` (renewal route B, Layer-2 Stage 3b/3c bridge)

The identity linking the `GreenForm` quadratic form `greenQ K f = ⟨(I−K)f, f⟩` to the directed jump
energy and killing defect (ChatGPT ac2 R12), for a **symmetric** kernel:

  `greenQ K f = ½·jumpEnergy K f + killEnergy K f`,
  `jumpEnergy K f = ∑_{x,y} K x y (f y − f x)²`,  `killEnergy K f = ∑_x (1 − rowSum K x)·f x²`.

This is the crux connecting `DirichletForm.bounded_jump_energy_le_edge_energy` (which bounds
`jumpEnergy`) to `GreenForm.green_domination_of_form_le` (which consumes `greenQ`).  Corollary
`greenQ_nonneg_of_symm_substochastic` discharges GreenForm's `hQnonneg` hypothesis for any symmetric
substochastic kernel.  (The `−Λ·E_edge` ellipticity lower half lives separately; see DOCTRINE R12/R13.)
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row sum of a finite kernel. -/
def rowSum (K : ι → ι → ℝ) (x : ι) : ℝ := ∑ y, K x y

/-- Unnormalized directed jump energy `∑_{x,y} K x y (f y − f x)²`. -/
def jumpEnergy (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := ∑ x, ∑ y, K x y * (f y - f x) ^ 2

/-- Killing/defect term `∑_x (1 − rowSum K x) f x²` in `⟨(I−K)f,f⟩`. -/
def killEnergy (K : ι → ι → ℝ) (f : ι → ℝ) : ℝ := ∑ x, (1 - rowSum K x) * (f x) ^ 2

/-- Symmetry swaps the two diagonal pieces in the directed jump expansion. -/
lemma symm_sum_y_sq_eq_sum_x_sq
    (K : ι → ι → ℝ) (f : ι → ℝ) (hKsym : ∀ x y, K x y = K y x) :
    (∑ x, ∑ y, K x y * (f y) ^ 2) = ∑ x, ∑ y, K x y * (f x) ^ 2 := by
  calc (∑ x, ∑ y, K x y * (f y) ^ 2) = ∑ y, ∑ x, K x y * (f y) ^ 2 := by rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, K y x * (f y) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro y _
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [hKsym x y]
    _ = ∑ x, ∑ y, K x y * (f x) ^ 2 := rfl

/-- `∑_{x,y} Kxy f(x)² = ∑_x rowSum(x) f(x)²`. -/
lemma sum_x_sq_eq_rowsum (K : ι → ι → ℝ) (f : ι → ℝ) :
    (∑ x, ∑ y, K x y * (f x) ^ 2) = ∑ x, rowSum K x * (f x) ^ 2 := by
  unfold rowSum
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.sum_mul]

/-- Expansion of the directed jump energy. -/
lemma jumpEnergy_expand (K : ι → ι → ℝ) (f : ι → ℝ) :
    jumpEnergy K f
      = (∑ x, ∑ y, K x y * (f y) ^ 2) - 2 * (∑ x, ∑ y, K x y * f y * f x)
        + (∑ x, ∑ y, K x y * (f x) ^ 2) := by
  unfold jumpEnergy
  calc (∑ x, ∑ y, K x y * (f y - f x) ^ 2)
        = ∑ x, ∑ y, (K x y * (f y) ^ 2 - K x y * f y * f x - K x y * f y * f x
            + K x y * (f x) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        refine Finset.sum_congr rfl ?_
        intro y _
        ring
    _ = (∑ x, ∑ y, K x y * (f y) ^ 2) - 2 * (∑ x, ∑ y, K x y * f y * f x)
          + (∑ x, ∑ y, K x y * (f x) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring

/-- Expansion of the killing term. -/
lemma killEnergy_expand (K : ι → ι → ℝ) (f : ι → ℝ) :
    killEnergy K f = (∑ x, (f x) ^ 2) - (∑ x, ∑ y, K x y * (f x) ^ 2) := by
  unfold killEnergy
  unfold rowSum
  calc (∑ x, (1 - ∑ y, K x y) * (f x) ^ 2)
        = ∑ x, ((f x) ^ 2 - (∑ y, K x y) * (f x) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        ring
    _ = (∑ x, (f x) ^ 2) - ∑ x, (∑ y, K x y) * (f x) ^ 2 := by rw [Finset.sum_sub_distrib]
    _ = (∑ x, (f x) ^ 2) - ∑ x, ∑ y, K x y * (f x) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Finset.sum_mul]

/-- Expansion of `greenQ`. -/
lemma greenQ_expand (K : ι → ι → ℝ) (f : ι → ℝ) :
    greenQ K f = (∑ x, (f x) ^ 2) - (∑ x, ∑ y, K x y * f y * f x) := by
  unfold greenQ greenA kerApply dotV
  calc (∑ x, (f x - ∑ y, K x y * f y) * f x)
        = ∑ x, ((f x) ^ 2 - (∑ y, K x y * f y) * f x) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        ring
    _ = (∑ x, (f x) ^ 2) - ∑ x, (∑ y, K x y * f y) * f x := by rw [Finset.sum_sub_distrib]
    _ = (∑ x, (f x) ^ 2) - ∑ x, ∑ y, K x y * f y * f x := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Finset.sum_mul]

/-- **Dirichlet-form representation** for a symmetric kernel:
`greenQ K f = ½·jumpEnergy K f + killEnergy K f`. -/
theorem greenQ_eq_half_jumpEnergy_add_killEnergy
    (K : ι → ι → ℝ) (f : ι → ℝ) (hKsym : ∀ x y, K x y = K y x) :
    greenQ K f = (1 / 2) * jumpEnergy K f + killEnergy K f := by
  set A : ℝ := ∑ x, ∑ y, K x y * (f y) ^ 2 with hA
  set B : ℝ := ∑ x, ∑ y, K x y * (f x) ^ 2 with hB
  set C : ℝ := ∑ x, ∑ y, K x y * f y * f x with hC
  set D : ℝ := ∑ x, (f x) ^ 2 with hD
  have hAB : A = B := by rw [hA, hB]; exact symm_sum_y_sq_eq_sum_x_sq K f hKsym
  have hJ : jumpEnergy K f = A - 2 * C + B := by rw [hA, hB, hC]; exact jumpEnergy_expand K f
  have hKill : killEnergy K f = D - B := by rw [hD, hB]; exact killEnergy_expand K f
  have hQ : greenQ K f = D - C := by rw [hD, hC]; exact greenQ_expand K f
  rw [hQ, hJ, hKill]; nlinarith

lemma jumpEnergy_nonneg (K : ι → ι → ℝ) (f : ι → ℝ) (hKnn : ∀ x y, 0 ≤ K x y) :
    0 ≤ jumpEnergy K f := by
  unfold jumpEnergy
  refine Finset.sum_nonneg ?_
  intro x _
  refine Finset.sum_nonneg ?_
  intro y _
  exact mul_nonneg (hKnn x y) (sq_nonneg _)

lemma killEnergy_nonneg (K : ι → ι → ℝ) (f : ι → ℝ) (hrow : ∀ x, rowSum K x ≤ 1) :
    0 ≤ killEnergy K f := by
  unfold killEnergy
  refine Finset.sum_nonneg ?_
  intro x _
  exact mul_nonneg (by linarith [hrow x]) (sq_nonneg _)

/-- `greenQ` is nonnegative for a symmetric substochastic kernel — discharges GreenForm's `hQnonneg`. -/
theorem greenQ_nonneg_of_symm_substochastic
    (K : ι → ι → ℝ) (hKsym : ∀ x y, K x y = K y x)
    (hKnn : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, rowSum K x ≤ 1) :
    ∀ f : ι → ℝ, 0 ≤ greenQ K f := by
  intro f
  rw [greenQ_eq_half_jumpEnergy_add_killEnergy K f hKsym]
  exact add_nonneg
    (mul_nonneg (by norm_num) (jumpEnergy_nonneg K f hKnn))
    (killEnergy_nonneg K f hrow)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
