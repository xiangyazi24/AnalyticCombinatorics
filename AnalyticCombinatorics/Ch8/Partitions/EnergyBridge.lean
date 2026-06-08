import AnalyticCombinatorics.Ch8.Partitions.ITEROccupation

/-!
# R7 Fact B via Doeblin: the D²-energy coalescence bridge

A direct energy argument on the *substochastic* unmatched mass `Umat` (no conditioned walk needed).
With `D` the pair-difference and `E t = ∑ Umat t · D²`, the per-row second-moment drift is `≥ c` off the
window (`c = v₀ − 2Rη > 0`) and `≥ −R²` on the window (trivially, next energy `≥ 0`, `D² ≤ R²`).
Telescoping with `E ≤ R²·umass ≤ R²`:

  `c · ∑_{t<M} umass t ≤ R² + (c + R²) · ∑_{t<M} goodMass t`.

Combined with `umass_le_one_sub_occupation` (`δ·∑goodMass ≤ 1`), `∑ umass` is bounded, so (umass
nonincreasing) `umass M ≤ K₀/M → 0`.  Deterministic finite-sum.  Opus-authored (energy identity ChatGPT R11).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

/-- D²-weighted unmatched mass. -/
def energy (D : α → α → ℝ) (t : ℕ) : ℝ :=
  ∑ a, ∑ b, Umat P rnk W i j t a b * (D a b) ^ 2

include hPnn hPmass in
/-- `umass` is `≤ 1` (it starts at `1` and is nonincreasing). -/
lemma umass_le_one (t : ℕ) : umass P rnk W i j t ≤ 1 := by
  have hmono : ∀ s, umass P rnk W i j (s + 1) ≤ umass P rnk W i j s := by
    intro s
    rw [umass_succ_eq P rnk W hPnn hPmass i j s]
    have : 0 ≤ ∑ x, ∑ y, Umat P rnk W i j s x y * cmass P rnk W x y :=
      Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
        mul_nonneg (Umat_nonneg P rnk W hPnn hPmass i j s x y) (cmass_nonneg P rnk W hPnn x y)))
    linarith
  have h0 : umass P rnk W i j 0 = 1 := by
    unfold umass
    have hx : ∀ x, ∑ y, Umat P rnk W i j 0 x y = if x = i then (1 : ℝ) else 0 := by
      intro x; simp only [Umat]; by_cases hx : x = i <;> simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ)),
      if_pos (Finset.mem_univ i)]
  induction t with
  | zero => rw [h0]
  | succ t ih => exact le_trans (hmono t) ih

include hPnn hPmass in
/-- **Energy controls occupation.** -/
theorem energy_controls_goodMass (D : α → α → ℝ) (c R : ℝ)
    (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
    (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
        c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
    (M : ℕ) :
    c * (∑ t ∈ Finset.range M, umass P rnk W i j t)
      ≤ R ^ 2 + (c + R ^ 2) * ∑ t ∈ Finset.range M, goodMass P rnk W i j t := by
  have hUnn : ∀ t a b, 0 ≤ Umat P rnk W i j t a b := Umat_nonneg P rnk W hPnn hPmass i j
  have hrowEnn : ∀ x y, 0 ≤ ∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2 := fun x y =>
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (Kres_nonneg P rnk W hPnn hPmass x y a b) (sq_nonneg _)))
  have hrow : ∀ x y, (if GoodW rnk W x y then -R ^ 2 else c)
      ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2 := by
    intro x y
    by_cases hg : GoodW rnk W x y
    · rw [if_pos hg]; nlinarith [hrowEnn x y, hD x y]
    · rw [if_neg hg]; exact hrow_off x y hg
  have hstep : ∀ t, c * umass P rnk W i j t - (c + R ^ 2) * goodMass P rnk W i j t
      ≤ energy P rnk W i j D (t + 1) - energy P rnk W i j D t := by
    intro t
    have hexp : energy P rnk W i j D (t + 1)
        = ∑ x, ∑ y, Umat P rnk W i j t x y
            * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) := by
      unfold energy
      have e1 : (∑ a, ∑ b, Umat P rnk W i j (t + 1) a b * (D a b) ^ 2)
          = ∑ a, ∑ b, ∑ x, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        simp only [Umat, Finset.sum_mul]
      rw [e1]
      calc (∑ a, ∑ b, ∑ x, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2)
          = ∑ a, ∑ x, ∑ b, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_comm]
        _ = ∑ x, ∑ a, ∑ b, ∑ y,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by rw [Finset.sum_comm]
        _ = ∑ x, ∑ a, ∑ y, ∑ b,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ => ?_))
            rw [Finset.sum_comm]
        _ = ∑ x, ∑ y, ∑ a, ∑ b,
              Umat P rnk W i j t x y * Kres P rnk W x y a b * (D a b) ^ 2 := by
            refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_comm]
        _ = ∑ x, ∑ y, Umat P rnk W i j t x y
              * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun b _ => by ring)
    have hdiff : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2)) - energy P rnk W i j D t
        = ∑ x, ∑ y, Umat P rnk W i j t x y
            * ((∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2) := by
      unfold energy
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => by ring)
    have hge : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (if GoodW rnk W x y then -R ^ 2 else c))
        ≤ ∑ x, ∑ y, Umat P rnk W i j t x y
            * ((∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hrow x y) (hUnn t x y)))
    have hval : (∑ x, ∑ y, Umat P rnk W i j t x y
          * (if GoodW rnk W x y then -R ^ 2 else c))
        = c * umass P rnk W i j t - (c + R ^ 2) * goodMass P rnk W i j t := by
      unfold umass goodMass
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hg : GoodW rnk W x y
      · rw [if_pos hg, if_pos hg]; ring
      · rw [if_neg hg, if_neg hg]; ring
    rw [hexp, hdiff, ← hval]; exact hge
  have htel : c * (∑ t ∈ Finset.range M, umass P rnk W i j t)
      - (c + R ^ 2) * (∑ t ∈ Finset.range M, goodMass P rnk W i j t)
      ≤ energy P rnk W i j D M - energy P rnk W i j D 0 := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
      linarith [ih, hstep M]
  have hE0 : 0 ≤ energy P rnk W i j D 0 :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      mul_nonneg (hUnn 0 a b) (sq_nonneg _)))
  have hEM : energy P rnk W i j D M ≤ R ^ 2 := by
    have h1 : energy P rnk W i j D M ≤ ∑ a, ∑ b, Umat P rnk W i j M a b * R ^ 2 := by
      unfold energy
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hD a b) (hUnn M a b)))
    have h2 : (∑ a, ∑ b, Umat P rnk W i j M a b * R ^ 2) = umass P rnk W i j M * R ^ 2 := by
      unfold umass; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_); rw [Finset.sum_mul]
    have h3 : umass P rnk W i j M ≤ 1 := umass_le_one P rnk W hPnn hPmass i j M
    rw [h2] at h1; nlinarith [h1, h3, sq_nonneg R]
  linarith [htel, hE0, hEM]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
