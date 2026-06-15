import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# Positive local variance of a product walk from two separated mass clumps (renewal route B, v0)

`locVar K D x = ∑_z K x z (D z − D x)²` is the *raw* second moment of the increment.  For the
product kernel `K((x,y),(a,b)) = P x a · P y b` of two independent copies and the difference
coordinate `D(a,b) = f a − f b`, a uniform positive lower bound on `locVar` follows from two
*separated* single-chain mass clumps: if `P` puts mass `≥ δ₂` on steps with `f`-increment `≥ hi`
and `≥ δ₁` on steps with `f`-increment `≤ lo` (`lo ≤ hi`), then

  `locVar (P⊗P) (f·.1 − f·.2) (x,y) ≥ δ₁·δ₂·(hi − lo)²`.

This is the abstract half of the `v0` input; the concrete half is the two `erdosWeight` window
clumps (the ρ-decrement takes separated values with positive probability).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Product-walk local variance lower bound** from two separated single-chain mass clumps. -/
lemma product_locVar_ge (P : α → α → ℝ) (f : α → ℝ) (x₀ y₀ : α)
    (S₁ S₂ : Finset α) (δ₁ δ₂ lo hi : ℝ)
    (hPnn : ∀ a b, 0 ≤ P a b)
    (hS1mass : δ₁ ≤ ∑ b ∈ S₁, P y₀ b) (hS2mass : δ₂ ≤ ∑ a ∈ S₂, P x₀ a)
    (hS1 : ∀ b ∈ S₁, f b - f y₀ ≤ lo) (hS2 : ∀ a ∈ S₂, hi ≤ f a - f x₀)
    (hgap : lo ≤ hi) (hδ1 : 0 ≤ δ₁) (hδ2 : 0 ≤ δ₂) :
    δ₁ * δ₂ * (hi - lo) ^ 2
      ≤ locVar (fun p q : α × α => P p.1 q.1 * P p.2 q.2) (fun p => f p.1 - f p.2) (x₀, y₀) := by
  have hgap0 : 0 ≤ hi - lo := by linarith
  -- restrict the locVar sum to S₂ ×ˢ S₁
  have hsub : (S₂ ×ˢ S₁) ⊆ (Finset.univ : Finset (α × α)) := Finset.subset_univ _
  have hsumnn : ∀ q : α × α, q ∉ S₂ ×ˢ S₁ →
      0 ≤ (fun p q : α × α => P p.1 q.1 * P p.2 q.2) (x₀, y₀) q
        * ((fun p => f p.1 - f p.2) q - (fun p => f p.1 - f p.2) (x₀, y₀)) ^ 2 := by
    intro q _
    exact mul_nonneg (mul_nonneg (hPnn _ _) (hPnn _ _)) (sq_nonneg _)
  unfold locVar
  calc δ₁ * δ₂ * (hi - lo) ^ 2
      ≤ (∑ a ∈ S₂, P x₀ a) * (∑ b ∈ S₁, P y₀ b) * (hi - lo) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc δ₁ * δ₂ = δ₂ * δ₁ := by ring
          _ ≤ (∑ a ∈ S₂, P x₀ a) * (∑ b ∈ S₁, P y₀ b) :=
              mul_le_mul hS2mass hS1mass hδ1 (Finset.sum_nonneg (fun a _ => hPnn _ _))
    _ = ∑ q ∈ S₂ ×ˢ S₁, (P x₀ q.1 * P y₀ q.2) * (hi - lo) ^ 2 := by
        rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul]
    _ ≤ ∑ q ∈ S₂ ×ˢ S₁, (P x₀ q.1 * P y₀ q.2)
          * ((f q.1 - f q.2) - (f x₀ - f y₀)) ^ 2 := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.mem_product] at hq
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hPnn _ _) (hPnn _ _))
        have hge : hi - lo ≤ (f q.1 - f q.2) - (f x₀ - f y₀) := by
          have h2 := hS2 q.1 hq.1
          have h1 := hS1 q.2 hq.2
          linarith
        nlinarith [hge, hgap0]
    _ ≤ ∑ q : α × α, (fun p q : α × α => P p.1 q.1 * P p.2 q.2) (x₀, y₀) q
          * ((fun p => f p.1 - f p.2) q - (fun p => f p.1 - f p.2) (x₀, y₀)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ hq => hsumnn q hq)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
