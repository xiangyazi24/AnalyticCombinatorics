import Mathlib

/-!
# R7 Fact B via Doeblin: moment interpolation (Paley–Zygmund anti-concentration core)

The Tanaka occupation lower bound needs `E|D_T| ≥ c√T`, which comes from the second and fourth moments
via the L¹–L²–L⁴ interpolation `(E f²)³ ≤ (E|f|)²·(E f⁴)` (equivalently `E|f| ≥ (E f²)^{3/2}/√(E f⁴)`).
This file proves that as a pure finite-sum inequality (two Cauchy–Schwarz applications), in the
deterministic substrate (`E` = weighted finite sum), avoiding any measure-theoretic machinery.
Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **L¹–L²–L⁴ interpolation, nonnegative form.** For nonnegative weights `p` and nonnegative `a`,
`(∑ p a²)³ ≤ (∑ p a)² · (∑ p a⁴)`.  Two Cauchy–Schwarz steps. -/
theorem mean_sq_cubed_le_nonneg {ι : Type*} (s : Finset ι) (p a : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, p i * a i ^ 2) ^ 3
      ≤ (∑ i ∈ s, p i * a i) ^ 2 * (∑ i ∈ s, p i * a i ^ 4) := by
  -- cs1 : (∑ p a²)² ≤ (∑ p a)(∑ p a³)
  have cs1 : (∑ i ∈ s, p i * a i ^ 2) ^ 2
      ≤ (∑ i ∈ s, p i * a i) * (∑ i ∈ s, p i * a i ^ 3) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (p i * a i)) (fun i => Real.sqrt (p i * a i ^ 3))
    have eFG : (∑ i ∈ s, Real.sqrt (p i * a i) * Real.sqrt (p i * a i ^ 3))
        = ∑ i ∈ s, p i * a i ^ 2 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← Real.sqrt_mul (by have := hp i hi; have := ha i hi; positivity),
        show p i * a i * (p i * a i ^ 3) = (p i * a i ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by have := hp i hi; have := ha i hi; positivity)]
    have eF2 : (∑ i ∈ s, Real.sqrt (p i * a i) ^ 2) = ∑ i ∈ s, p i * a i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Real.sq_sqrt (by have := hp i hi; have := ha i hi; positivity)]
    have eG2 : (∑ i ∈ s, Real.sqrt (p i * a i ^ 3) ^ 2) = ∑ i ∈ s, p i * a i ^ 3 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Real.sq_sqrt (by have := hp i hi; have := ha i hi; positivity)]
    rw [eFG, eF2, eG2] at h
    exact h
  -- cs2 : (∑ p a³)² ≤ (∑ p a²)(∑ p a⁴)
  have cs2 : (∑ i ∈ s, p i * a i ^ 3) ^ 2
      ≤ (∑ i ∈ s, p i * a i ^ 2) * (∑ i ∈ s, p i * a i ^ 4) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (p i * a i ^ 2)) (fun i => Real.sqrt (p i * a i ^ 4))
    have eFG : (∑ i ∈ s, Real.sqrt (p i * a i ^ 2) * Real.sqrt (p i * a i ^ 4))
        = ∑ i ∈ s, p i * a i ^ 3 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← Real.sqrt_mul (by have := hp i hi; have := ha i hi; positivity),
        show p i * a i ^ 2 * (p i * a i ^ 4) = (p i * a i ^ 3) ^ 2 by ring,
        Real.sqrt_sq (by have := hp i hi; have := ha i hi; positivity)]
    have eF2 : (∑ i ∈ s, Real.sqrt (p i * a i ^ 2) ^ 2) = ∑ i ∈ s, p i * a i ^ 2 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Real.sq_sqrt (by have := hp i hi; have := ha i hi; positivity)]
    have eG2 : (∑ i ∈ s, Real.sqrt (p i * a i ^ 4) ^ 2) = ∑ i ∈ s, p i * a i ^ 4 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Real.sq_sqrt (by have := hp i hi; have := ha i hi; positivity)]
    rw [eFG, eF2, eG2] at h
    exact h
  -- combine: A² ≤ B·C and C² ≤ A·D give A³ ≤ B²·D
  set A := ∑ i ∈ s, p i * a i ^ 2 with hA
  set B := ∑ i ∈ s, p i * a i with hB
  set C := ∑ i ∈ s, p i * a i ^ 3 with hC
  set D := ∑ i ∈ s, p i * a i ^ 4 with hD
  have hAnn : 0 ≤ A := Finset.sum_nonneg (fun i hi => by have := hp i hi; have := ha i hi; positivity)
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun i hi => by have := hp i hi; have := ha i hi; positivity)
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun i hi => by have := hp i hi; have := ha i hi; positivity)
  have hDnn : 0 ≤ D := Finset.sum_nonneg (fun i hi => by have := hp i hi; have := ha i hi; positivity)
  -- A⁴ ≤ B²C² ≤ B²(AD) = A B² D, so A³ ≤ B² D (A ≥ 0)
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0]; simpa using mul_nonneg (sq_nonneg B) hDnn
  · have h4 : A ^ 4 ≤ B ^ 2 * C ^ 2 := by
      nlinarith [mul_le_mul cs1 cs1 (sq_nonneg A) (mul_nonneg hBnn hCnn)]
    have h5 : B ^ 2 * C ^ 2 ≤ B ^ 2 * (A * D) := mul_le_mul_of_nonneg_left cs2 (sq_nonneg B)
    have h6 : A * A ^ 3 ≤ A * (B ^ 2 * D) := by nlinarith [h4, h5]
    exact le_of_mul_le_mul_left h6 hApos

/-- **L¹–L²–L⁴ interpolation.** For nonnegative weights `p`, `(∑ p f²)³ ≤ (∑ p |f|)²·(∑ p f⁴)`.
With `∑ p = 1` this is `E|f| ≥ (E f²)^{3/2}/√(E f⁴)`. -/
theorem mean_sq_cubed_le {ι : Type*} (s : Finset ι) (p f : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    (∑ i ∈ s, p i * f i ^ 2) ^ 3
      ≤ (∑ i ∈ s, p i * |f i|) ^ 2 * (∑ i ∈ s, p i * f i ^ 4) := by
  have key := mean_sq_cubed_le_nonneg s p (fun i => |f i|) hp (fun i _ => abs_nonneg _)
  have e2 : (∑ i ∈ s, p i * |f i| ^ 2) = ∑ i ∈ s, p i * f i ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [sq_abs]
  have e4 : (∑ i ∈ s, p i * |f i| ^ 4) = ∑ i ∈ s, p i * f i ^ 4 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show |f i| ^ 4 = f i ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)]]
  rw [e2, e4] at key
  exact key

end AnalyticCombinatorics.Ch8.Partitions.Erdos
