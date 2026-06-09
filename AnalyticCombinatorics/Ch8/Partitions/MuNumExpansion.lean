import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MuNumModel
import AnalyticCombinatorics.Ch8.Partitions.MassRateApprox2
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOne
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOneTwoTerm
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwoAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentThreeAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound

/-!
# MuNum two-term expansion

`|muNum n − (μ̄ + μA/√n)| ≤ K/n` for large `n`, where
`μ̄ = 3/massLam` and `μA = 3/(2·massLam²)`.  Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ### Algebraic expansion of the model product -/

/-- `modelSummand·rhoDropModel = σ·e^{−tm}·(c₁·m + c₂·m² + c₃·m³ + c₄·m⁴)` with
  `c₁ = 3/(2·n·√n)`, `c₂ = 15/(8·n²·√n)`, `c₃ = 3/(8·n²·(√n)³) − 3·C/(16·n³)`,
  `c₄ = −3·C/(64·n⁴)`. -/
lemma modelSummand_mul_rhoDropModel_expand {n m : ℕ} (hm : m ≠ 0) :
    modelSummand n m * rhoDropModel n m
    = Sigma.sigmaR m * Real.exp (-(massLam / Real.sqrt (n:ℝ)) * (m:ℝ))
    * ( (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * (m:ℝ)
      + ((15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * (m:ℝ) ^ 2)
      + (((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3))
         - 3 * C / (16 * (n:ℝ) ^ 3)) * (m:ℝ) ^ 3)
      + ((-3 * C / (64 * (n:ℝ) ^ 4)) * (m:ℝ) ^ 4)) := by
  rw [modelSummand, rhoDropModel, if_neg hm]
  ring

/-! ### Model sum expressed via sigma moments (infinite-sum identity) -/

variable (n : ℕ) (hn1 : 1 ≤ n)

/-- `tsum` of `modelSummand·rhoDropModel = c₁·M₁ + c₂·M₂ + c₃·M₃ + c₄·M₄`. -/
lemma model_sum_eq_moments :
    (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
    = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
    + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
    + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
       - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
    + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have ht0 : 0 < massLam / Real.sqrt (n:ℝ) := div_pos massLam_pos hs0
  set t : ℝ := massLam / Real.sqrt (n:ℝ) with htdef
  set r : ℝ := Real.exp (-t) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  have hrn : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos, hrdef]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  -- each sigma moment is summable
  have hsum (k : ℕ) : Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m : ℝ) ^ k * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
    have h := summable_pow_sigma_geometric k hrn
    refine h.congr (fun m => ?_)
    rcases eq_or_ne m 0 with hz | hz
    · simp [hz]
    · simp [hz, hrdef, ← Real.exp_nat_mul, mul_comm (-t)]
  set c1 : ℝ := 3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ)) with hc1
  set c2 : ℝ := 15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ)) with hc2
  set c3 : ℝ := 3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3) - 3 * C / (16 * (n:ℝ) ^ 3) with hc3
  set c4 : ℝ := -3 * C / (64 * (n:ℝ) ^ 4) with hc4
  calc
    (∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
    = (∑' m : ℕ, if m = 0 then (0:ℝ) else Sigma.sigmaR m *
        Real.exp (-t * (m : ℝ)) * (c1 * (m : ℝ) + c2 * (m : ℝ) ^ 2
          + c3 * (m : ℝ) ^ 3 + c4 * (m : ℝ) ^ 4)) := by
      apply tsum_congr; intro m; rcases eq_or_ne m 0 with h | h
      · simp [h]
      · rw [if_neg h, modelSummand_mul_rhoDropModel_expand h, htdef, hc1, hc2, hc3, hc4]
    _ = (∑' m : ℕ, c1 • ((fun m => if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) m)
        + c2 • ((fun m => if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) m)
        + c3 • ((fun m => if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) m)
        + c4 • ((fun m => if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) m)) := by
      apply tsum_congr; intro m; rcases eq_or_ne m 0 with h | h
      · simp [h]
      · simp [h]; ring
    _ = c1 * (∑' m : ℕ, if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 1 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))
      + c2 * (∑' m : ℕ, if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 2 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))
      + c3 * (∑' m : ℕ, if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 3 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))
      + c4 * (∑' m : ℕ, if m = 0 then (0:ℝ) else
          (m : ℝ) ^ 4 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
      simp [tsum_add (hsum 1).const_smul c1
        (((hsum 2).const_smul c2).add (((hsum 3).const_smul c3).add ((hsum 4).const_smul c4))),
        tsum_add ((hsum 2).const_smul c2) (((hsum 3).const_smul c3).add ((hsum 4).const_smul c4)),
        tsum_add ((hsum 3).const_smul c3) ((hsum 4).const_smul c4),
        tsum_const_smul _ (hsum 1), tsum_const_smul _ (hsum 2),
        tsum_const_smul _ (hsum 3), tsum_const_smul _ (hsum 4)]
    _ = c1 * sigmaMoment 1 t + c2 * sigmaMoment 2 t + c3 * sigmaMoment 3 t + c4 * sigmaMoment 4 t := by
      simp [sigmaMoment, htdef]
    _ = (3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))) * sigmaMoment 1 (massLam / Real.sqrt (n:ℝ))
      + (15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))) * sigmaMoment 2 (massLam / Real.sqrt (n:ℝ))
      + ((3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3)
         - 3 * C / (16 * (n:ℝ) ^ 3)) * sigmaMoment 3 (massLam / Real.sqrt (n:ℝ))
      + ((-3 * C / (64 * (n:ℝ) ^ 4)) * sigmaMoment 4 (massLam / Real.sqrt (n:ℝ)))) := by
      rfl

/-! ### Small lemmas -/

/-- `sigmaMoment r t ≥ 0` for `t > 0` (all summands are nonnegative). -/
lemma sigmaMoment_nonneg (r : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ sigmaMoment r t := by
  rw [sigmaMoment]
  refine tsum_nonneg (fun m => ?_)
  rcases eq_or_ne m 0 with h | h
  · simp [h]
  · rw [if_neg h]; positivity

/-! ### Two-term asymptotic from the moment asymptotics -/

/-- For `n` large enough, `t = massLam/√n ∈ (0,1]`. -/
lemma t_in_range (n : ℕ) (hn : max 2 ⌈massLam ^ 2⌉₊ ≤ n) :
    0 < massLam / Real.sqrt (n:ℝ) ∧ massLam / Real.sqrt (n:ℝ) ≤ 1 := by
  have hn1 : 1 ≤ n := by
    have : 2 ≤ max 2 ⌈massLam ^ 2⌉₊ := le_max_left _ _
    omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  have hlam_sq_le_n : massLam ^ 2 ≤ (n : ℝ) := by
    have hceil : (⌈massLam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
      have : ⌈massLam ^ 2⌉₊ ≤ max 2 ⌈massLam ^ 2⌉₊ := le_max_right _ _
      exact_mod_cast le_trans this hn
    have hceil' : massLam ^ 2 ≤ (⌈massLam ^ 2⌉₊ : ℝ) := le_of_lt (Nat.lt_ceil _)
    nlinarith
  have hsqrt : massLam ≤ Real.sqrt (n:ℝ) := by
    calc massLam = Real.sqrt (massLam ^ 2) := (Real.sqrt_sq massLam_pos.le).symm
      _ ≤ Real.sqrt (n:ℝ) := Real.sqrt_le_sqrt hlam_sq_le_n
  exact ⟨div_pos massLam_pos hs0, (div_le_one hs0).mpr hsqrt⟩

set_option maxHeartbeats 8000000 in
/-- **Model sum two-term asymptotic**: `|model_sum − (μ̄ + μA/√n)| ≤ K/n` for large n.

  The identity `model_sum = c₁·M₁ + c₂·M₂ + c₃·M₃ + c₄·M₄` (Lemma `model_sum_eq_moments`)
  is combined with the banked moment asymptotics.  The cancellation of the `1/√n` coefficients
  yields `μA = 3/(2·massLam²)`.  The `O(1/n)` remainders from the moment errors, plus the
  `O(1/n)`-order `c₃·(24λ²/t⁵)` term and the `c₄·M₄` term, all contribute to the `K/n` bound. -/
theorem model_sum_two_term_asymp :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |(∑' m : ℕ, if m = 0 then (0:ℝ) else modelSummand n m * rhoDropModel n m)
        - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  have hmass_pos : 0 < massLam := massLam_pos
  have hmass_sq_eq : massLam ^ 2 = Real.pi ^ 2 / 6 := massLam_sq
  obtain ⟨K1, hK1pos, hK1⟩ := sigmaMoment_one_two_term
  obtain ⟨K2, hK2pos, hK2⟩ := sigmaMoment_two_asymp_weak
  obtain ⟨K3, hK3pos, hK3⟩ := sigmaMoment_three_one_term
  obtain ⟨K4, hK4pos, hK4⟩ := sigmaMoment_le_power_sharp 4
  set μ̄ : ℝ := 3 / massLam
  set μA : ℝ := 3 / (2 * massLam ^ 2)
  set R0 : ℕ := max 2 ⌈massLam ^ 2⌉₊
  set t (n : ℕ) : ℝ := massLam / Real.sqrt (n:ℝ)
  -- the moment asymptotics at t(n) for n ≥ R0
  have hM1ev : ∀ᶠ n : ℕ in atTop,
      |sigmaMoment 1 (t n) - (2 * massLam ^ 2 / (t n) ^ 3 - 1 / (2 * (t n) ^ 2))| ≤ K1 / (t n) := by
    filter_upwards [Filter.eventually_ge_atTop R0] with n hn
    rcases t_in_range n hn with ⟨htpos, htle1⟩; exact hK1 htpos htle1
  have hM2ev : ∀ᶠ n : ℕ in atTop,
      |sigmaMoment 2 (t n) - 6 * massLam ^ 2 / (t n) ^ 4| ≤ K2 / (t n) ^ 3 := by
    filter_upwards [Filter.eventually_ge_atTop R0] with n hn
    rcases t_in_range n hn with ⟨htpos, htle1⟩
    have h := hK2 htpos htle1; rw [hmass_sq_eq] at h; exact h
  have hM3ev : ∀ᶠ n : ℕ in atTop,
      |sigmaMoment 3 (t n) - 24 * massLam ^ 2 / (t n) ^ 5| ≤ K3 / (t n) ^ 4 := by
    filter_upwards [Filter.eventually_ge_atTop R0] with n hn
    rcases t_in_range n hn with ⟨htpos, htle1⟩
    have h := hK3 htpos htle1; rw [hmass_sq_eq] at h; exact h
  have hM4ev : ∀ᶠ n : ℕ in atTop,
      sigmaMoment 4 (t n) ≤ K4 / (t n) ^ 6 := by
    filter_upwards [Filter.eventually_ge_atTop R0] with n hn
    rcases t_in_range n hn with ⟨htpos, _⟩
    exact (hK4 (t n) htpos (le_refl _)).trans_eq (by ring)
  -- the identity: c1·M1error + c2·M2error + c3·M3error + c4·M4 ≤ K/n
  -- where each term |cⱼ|·(Kⱼ/(t n)^{kⱼ}) ≤ Cⱼ·Kⱼ/n with explicit Cⱼ
  -- C1: |c1|/(t n) = 3/(2·massLam)·(1/n)
  -- C2: |c2|/(t n)³ = 15/(8·massLam³)·(1/n)  (since n^{-5/2}/t³ = n^{-5/2}·n^{3/2}/λ³ = n^{-1}/λ³)
  -- C3: |c3|/(t n)⁴ ≤ (3/(8·massLam⁴) + 3·C/(16·massLam⁴))·(1/n)
  -- C4: |c4|/(t n)⁶ = 3·C/(64·massLam⁶)·(1/n)
  -- Plus the O(1/n) leading piece from c3: 9/(massLam³·n)
  set C1c : ℝ := 3 / (2 * massLam)
  set C2c : ℝ := 15 / (8 * massLam ^ 3)
  set C3c : ℝ := 3 / (8 * massLam ^ 4) + 3 * C / (16 * massLam ^ 4)
  set C4c : ℝ := 3 * C / (64 * massLam ^ 6)
  set K_total : ℝ := K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + (9 / massLam ^ 3) + 1
  have hK_total_pos : 0 < K_total := by positivity
  refine ⟨K_total, hK_total_pos, ?_⟩
  filter_upwards [hM1ev, hM2ev, hM3ev, hM4ev,
    model_sum_eq_moments, Filter.eventually_ge_atTop (max R0 1)] with n hM1n hM2n hM3n hM4n hsum_eq hnR0
  have hn1 : 1 ≤ n := le_trans (by exact le_max_right _ _) hnR0
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hs0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
  rcases t_in_range n (le_trans (le_max_left _ _) hnR0) with ⟨htpos, htle1⟩
  rw [hsum_eq n hn1]
  set c1 : ℝ := 3 / (2 * (n:ℝ) * Real.sqrt (n:ℝ))
  set c2 : ℝ := 15 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ))
  set c3 : ℝ := 3 / (8 * (n:ℝ) ^ 2 * Real.sqrt (n:ℝ) ^ 3) - 3 * C / (16 * (n:ℝ) ^ 3)
  set c4 : ℝ := -3 * C / (64 * (n:ℝ) ^ 4)
  set M1a : ℝ := 2 * massLam ^ 2 / (t n) ^ 3 - 1 / (2 * (t n) ^ 2)
  set M2a : ℝ := 6 * massLam ^ 2 / (t n) ^ 4
  set M3a : ℝ := 24 * massLam ^ 2 / (t n) ^ 5
  -- Cancellation identities (verified by field_simp + ring, confirmed by ChatGPT):
  -- c1·(2λ²/t³) = 3/λ = μ̄
  have hid_c1_leading : c1 * (2 * massLam ^ 2 / (t n) ^ 3) = μ̄ := by
    dsimp [c1, t, μ̄]; field_simp; ring
  -- c1·(−1/(2t²)) = −3/(4λ²√n)   (1/√n term, feeds μA)
  have hid_c1_correction : c1 * (-1 / (2 * (t n) ^ 2))
      = -(3 / (4 * massLam ^ 2)) / Real.sqrt (n : ℝ) := by
    dsimp [c1, t]; field_simp; ring
  -- c2·(6λ²/t⁴) = 45/(4λ²√n)   (1/√n term, feeds μA)
  have hid_c2_leading : c2 * (6 * massLam ^ 2 / (t n) ^ 4)
      = (45 / (4 * massLam ^ 2)) / Real.sqrt (n : ℝ) := by
    dsimp [c2, t]; field_simp; ring
  -- c3·(24λ²/t⁵) = 9/(λ³·n) − 9/(λ²√n)   (O(1/n) piece + 1/√n piece)
  have hid_c3_leading : c3 * (24 * massLam ^ 2 / (t n) ^ 5)
      = (9 / (massLam ^ 3)) / (n : ℝ) - (9 / (massLam ^ 2)) / Real.sqrt (n : ℝ) := by
    dsimp [c3, t]; field_simp; ring
  -- Total 1/√n: (−3/4 + 45/4 − 9)/λ²·1/√n = 6/(4λ²√n) = 3/(2λ²√n) = μA/√n ✓
  have hid_muA : μA / Real.sqrt (n : ℝ) = (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ) := by
    dsimp [μA]; ring
  -- Assemble: rewrite target as error terms
  -- LHS = c1·(M1 − M1a) + c2·(M2 − M2a) + c3·(M3 − M3a) + c4·M4
  --     + (c1·M1a + c2·M2a + c3·M3a − μ̄ − μA/√n)
  -- The last bracket = c1·(2λ²/t³) + c1·(−1/(2t²)) + c2·(6λ²/t⁴) + c3·(24λ²/t⁵) − μ̄ − μA/√n
  -- = (μ̄) + (−3/(4λ²√n)) + (45/(4λ²√n)) + (9/(λ³·n) − 9/(λ²√n)) − μ̄ − (3/(2λ²√n))
  -- = (−3 + 45 − 36)/(4λ²√n) + 9/(λ³·n) − 3/(2λ²√n)  ... wait:
  -- (−3 + 45)/(4λ²√n) = 42/(4λ²√n), then −9/(λ²√n) = −36/(4λ²√n)
  -- Total: (42−36)/(4λ²√n) = 6/(4λ²√n) = 3/(2λ²√n) = μA/√n ← CANCELS with −μA/√n!
  -- Leaving: 9/(λ³·n) = O(1/n)
  have hcancel : c1 * M1a + c2 * M2a + c3 * M3a - (μ̄ + μA / Real.sqrt (n : ℝ))
      = (9 / (massLam ^ 3)) / (n : ℝ) := by
    calc c1 * M1a + c2 * M2a + c3 * M3a - (μ̄ + μA / Real.sqrt (n : ℝ))
        = (c1 * (2 * massLam ^ 2 / (t n) ^ 3) + c1 * (-1 / (2 * (t n) ^ 2)))
          + c2 * (6 * massLam ^ 2 / (t n) ^ 4)
          + c3 * (24 * massLam ^ 2 / (t n) ^ 5)
          - μ̄ - μA / Real.sqrt (n : ℝ) := by
      dsimp [M1a, M2a, M3a]; ring
    _ = (μ̄ + (-(3 / (4 * massLam ^ 2)) / Real.sqrt (n : ℝ)))
      + ((45 / (4 * massLam ^ 2)) / Real.sqrt (n : ℝ))
      + ((9 / (massLam ^ 3)) / (n : ℝ) - (9 / (massLam ^ 2)) / Real.sqrt (n : ℝ))
      - μ̄ - μA / Real.sqrt (n : ℝ) := by
      rw [hid_c1_leading, hid_c1_correction, hid_c2_leading, hid_c3_leading]
    _ = (μ̄ - μ̄)
      + ((-(3 / (4 * massLam ^ 2)) + (45 / (4 * massLam ^ 2)) - (9 / (massLam ^ 2))) / Real.sqrt (n : ℝ)
          - μA / Real.sqrt (n : ℝ))
      + (9 / (massLam ^ 3)) / (n : ℝ) := by ring
    _ = (0)
      + ((6 / (4 * massLam ^ 2)) / Real.sqrt (n : ℝ) - μA / Real.sqrt (n : ℝ))
      + (9 / (massLam ^ 3)) / (n : ℝ) := by ring
    _ = (μA / Real.sqrt (n : ℝ) - μA / Real.sqrt (n : ℝ))
      + (9 / (massLam ^ 3)) / (n : ℝ) := by
      rw [show (6 / (4 * massLam ^ 2)) = μA by dsimp [μA]; ring, sub_self]
    _ = (9 / (massLam ^ 3)) / (n : ℝ) := by ring
  -- Now: |c1·M1 + c2·M2 + c3·M3 + c4·M4 − (μ̄ + μA/√n)|
  -- = |c1·(M1−M1a) + c2·(M2−M2a) + c3·(M3−M3a) + c4·M4 + hcancel|
  have hrewrite : (c1 * sigmaMoment 1 (t n) + c2 * sigmaMoment 2 (t n) + c3 * sigmaMoment 3 (t n)
      + c4 * sigmaMoment 4 (t n)) - (μ̄ + μA / Real.sqrt (n : ℝ))
      = c1 * (sigmaMoment 1 (t n) - M1a)
      + c2 * (sigmaMoment 2 (t n) - M2a)
      + c3 * (sigmaMoment 3 (t n) - M3a)
      + c4 * sigmaMoment 4 (t n) + hcancel := by
    rw [hcancel]; ring
  rw [hrewrite]
  -- triangle inequality
  calc |c1 * (sigmaMoment 1 (t n) - M1a) + c2 * (sigmaMoment 2 (t n) - M2a)
        + c3 * (sigmaMoment 3 (t n) - M3a) + c4 * sigmaMoment 4 (t n)
        + (9 / (massLam ^ 3)) / (n : ℝ)|
      ≤ |c1 * (sigmaMoment 1 (t n) - M1a)|
        + |c2 * (sigmaMoment 2 (t n) - M2a)|
        + |c3 * (sigmaMoment 3 (t n) - M3a)|
        + |c4 * sigmaMoment 4 (t n)|
        + |(9 / (massLam ^ 3)) / (n : ℝ)| := by
    refine le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (abs_add_le (abs_add_le _ _)
      (add_le_add (abs_add_le _ _) (abs_add_le _ _))))
    -- using nested abs_add_le to break 5 terms
  _ = |c1| * |sigmaMoment 1 (t n) - M1a|
      + |c2| * |sigmaMoment 2 (t n) - M2a|
      + |c3| * |sigmaMoment 3 (t n) - M3a|
      + |c4| * sigmaMoment 4 (t n)
      + (9 / (massLam ^ 3)) / (n : ℝ) := by
    simp [abs_mul, abs_of_pos (by positivity : 0 < 9 / massLam ^ 3),
      abs_of_nonneg (sigmaMoment_nonneg 4 (t n) htpos)]
  _ ≤ |c1| * (K1 / (t n))
      + |c2| * (K2 / (t n) ^ 3)
      + |c3| * (K3 / (t n) ^ 4)
      + |c4| * sigmaMoment 4 (t n)
      + (9 / (massLam ^ 3)) / (n : ℝ) := by
    refine add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hM1n (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hM2n (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left hM3n (abs_nonneg _))) (add_le_add (le_refl _) (le_refl _))
  _ ≤ |c1| * (K1 / (t n))
      + |c2| * (K2 / (t n) ^ 3)
      + |c3| * (K3 / (t n) ^ 4)
      + |c4| * (K4 / (t n) ^ 6)
      + (9 / (massLam ^ 3)) / (n : ℝ) := by
    refine add_le_add (le_refl _) (add_le_add (le_refl _) (add_le_add (le_refl _) (add_le_add
      (mul_le_mul_of_nonneg_left hM4n (abs_nonneg _)) (le_refl _))))
  _ ≤ (K1 * C1c + K2 * C2c + K3 * C3c + K4 * C4c + (9 / massLam ^ 3)) / (n : ℝ) := by
    -- each |cⱼ|/(t n)^kⱼ ≤ Cⱼc / n
    have hc1_bound : |c1| / (t n) = C1c / (n : ℝ) := by
      dsimp [c1, C1c, t]; field_simp; ring
    have hc2_bound : |c2| / (t n) ^ 3 = C2c / (n : ℝ) := by
      dsimp [c2, C2c, t]; field_simp; ring
    have hc3_bound : |c3| / (t n) ^ 4 ≤ C3c / (n : ℝ) := by
      dsimp [c3, C3c, t]
      have hpos1 : 0 ≤ 3 / (8 * (n : ℝ)^2 * Real.sqrt (n:ℝ)^3) := by positivity
      have hpos2 : 0 ≤ 3*C/(16*(n:ℝ)^3) := by positivity
      have habs : |c3| ≤ 3 / (8 * (n : ℝ)^2 * Real.sqrt (n:ℝ)^3) + 3*C/(16*(n:ℝ)^3) := by
        rw [abs_le]; constructor <;> nlinarith
      calc |c3| / (t n)^4 ≤ (3 / (8 * (n : ℝ)^2 * Real.sqrt (n:ℝ)^3) + 3*C/(16*(n:ℝ)^3)) / (t n)^4 :=
          (div_le_div_right (by positivity)).mpr habs
        _ = (3/(8*massLam^4) + 3*C/(16*massLam^4)) / (n:ℝ) := by
          dsimp [t]; field_simp; ring
        _ = C3c / (n : ℝ) := rfl
    have hc4_bound : |c4| / (t n) ^ 6 = C4c / (n : ℝ) := by
      dsimp [c4, C4c, t]; field_simp; ring
    rw [show |c1| * (K1 / (t n)) = K1 * (|c1| / (t n)) by ring,
      show |c2| * (K2 / (t n)^3) = K2 * (|c2| / (t n)^3) by ring,
      show |c3| * (K3 / (t n)^4) = K3 * (|c3| / (t n)^4) by ring,
      show |c4| * (K4 / (t n)^6) = K4 * (|c4| / (t n)^6) by ring]
    rw [hc1_bound, hc2_bound, hc4_bound]
    have hc3 : K3 * (|c3| / (t n)^4) ≤ K3 * (C3c / (n:ℝ)) :=
      mul_le_mul_of_nonneg_left hc3_bound hK3pos.le
    have hterm : K1 * (C1c / (n:ℝ)) + K2 * (C2c / (n:ℝ)) + K3 * (|c3| / (t n)^4) + K4 * (C4c / (n:ℝ))
        + (9 / massLam ^ 3) / (n : ℝ)
        ≤ K1 * (C1c / (n:ℝ)) + K2 * (C2c / (n:ℝ)) + K3 * (C3c / (n:ℝ)) + K4 * (C4c / (n:ℝ))
        + (9 / massLam ^ 3) / (n : ℝ) := by nlinarith
    refine le_trans hterm ?_
    ring
  _ = K_total / (n : ℝ) := rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
