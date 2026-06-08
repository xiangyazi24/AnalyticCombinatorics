import AnalyticCombinatorics.Ch8.Partitions.QVTelescope

/-!
# R7 Fact B via Doeblin: per-step fourth-moment drift bound

For a mean-preserving kernel with bounded increments `b`, the one-step fourth-moment drift is controlled
by the second moment:

  `∑_z K x z (D z)⁴ − (D x)⁴ ≤ 8 b² (D x)² + 3 b⁴`.

Telescoped (with the upper quadratic variation `E[D_t²] ≤ D₀² + b² t`) this gives the BDG-type bound
`E[D_T⁴] ≤ C b⁴ T²`, the fourth moment feeding the Paley–Zygmund anti-concentration `E|D_T| ≥ c√T`.
Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **Per-step fourth-moment drift bound.** -/
theorem fourth_drift_le (K : ι → ι → ℝ) (D : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b) (x : ι)
    (hKnn : ∀ z, 0 ≤ K x z) (hKsum : ∑ z, K x z = 1) (hmart : ∑ z, K x z * D z = D x)
    (hbinc : ∀ z, K x z ≠ 0 → |D z - D x| ≤ b) :
    (∑ z, K x z * (D z) ^ 4) - (D x) ^ 4 ≤ 8 * b ^ 2 * (D x) ^ 2 + 3 * b ^ 4 := by
  set lv := ∑ z, K x z * (D z - D x) ^ 2 with hlvdef
  set M3 := ∑ z, K x z * (D z - D x) ^ 3 with hM3def
  set M4 := ∑ z, K x z * (D z - D x) ^ 4 with hM4def
  -- mean-zero increment
  have hmean0 : (∑ z, K x z * (D z - D x)) = 0 := by
    have h : ∀ z, K x z * (D z - D x) = K x z * D z - D x * K x z := fun z => by ring
    rw [Finset.sum_congr rfl (fun z _ => h z), Finset.sum_sub_distrib, ← Finset.mul_sum, hmart, hKsum]
    ring
  -- binomial expansion of the fourth moment
  have hexp : (∑ z, K x z * (D z) ^ 4) = (D x) ^ 4 + 6 * (D x) ^ 2 * lv + 4 * (D x) * M3 + M4 := by
    have key : ∀ z, K x z * (D z) ^ 4
        = (D x) ^ 4 * K x z + 4 * (D x) ^ 3 * (K x z * (D z - D x))
          + 6 * (D x) ^ 2 * (K x z * (D z - D x) ^ 2)
          + 4 * (D x) * (K x z * (D z - D x) ^ 3) + K x z * (D z - D x) ^ 4 := fun z => by ring
    rw [Finset.sum_congr rfl (fun z _ => key z)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hKsum, hmean0,
      hlvdef, hM3def, hM4def]
    ring
  -- moment bounds from the increment bound b
  have hlv_le : lv ≤ b ^ 2 := by
    rw [hlvdef]
    calc ∑ z, K x z * (D z - D x) ^ 2 ≤ ∑ z, K x z * b ^ 2 := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hz : K x z = 0
          · rw [hz, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ (hKnn z)
            have := hbinc z hz
            nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), this]
      _ = b ^ 2 := by rw [← Finset.sum_mul, hKsum, one_mul]
  have hlv_nn : 0 ≤ lv := by
    rw [hlvdef]; exact Finset.sum_nonneg (fun z _ => mul_nonneg (hKnn z) (sq_nonneg _))
  have hM4_le : M4 ≤ b ^ 2 * lv := by
    rw [hM4def, hlvdef, Finset.mul_sum]
    refine Finset.sum_le_sum (fun z _ => ?_)
    by_cases hz : K x z = 0
    · rw [hz, zero_mul]; positivity
    · have hb := hbinc z hz
      have hsq : (D z - D x) ^ 2 ≤ b ^ 2 := by nlinarith [abs_nonneg (D z - D x), sq_abs (D z - D x), hb]
      have h4 : (D z - D x) ^ 4 ≤ b ^ 2 * (D z - D x) ^ 2 := by nlinarith [sq_nonneg (D z - D x), hsq]
      calc K x z * (D z - D x) ^ 4 ≤ K x z * (b ^ 2 * (D z - D x) ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (hKnn z)
        _ = b ^ 2 * (K x z * (D z - D x) ^ 2) := by ring
  have hM3_abs : |M3| ≤ b * lv := by
    rw [hM3def, hlvdef, Finset.mul_sum]
    calc |∑ z, K x z * (D z - D x) ^ 3| ≤ ∑ z, |K x z * (D z - D x) ^ 3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, b * (K x z * (D z - D x) ^ 2) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          by_cases hz : K x z = 0
          · rw [hz, zero_mul]; simp
          · have hb := hbinc z hz
            rw [abs_mul, abs_of_nonneg (hKnn z)]
            have hcube : |(D z - D x) ^ 3| ≤ b * (D z - D x) ^ 2 := by
              rw [show (D z - D x) ^ 3 = (D z - D x) * (D z - D x) ^ 2 by ring, abs_mul,
                abs_of_nonneg (sq_nonneg (D z - D x))]
              exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
            calc K x z * |(D z - D x) ^ 3| ≤ K x z * (b * (D z - D x) ^ 2) :=
                  mul_le_mul_of_nonneg_left hcube (hKnn z)
              _ = b * (K x z * (D z - D x) ^ 2) := by ring
  -- assemble
  rw [hexp]
  have hM3lo : -(b * lv) ≤ M3 := (abs_le.1 hM3_abs).1
  have hM3hi : M3 ≤ b * lv := (abs_le.1 hM3_abs).2
  -- 4 D x M3 ≤ 2 (D x)² b² + 2 b⁴ via |·| and AM-GM
  have hcross : 4 * (D x) * M3 ≤ 2 * (D x) ^ 2 * b ^ 2 + 2 * b ^ 4 := by
    have hbnd : (D x) * M3 ≤ |D x| * (b * lv) := by
      calc (D x) * M3 ≤ |(D x) * M3| := le_abs_self _
        _ = |D x| * |M3| := abs_mul _ _
        _ ≤ |D x| * (b * lv) := mul_le_mul_of_nonneg_left hM3_abs (abs_nonneg _)
    have hlb : |D x| * (b * lv) ≤ |D x| * b ^ 3 := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [hlv_le, hbnn, hlv_nn]
    nlinarith [hbnd, hlb, sq_nonneg (|D x| - b), sq_abs (D x), abs_nonneg (D x), hbnn,
      mul_nonneg (show (0:ℝ) ≤ 2 * b ^ 2 by positivity) (sq_nonneg (|D x| - b))]
  nlinarith [hlv_le, hlv_nn, hM4_le, sq_nonneg (D x), hbnn, hcross,
    mul_le_mul_of_nonneg_left hlv_le (show (0:ℝ) ≤ 6 * (D x) ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hlv_le (show (0:ℝ) ≤ b ^ 2 by positivity)]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
