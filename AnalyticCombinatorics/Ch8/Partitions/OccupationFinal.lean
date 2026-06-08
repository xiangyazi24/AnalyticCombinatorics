import AnalyticCombinatorics.Ch8.Partitions.OccupationAssembly
import AnalyticCombinatorics.Ch8.Partitions.TanakaTelescope
import AnalyticCombinatorics.Ch8.Partitions.ProbMoments

/-!
# R7 Fact B via Doeblin: the occupation lower bound is unbounded

For a mean-preserving, bounded-increment, uniformly-positive-local-variance walk, the mean absolute
displacement `E|D_T|` is unbounded in `T` (Paley–Zygmund anti-concentration with `E[D_T²] ≥ v₀T` and
`E[D_T⁴] ≤ C·T²`), and hence (Tanaka, brick 86) the cumulative window occupation is unbounded.  This is
the abstract form of the recurrence content: the residual coupling spends arbitrarily much time in the
window, so coalescence eventually exceeds any threshold `1/δ`.  Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- **`E|D_T|` is unbounded.** -/
theorem abs_mean_unbounded (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b v0 : ℝ)
    (hb0 : 0 < b) (hv0 : 0 < v0) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hmart : ∀ x, ∑ z, K x z * D z = D x) (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hlvge : ∀ x, v0 ≤ locVar K D x) (M : ℝ) :
    ∃ T : ℕ, M ≤ ∑ x, distPow K μ0 T x * |D x| := by
  set E0sq := ∑ x, μ0 x * (D x) ^ 2 with hE0sq
  set E0q := ∑ x, μ0 x * (D x) ^ 4 with hE0q
  have hE0sq_nn : 0 ≤ E0sq := Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (sq_nonneg _))
  have hE0q_nn : 0 ≤ E0q := Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (by positivity))
  set C := E0q + 8 * b ^ 2 * E0sq + 11 * b ^ 4 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  -- choose horizon T ≥ max(1, M²C/v₀³)
  set Treal := M ^ 2 * C / v0 ^ 3 with hTreal
  set T : ℕ := max 1 ⌈Treal⌉₊ with hTdef
  have hTge1 : (1 : ℝ) ≤ T := by exact_mod_cast le_max_left 1 ⌈Treal⌉₊
  have hTrge : Treal ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil Treal) (by exact_mod_cast le_max_right 1 ⌈Treal⌉₊)
  refine ⟨T, ?_⟩
  set A := ∑ x, distPow K μ0 T x * (D x) ^ 2 with hAdef
  set B := ∑ x, distPow K μ0 T x * |D x| with hBdef
  set Dq := ∑ x, distPow K μ0 T x * (D x) ^ 4 with hDqdef
  have hBnn : 0 ≤ B := Finset.sum_nonneg (fun x _ => mul_nonneg (distPow_nonneg K μ0 hKnn hμ0nn T x) (abs_nonneg _))
  -- lower QV : v₀T ≤ A
  have hlow : v0 * T ≤ A := by
    have h := sq_moment_ge K D μ0 v0 hKnn hKsum hmart hμ0nn hμ0sum hlvge T
    rw [← hE0sq, ← hAdef] at h
    linarith [h, hE0sq_nn]
  have hAnn : 0 ≤ A := le_trans (by positivity) hlow
  -- 4th moment : Dq ≤ C T²
  have hhi : Dq ≤ C * (T : ℝ) ^ 2 := by
    have h4 := fourth_moment_le_quadratic K D μ0 b hb0.le hKnn hKsum hmart hbinc hμ0nn hμ0sum T
    rw [← hE0q, ← hE0sq, ← hDqdef] at h4
    rw [hCdef]
    have hTT : (0 : ℝ) ≤ (T : ℝ) ^ 2 - (T : ℝ) := by nlinarith [hTge1]
    have hT21 : (0 : ℝ) ≤ (T : ℝ) ^ 2 - 1 := by nlinarith [hTge1]
    nlinarith [h4, mul_nonneg hE0q_nn hT21,
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8 * b ^ 2) hE0sq_nn) hTT,
      mul_nonneg (by positivity : (0:ℝ) ≤ 3 * b ^ 4) hTT]
  -- Paley–Zygmund : A³ ≤ B² · Dq
  have hpz : A ^ 3 ≤ B ^ 2 * Dq := by
    have h := mean_sq_cubed_le (Finset.univ) (distPow K μ0 T) D
      (fun x _ => distPow_nonneg K μ0 hKnn hμ0nn T x)
    rw [hAdef, hBdef, hDqdef]; exact h
  -- v₀³ T ≥ M² C
  have hv3 : 0 < v0 ^ 3 := by positivity
  have hkey : M ^ 2 * C ≤ v0 ^ 3 * (T : ℝ) := by
    calc M ^ 2 * C = v0 ^ 3 * Treal := by rw [hTreal]; field_simp
      _ ≤ v0 ^ 3 * (T : ℝ) := mul_le_mul_of_nonneg_left hTrge hv3.le
  -- chain: B²·C·T² ≥ B²·Dq ≥ A³ ≥ (v₀T)³ = v₀³T³ ≥ M²C·T²
  have hcube : (v0 * T) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hlow 3
  have hCT2 : 0 < C * (T : ℝ) ^ 2 := by positivity
  have hBDq : B ^ 2 * Dq ≤ B ^ 2 * (C * (T : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hhi (sq_nonneg B)
  have hMCT : M ^ 2 * (C * (T : ℝ) ^ 2) ≤ v0 ^ 3 * (T : ℝ) ^ 3 := by nlinarith [hkey, hTge1]
  have hchain : M ^ 2 * (C * (T : ℝ) ^ 2) ≤ B ^ 2 * (C * (T : ℝ) ^ 2) := by
    calc M ^ 2 * (C * (T : ℝ) ^ 2) ≤ v0 ^ 3 * (T : ℝ) ^ 3 := hMCT
      _ = (v0 * T) ^ 3 := by ring
      _ ≤ A ^ 3 := hcube
      _ ≤ B ^ 2 * Dq := hpz
      _ ≤ B ^ 2 * (C * (T : ℝ) ^ 2) := hBDq
  have hM2B2 : M ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_right hchain hCT2
  by_cases hM : M ≤ 0
  · exact le_trans hM hBnn
  · push_neg at hM
    exact le_of_pow_le_pow_left₀ (by norm_num) hBnn hM2B2

/-- **The cumulative window occupation is unbounded.** -/
theorem occupation_unbounded (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b v0 : ℝ)
    (hb0 : 0 < b) (hv0 : 0 < v0) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hmart : ∀ x, ∑ z, K x z * D z = D x) (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hlvge : ∀ x, v0 ≤ locVar K D x) (Mtarget : ℝ) :
    ∃ T : ℕ, Mtarget ≤ ∑ t ∈ Finset.range T,
        ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0) := by
  obtain ⟨T, hT⟩ := abs_mean_unbounded K D μ0 b v0 hb0 hv0 hKnn hKsum hmart hbinc hμ0nn hμ0sum hlvge
    (b * Mtarget + ∑ x, μ0 x * |D x|)
  refine ⟨T, ?_⟩
  have htan := occupation_ge_tanaka K D b hb0.le μ0 hμ0nn hKnn hKsum hmart hbinc T
  -- htan : E|D_T| − E|D_0| ≤ b · occ ; hT : b·Mtarget + E|D_0| ≤ E|D_T|
  have hbm : b * Mtarget
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) := by
    linarith [htan, hT]
  exact le_of_mul_le_mul_left hbm hb0

end AnalyticCombinatorics.Ch8.Partitions.Erdos
