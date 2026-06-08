import AnalyticCombinatorics.Ch8.Partitions.QVEta
import AnalyticCombinatorics.Ch8.Partitions.TanakaEta
import AnalyticCombinatorics.Ch8.Partitions.ProbMoments

/-!
# R7 Fact B via Doeblin: η-robust occupation capstone

For the η-approximate-martingale Erdős rank-difference walk, the window occupation is still unbounded.
The fourth moment is bounded *trivially* by `R⁴` (since `|D| ≤ R`), so Paley–Zygmund with the linear
lower QV `E[D_T²] ≥ (v₀−2Rη)·T` gives `(E|D_T|)² ≥ ((v₀−2Rη)T)³/R⁴ → ∞` (cubic) — no re-derived
fourth-moment bound needed.  Combined with the η-robust Tanaka bound `occ ≥ (E|D_T| − E|D_0| − ηT)/b`,
and since `E|D_T| ~ T^{3/2} ≫ ηT`, the occupation exceeds any target.  Deterministic finite-sum.
Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

/-- Trivial fourth-moment bound from the range. -/
lemma fourth_moment_le_R4 (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (R : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hμ0nn : ∀ x, 0 ≤ μ0 x)
    (hμ0sum : ∑ x, μ0 x = 1) (hR : ∀ x, |D x| ≤ R) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ R ^ 4 := by
  calc (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ ∑ x, distPow K μ0 T x * R ^ 4 := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (distPow_nonneg K μ0 hKnn hμ0nn T x)
        have hd4 : (D x) ^ 4 = |D x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        rw [hd4]; exact pow_le_pow_left₀ (abs_nonneg _) (hR x) 4
    _ = R ^ 4 := by rw [← Finset.sum_mul, distPow_sum K μ0 hKsum hμ0sum T, one_mul]

/-- **η-robust occupation is unbounded.** -/
theorem occupation_unbounded_eta (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b η R v0 : ℝ)
    (hb0 : 0 < b) (hηnn : 0 ≤ η) (hRpos : 0 < R) (hv' : 0 < v0 - 2 * R * η)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hmarteta : ∀ x, |(∑ z, K x z * D z) - D x| ≤ η) (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hlvge : ∀ x, v0 ≤ locVar K D x)
    (hR : ∀ x, |D x| ≤ R) (Mtarget : ℝ) :
    ∃ T : ℕ, Mtarget ≤ ∑ t ∈ Finset.range T,
        ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0) := by
  set v' := v0 - 2 * R * η with hv'def
  set E0abs := ∑ x, μ0 x * |D x| with hE0abs
  have hE0abs_nn : 0 ≤ E0abs :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (abs_nonneg _))
  set M := b * Mtarget + E0abs with hMdef
  -- choose horizon
  set T : ℕ := max 1 (max ⌈4 * M ^ 2 * R ^ 4 / v' ^ 3⌉₊ ⌈4 * η ^ 2 * R ^ 4 / v' ^ 3⌉₊) with hTdef
  have hTge1 : (1 : ℝ) ≤ T := by exact_mod_cast le_max_left 1 _
  have hv3 : 0 < v' ^ 3 := by positivity
  have hT1 : 4 * M ^ 2 * R ^ 4 / v' ^ 3 ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) (le_max_right 1 _))
  have hT2 : 4 * η ^ 2 * R ^ 4 / v' ^ 3 ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right 1 _))
  have hTM : 4 * M ^ 2 * R ^ 4 ≤ v' ^ 3 * T := by
    rw [div_le_iff₀ hv3] at hT1; linarith [hT1]
  have hTη : 4 * η ^ 2 * R ^ 4 ≤ v' ^ 3 * T := by
    rw [div_le_iff₀ hv3] at hT2; linarith [hT2]
  refine ⟨T, ?_⟩
  set A := ∑ x, distPow K μ0 T x * (D x) ^ 2 with hAdef
  set B := ∑ x, distPow K μ0 T x * |D x| with hBdef
  set Dq := ∑ x, distPow K μ0 T x * (D x) ^ 4 with hDqdef
  have hBnn : 0 ≤ B :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (distPow_nonneg K μ0 hKnn hμ0nn T x) (abs_nonneg _))
  -- lower QV
  have hlow : v' * T ≤ A := by
    have h := sq_moment_ge_eta K D μ0 v0 η R hKnn hKsum hmarteta hμ0nn hμ0sum hlvge hR T
    have hE0 : (0 : ℝ) ≤ ∑ x, μ0 x * (D x) ^ 2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (sq_nonneg _))
    rw [hAdef]; rw [← hv'def] at h; linarith [h, hE0]
  -- fourth moment trivial bound
  have hDq : Dq ≤ R ^ 4 := by
    rw [hDqdef]; exact fourth_moment_le_R4 K D μ0 R hKnn hKsum hμ0nn hμ0sum hR T
  -- Paley–Zygmund
  have hpz : A ^ 3 ≤ B ^ 2 * Dq := by
    have h := mean_sq_cubed_le (Finset.univ) (distPow K μ0 T) D
      (fun x _ => distPow_nonneg K μ0 hKnn hμ0nn T x)
    rw [hAdef, hBdef, hDqdef]; exact h
  -- key: (M + ηT)² · R⁴ ≤ v'³ · T³
  have hR4 : 0 < R ^ 4 := by positivity
  have hkey : (M + η * T) ^ 2 * R ^ 4 ≤ v' ^ 3 * (T : ℝ) ^ 3 := by
    have hsq : (M + η * (T : ℝ)) ^ 2 ≤ 2 * M ^ 2 + 2 * η ^ 2 * (T : ℝ) ^ 2 := by nlinarith [sq_nonneg (M - η * (T : ℝ))]
    have hTcube : (T : ℝ) ≤ (T : ℝ) ^ 3 := by nlinarith [hTge1]
    nlinarith [hsq, hTcube, hTM, hTη, mul_nonneg hR4.le (sq_nonneg ((T:ℝ))), hTge1,
      mul_le_mul_of_nonneg_right hTM (sq_nonneg (T:ℝ)), hv3, hRpos]
  -- chain: (M+ηT)²·R⁴ ≤ v'³T³ ≤ A³ ≤ B²·Dq ≤ B²·R⁴, so M+ηT ≤ B
  have hcube : (v' * T) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hlow 3
  have hchain : (M + η * T) ^ 2 * R ^ 4 ≤ B ^ 2 * R ^ 4 := by
    calc (M + η * T) ^ 2 * R ^ 4 ≤ v' ^ 3 * (T : ℝ) ^ 3 := hkey
      _ = (v' * T) ^ 3 := by ring
      _ ≤ A ^ 3 := hcube
      _ ≤ B ^ 2 * Dq := hpz
      _ ≤ B ^ 2 * R ^ 4 := mul_le_mul_of_nonneg_left hDq (sq_nonneg B)
  have hMB : M + η * T ≤ B := by
    have hsq : (M + η * T) ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_right hchain hR4
    exact le_of_pow_le_pow_left₀ (by norm_num) hBnn hsq
  -- η-robust Tanaka : B − E0abs ≤ b·occ + η·T
  have htan := occupation_ge_tanaka_eta K D b η hb0.le hηnn μ0 hμ0nn hKnn hKsum hμ0sum hmarteta hbinc T
  rw [← hBdef, ← hE0abs] at htan
  have hbm : b * Mtarget
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) := by
    rw [hMdef] at hMB; linarith [htan, hMB]
  exact le_of_mul_le_mul_left hbm hb0

end AnalyticCombinatorics.Ch8.Partitions.Erdos
