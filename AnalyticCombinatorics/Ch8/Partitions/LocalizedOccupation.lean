import AnalyticCombinatorics.Ch8.Partitions.LocalizedQV
import AnalyticCombinatorics.Ch8.Partitions.LocalizedTanaka
import AnalyticCombinatorics.Ch8.Partitions.OccupationEta
import AnalyticCombinatorics.Ch8.Partitions.ProbMoments

/-!
# R7 Fact B via Doeblin: localized occupation is unbounded (conditioned-walk version)

`occupation_unbounded_eta` re-derived with the LOCALIZED hypotheses the conditioned residual walk
satisfies: one-sided QV (`D·e ≥ −Rη`, brick 99) + off-window Tanaka drift (brick 100), plus uniform
local-variance `locVar ≥ v₀` (holds for the conditioned walk: removing the central coalescing outcomes
only increases the spread).  Paley–Zygmund with `E[D_M²] ≥ (v₀−2Rη)M` and `E[D_M⁴] ≤ R⁴` gives
`E|D_M| ~ M^{3/2} → ∞`; the localized Tanaka bound then forces the window occupation past any target.
Deterministic finite-sum.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **Localized occupation is unbounded.** -/
theorem occupation_unbounded_loc (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ) (b η R v0 : ℝ)
    (hb0 : 0 < b) (hηnn : 0 ≤ η) (hRpos : 0 < R) (hv' : 0 < v0 - 2 * R * η)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hlvge : ∀ x, v0 ≤ locVar K D x)
    (hcross : ∀ x, -(R * η) ≤ (D x) * ((∑ z, K x z * D z) - D x))
    (hdrift_off : ∀ x, b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1) (hR : ∀ x, |D x| ≤ R) (Mtarget : ℝ) :
    ∃ M : ℕ, Mtarget ≤ ∑ t ∈ Finset.range M,
        ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0) := by
  set v' := v0 - 2 * R * η with hv'def
  set E0abs := ∑ x, μ0 x * |D x| with hE0abs
  have hE0abs_nn : 0 ≤ E0abs :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (abs_nonneg _))
  set M0 := b * Mtarget + E0abs with hM0def
  set T : ℕ := max 1 (max ⌈4 * M0 ^ 2 * R ^ 4 / v' ^ 3⌉₊ ⌈4 * η ^ 2 * R ^ 4 / v' ^ 3⌉₊) with hTdef
  have hTge1 : (1 : ℝ) ≤ T := by exact_mod_cast le_max_left 1 _
  have hv3 : 0 < v' ^ 3 := by positivity
  have hT1 : 4 * M0 ^ 2 * R ^ 4 / v' ^ 3 ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) (le_max_right 1 _))
  have hT2 : 4 * η ^ 2 * R ^ 4 / v' ^ 3 ≤ (T : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right 1 _))
  have hTM : 4 * M0 ^ 2 * R ^ 4 ≤ v' ^ 3 * T := by rw [div_le_iff₀ hv3] at hT1; linarith [hT1]
  have hTη : 4 * η ^ 2 * R ^ 4 ≤ v' ^ 3 * T := by rw [div_le_iff₀ hv3] at hT2; linarith [hT2]
  refine ⟨T, ?_⟩
  set A := ∑ x, distPow K μ0 T x * (D x) ^ 2 with hAdef
  set B := ∑ x, distPow K μ0 T x * |D x| with hBdef
  set Dq := ∑ x, distPow K μ0 T x * (D x) ^ 4 with hDqdef
  have hBnn : 0 ≤ B :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (distPow_nonneg K μ0 hKnn hμ0nn T x) (abs_nonneg _))
  -- one-sided lower QV
  have hlow : v' * T ≤ A := by
    have h := sq_moment_ge_onesided P hPnn hPmass K D μ0 v0 η R hKnn hKsum hμ0nn hμ0sum
      hlvge hcross T
    have hE0 : (0 : ℝ) ≤ ∑ x, μ0 x * (D x) ^ 2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (hμ0nn x) (sq_nonneg _))
    rw [hAdef]; rw [← hv'def] at h; linarith [h, hE0]
  have hDq : Dq ≤ R ^ 4 := by
    rw [hDqdef]; exact fourth_moment_le_R4 K D μ0 R hKnn hKsum hμ0nn hμ0sum hR T
  have hpz : A ^ 3 ≤ B ^ 2 * Dq := by
    have h := mean_sq_cubed_le (Finset.univ) (distPow K μ0 T) D
      (fun x _ => distPow_nonneg K μ0 hKnn hμ0nn T x)
    rw [hAdef, hBdef, hDqdef]; exact h
  have hR4 : 0 < R ^ 4 := by positivity
  have hkey : (M0 + η * T) ^ 2 * R ^ 4 ≤ v' ^ 3 * (T : ℝ) ^ 3 := by
    have hsq : (M0 + η * (T : ℝ)) ^ 2 ≤ 2 * M0 ^ 2 + 2 * η ^ 2 * (T : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (M0 - η * (T : ℝ))]
    have hTcube : (T : ℝ) ≤ (T : ℝ) ^ 3 := by nlinarith [hTge1]
    nlinarith [hsq, hTcube, hTM, hTη, mul_nonneg hR4.le (sq_nonneg ((T:ℝ))), hTge1,
      mul_le_mul_of_nonneg_right hTM (sq_nonneg (T:ℝ)), hv3, hRpos]
  have hcube : (v' * T) ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (by positivity) hlow 3
  have hchain : (M0 + η * T) ^ 2 * R ^ 4 ≤ B ^ 2 * R ^ 4 := by
    calc (M0 + η * T) ^ 2 * R ^ 4 ≤ v' ^ 3 * (T : ℝ) ^ 3 := hkey
      _ = (v' * T) ^ 3 := by ring
      _ ≤ A ^ 3 := hcube
      _ ≤ B ^ 2 * Dq := hpz
      _ ≤ B ^ 2 * R ^ 4 := mul_le_mul_of_nonneg_left hDq (sq_nonneg B)
  have hMB : M0 + η * T ≤ B := by
    have hsq : (M0 + η * T) ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_right hchain hR4
    exact le_of_pow_le_pow_left₀ (by norm_num) hBnn hsq
  -- localized Tanaka : B − E0abs ≤ b·occ + η·T
  have htan := occupation_ge_tanaka_loc P hPnn hPmass K D b η hb0.le hηnn μ0 hμ0nn hKnn hKsum
    hμ0sum hdrift_off hbinc T
  rw [← hBdef, ← hE0abs] at htan
  have hbm : b * Mtarget
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) := by
    rw [hM0def] at hMB; nlinarith [htan, hMB]
  exact le_of_mul_le_mul_left hbm hb0

end AnalyticCombinatorics.Ch8.Partitions.Erdos
