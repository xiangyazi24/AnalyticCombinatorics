import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOne

/-!
# Mass-rate campaign: crude power bounds for the Lambert moments

`Σ' m^j x^m ≤ j!/(1−x)^{j+1}` (via `m^j ≤ j!·C(m+j,j)` and the choose-geometric sum), hence
`M_r(t) ≤ (r+2)!·2^{r+3}/t^{r+3}` on `0 < t ≤ 1` — the tail-control input for the `r = 2,3,4`
moments in the §5–7 kernel-mass assembly.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `Σ' m^j x^m ≤ j!/(1−x)^{j+1}` for `0 ≤ x < 1`. -/
lemma tsum_pow_mul_geometric_le (j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' m : ℕ, (m : ℝ) ^ j * x ^ m ≤ (j.factorial : ℝ) / (1 - x) ^ (j + 1) := by
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hsum1 : Summable (fun m : ℕ => (m : ℝ) ^ j * x ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j hxn
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one j hxn
  have hsum2 : Summable
      (fun m : ℕ => (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m) := by
    have hbase := hchoose.summable.mul_left (j.factorial : ℝ)
    refine hbase.congr fun m => ?_
    ring
  have hle : ∀ m : ℕ, (m : ℝ) ^ j * x ^ m
      ≤ (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m := by
    intro m
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0 m)
    have hnat : m ^ j ≤ j.factorial * (m + j).choose j := by
      have h1 : (m + 1) ^ j ≤ (m + j).descFactorial j := by
        have h := Nat.pow_sub_le_descFactorial (m + j) j
        have harg : m + j + 1 - j = m + 1 := by omega
        rwa [harg] at h
      have h2 : m ^ j ≤ (m + 1) ^ j := Nat.pow_le_pow_left (Nat.le_succ m) j
      have h3 : (m + j).descFactorial j = j.factorial * (m + j).choose j := by
        have hd := Nat.factorial_dvd_descFactorial (m + j) j
        rw [Nat.choose_eq_descFactorial_div_factorial, Nat.mul_div_cancel' hd]
      exact le_trans h2 (le_trans h1 (le_of_eq h3))
    exact_mod_cast hnat
  have hmain := hsum1.tsum_le_tsum hle hsum2
  refine le_trans hmain (le_of_eq ?_)
  have hfac : ∀ m : ℕ, (j.factorial : ℝ) * (((m + j).choose j : ℕ) : ℝ) * x ^ m
      = (j.factorial : ℝ) * ((((m + j).choose j : ℕ) : ℝ) * x ^ m) := by
    intro m
    ring
  rw [tsum_congr hfac, tsum_mul_left, hchoose.tsum_eq]
  rw [mul_one_div]

/-- `1 − e^{−t} ≥ t/2` on `0 < t ≤ 1`. -/
lemma one_sub_exp_neg_ge_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hpos : (0:ℝ) < 1 + t := by linarith
  have h3 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le hpos
    linarith
  have h4 : 1 / (1 + t) ≤ 1 - t / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-- **Crude moment power bound** (§5–7 tail input):
`M_r(t) ≤ (r+2)!·2^{r+3}/t^{r+3}` on `0 < t ≤ 1`. -/
lemma sigmaMoment_le_power (r : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    sigmaMoment r t ≤ ((r + 2).factorial : ℝ) * 2 ^ (r + 3) / t ^ (r + 3) := by
  set x := Real.exp (-t) with hxdef
  have hx0 : (0:ℝ) ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    rw [hxdef, Real.exp_lt_one_iff]
    linarith
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  -- step 1: σ(m) ≤ m² termwise
  have hsumRHS : Summable (fun m : ℕ => (m : ℝ) ^ (r + 2) * x ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r + 2) hxn
  have hsumLHS : Summable (fun m : ℕ =>
      if m = 0 then (0:ℝ) else (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ))) := by
    have hbase := summable_pow_sigma_geometric r (r := x) hxn
    have habs : |x| = x := abs_of_nonneg hx0
    rw [habs] at hbase
    apply Summable.of_nonneg_of_le
      (f := fun m : ℕ => (m : ℝ) ^ r * Sigma.sigmaR m * x ^ m)
      (fun m => ?_) (fun m => ?_) hbase
    · by_cases hm : m = 0
      · simp [hm]
      · rw [if_neg hm]
        have := sigmaR_nonneg m
        positivity
    · by_cases hm : m = 0
      · rw [if_pos hm]
        have := sigmaR_nonneg m
        positivity
      · rw [if_neg hm]
        have hxm : Real.exp (-t * (m : ℝ)) = x ^ m := by
          rw [hxdef, ← Real.exp_nat_mul]
          congr 1
          ring
        rw [hxm]
  have hstep : sigmaMoment r t ≤ ∑' m : ℕ, (m : ℝ) ^ (r + 2) * x ^ m := by
    rw [sigmaMoment]
    refine hsumLHS.tsum_le_tsum (fun m => ?_) hsumRHS
    by_cases hm : m = 0
    · rw [if_pos hm]
      positivity
    · rw [if_neg hm]
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hσ : Sigma.sigmaR m ≤ (m : ℝ) ^ 2 := sigmaR_le_square hm1
      have hxm : Real.exp (-t * (m : ℝ)) = x ^ m := by
        rw [hxdef, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [hxm]
      have hmr : (0:ℝ) ≤ (m : ℝ) ^ r := by positivity
      have hxmp : (0:ℝ) ≤ x ^ m := by positivity
      have hkey : (m : ℝ) ^ r * Sigma.sigmaR m ≤ (m : ℝ) ^ (r + 2) := by
        have h1 : (m : ℝ) ^ r * Sigma.sigmaR m ≤ (m : ℝ) ^ r * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hσ hmr
        have h2 : (m : ℝ) ^ r * (m : ℝ) ^ 2 = (m : ℝ) ^ (r + 2) := by
          rw [← pow_add]
        linarith
      exact mul_le_mul_of_nonneg_right hkey hxmp
  -- step 2: the choose-geometric bound
  have hstep2 := tsum_pow_mul_geometric_le (r + 2) hx0 hx1
  -- step 3: 1−x ≥ t/2
  have hkey := one_sub_exp_neg_ge_half ht0 ht1
  have hpow : (t / 2) ^ (r + 2 + 1) ≤ (1 - x) ^ (r + 2 + 1) :=
    pow_le_pow_left₀ (by positivity) hkey _
  have hstep3 : ((r + 2).factorial : ℝ) / (1 - x) ^ (r + 2 + 1)
      ≤ ((r + 2).factorial : ℝ) / (t / 2) ^ (r + 2 + 1) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  have heq : ((r + 2).factorial : ℝ) / (t / 2) ^ (r + 2 + 1)
      = ((r + 2).factorial : ℝ) * 2 ^ (r + 3) / t ^ (r + 3) := by
    have harith : r + 2 + 1 = r + 3 := by omega
    rw [harith, div_pow, div_div_eq_mul_div]
  linarith [le_trans hstep (le_trans hstep2 (le_trans hstep3 (le_of_eq heq)))]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
