import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMoments

/-!
# Mass-rate campaign: explicit tail beyond the main range (R8 §4.1)

Beyond `m > n^{2/3}` (stated as `n² < m³` to stay cast-friendly) the kernel tail is
exponentially small:

  `Σ_{m: n² < m³} erdosWeight n m ≤ n³·e^{−(C/2)·n^{1/6}}`,

since `√n − √(n−m) ≥ m/(2√n) ≥ n^{1/6}/2`, `σ(m) ≤ m² ≤ n²`, `n−m ≥ 1`, and there are
at most `n` terms.  Far smaller than `1/n`.  Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The square-root drop dominates `m/(2√n)`. -/
lemma sqrt_drop_ge {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    (m : ℝ) / (2 * Real.sqrt (n : ℝ))
      ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  set q : ℝ := Real.sqrt ((n - m : ℕ) : ℝ) with hqdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    push_cast [Nat.cast_sub hm]
    ring
  have hq2 : q ^ 2 = s ^ 2 - (m : ℝ) := by
    rw [hqdef, Real.sq_sqrt (Nat.cast_nonneg _), hcast, hs2]
  have hqs : q ≤ s := by
    have h1 : q ^ 2 ≤ s ^ 2 := by
      rw [hq2]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    nlinarith [hq0, hs.le]
  have hprod : (s - q) * (s + q) = (m : ℝ) := by
    have h : (s - q) * (s + q) = s ^ 2 - q ^ 2 := by ring
    rw [h, hq2]
    ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)]
  have hsum_le : s + q ≤ 2 * s := by linarith
  have hsq_nonneg : 0 ≤ s - q := by linarith
  calc (m : ℝ) = (s - q) * (s + q) := hprod.symm
    _ ≤ (s - q) * (2 * s) := mul_le_mul_of_nonneg_left hsum_le hsq_nonneg

/--
**Explicit kernel tail beyond `n^{2/3}`** (R8 §4.1): eventually,

  `Σ_{m ∈ [1,n−1], n² < m³} erdosWeight n m ≤ n³·e^{−(C/2)·n^{1/6}}`.
-/
lemma kernel_tail_beyond_cube :
    ∀ᶠ n : ℕ in atTop,
      (∑ m ∈ Finset.Icc 1 (n - 1),
        if (n : ℝ) ^ 2 < (m : ℝ) ^ 3 then erdosWeight n m else 0)
        ≤ (n : ℝ) ^ 3 * Real.exp (-(C / 2) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
  classical
  have hC := C_pos
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  set X : ℝ := (n : ℝ) ^ 2 * Real.exp (-(C / 2) * (n : ℝ) ^ ((1 : ℝ) / 6)) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  -- per-term bound
  have hterm : ∀ m ∈ Finset.Icc 1 (n - 1),
      (if (n : ℝ) ^ 2 < (m : ℝ) ^ 3 then erdosWeight n m else 0) ≤ X := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hm_le : m ≤ n := by omega
    split_ifs with hcut
    · -- m ≥ n^{2/3}
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hm_ge : (n : ℝ) ^ ((2 : ℝ) / 3) ≤ (m : ℝ) := by
        by_contra hlt
        push_neg at hlt
        have h1 : ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ ((2 : ℝ) / 3)) 3,
            ← Real.rpow_mul hnpos.le]
          norm_num
        have h2 : (m : ℝ) ^ (3 : ℕ) < ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) :=
          pow_lt_pow_left₀ hlt hm0.le (by norm_num)
        rw [h1] at h2
        exact absurd hcut (by linarith [h2])
      have hdrop_ge : (n : ℝ) ^ ((1 : ℝ) / 6) / 2
          ≤ Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ) := by
        have h1 := sqrt_drop_ge hn1 hm_le
        have h2 : (n : ℝ) ^ ((1 : ℝ) / 6) / 2 ≤ (m : ℝ) / (2 * Real.sqrt (n : ℝ)) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          have hsqrt_rpow : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.sqrt_eq_rpow _
          have hmul : (n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 2)
              = (n : ℝ) ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_add hnpos]
            norm_num
          calc (n : ℝ) ^ ((1 : ℝ) / 6) * (2 * Real.sqrt (n : ℝ))
              = 2 * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 2)) := by
                rw [hsqrt_rpow]
                ring
            _ = 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by rw [hmul]
            _ ≤ (m : ℝ) * 2 := by linarith [hm_ge]
        linarith
      rw [erdosWeight, hXdef]
      have hσ : Sigma.sigmaR m ≤ (n : ℝ) ^ 2 := by
        have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm_le
        calc Sigma.sigmaR m ≤ (m : ℝ) ^ 2 := sigmaR_le_square hm1
          _ ≤ (n : ℝ) ^ 2 := by nlinarith [hm0.le]
      have hden : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
        have h1 : 1 ≤ n - m := by omega
        exact_mod_cast h1
      have hexp_le : Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
          ≤ Real.exp (-(C / 2) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hdrop_ge, hC]
      have hfrac : Sigma.sigmaR m / ((n - m : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc Sigma.sigmaR m / ((n - m : ℕ) : ℝ)
            ≤ Sigma.sigmaR m / 1 :=
              div_le_div_of_nonneg_left (sigmaR_nonneg m) one_pos hden
          _ = Sigma.sigmaR m := div_one _
          _ ≤ (n : ℝ) ^ 2 := hσ
      exact mul_le_mul hfrac hexp_le (Real.exp_pos _).le (by positivity)
    · exact hX0
  -- sum over at most n terms
  have hsum := Finset.sum_le_sum hterm
  have hconst : (∑ _m ∈ Finset.Icc 1 (n - 1), X) = ((n - 1 : ℕ) : ℝ) * X := by
    rw [Finset.sum_const, Nat.card_Icc]
    simp [nsmul_eq_mul]
  rw [hconst] at hsum
  have hcard : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hfinal : ((n - 1 : ℕ) : ℝ) * X ≤ (n : ℝ) * X :=
    mul_le_mul_of_nonneg_right hcard hX0
  have hgoal_eq : (n : ℝ) * X = (n : ℝ) ^ 3 * Real.exp (-(C / 2) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
    rw [hXdef]
    ring
  linarith [hsum, hfinal, le_of_eq hgoal_eq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
