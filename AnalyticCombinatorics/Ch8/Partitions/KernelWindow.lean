import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MeshEstimate
import AnalyticCombinatorics.Ch8.Partitions.ErdosUniform
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# The true-kernel window limit

`Σ_{(a√n, b√n]} erdosWeight n m → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.

Conversion of the model kernel to the true Erdős kernel via the banked uniform window
replacements: `1/(n−m) = 1/n + O(b/n^{3/2})` (`inv_window_approx`) and
`√n − √(n−m) = m/(2√n) + O(b²/√n)·(1/√n)` (`sqrt_diff_window_approx`), with all
exponentials `≤ 1` on the window.  Per-term difference `≤ σ(m)·D/n^{3/2}`; summed against
the quadratic divisor bound `Σ_{m ≤ b√n} σ(m) ≤ B b² n` this is `O(1/√n) → 0`, and
`model_kernel_window` finishes.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- Lipschitz bound for `e^{−x}` on the nonnegative half-line (local copy). -/
private lemma exp_neg_sub_exp_neg_le' {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
    have := Real.add_one_le_exp (-(v - u))
    linarith
  have h4 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4), Real.exp_pos (-u)]

/-- `|e^x − e^y| ≤ |x − y|` for `x, y ≤ 0`. -/
private lemma abs_exp_sub_exp_le {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · have hle : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have h2 := exp_neg_sub_exp_neg_le' (u := -x) (v := -y) (by linarith) (by linarith)
    simp only [neg_neg] at h2
    linarith
  · have hle : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have h2 := exp_neg_sub_exp_neg_le' (u := -y) (v := -x) (by linarith) (by linarith)
    simp only [neg_neg] at h2
    linarith

/--
Per-term difference bound on the window: for `2m ≤ n`, `m ≤ b√n`,

  `|erdosWeight n m − σ(m)·e^{−(C/2)m/√n}·(1/n)| ≤ σ(m)·(2b + Cb²/2)/(n√n)`.
-/
private lemma kernel_term_diff_bound {b : ℝ} (hb : 0 < b) {n m : ℕ}
    (hn : 1 ≤ n) (h2m : 2 * m ≤ n)
    (hwin : (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) :
    |erdosWeight n m -
        σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) * (1 / (n : ℝ))|
      ≤ σR m * ((2 * b + C * b ^ 2 / 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
  have hC := C_pos
  have hm_le : m ≤ n := le_trans (by omega) h2m
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnposR
  have hσ : (0 : ℝ) ≤ σR m := sigmaR_nonneg m
  have hsub_le : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n m
  -- the two exponentials
  set w : ℝ := Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))) with hwdef
  set md : ℝ := Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) with hmddef
  have hw_pos : 0 < w := Real.exp_pos _
  have hw_le_one : w ≤ 1 := by
    rw [hwdef, Real.exp_le_one_iff]
    nlinarith [hsub_le, hC]
  -- decomposition
  have hdecomp :
      erdosWeight n m - σR m * md * (1 / (n : ℝ))
        = σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)
          + σR m * ((w - md) * (1 / (n : ℝ))) := by
    unfold erdosWeight
    rw [← hwdef]
    ring
  -- the reciprocal replacement
  have h1 : |1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)|
      ≤ 2 * b / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
    inv_window_approx hb.le h2m hn hwin
  -- the exponent replacement
  have h2 : |w - md| ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) := by
    have hx : -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)) ≤ 0 := by
      nlinarith [hsub_le, hC]
    have hy : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ) ≤ 0 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hnum : -(C / 2) * (m : ℝ) ≤ 0 := by nlinarith [hC]
      exact div_nonpos_of_nonpos_of_nonneg hnum hs.le
    have habs := abs_exp_sub_exp_le hx hy
    have heq :
        -C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
            - (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
          = -C * ((Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
              - (m : ℝ) / (2 * Real.sqrt (n : ℝ))) := by
      field_simp
      ring
    calc |w - md| ≤ |(-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
            - (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))| := habs
      _ = C * |(Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
            - (m : ℝ) / (2 * Real.sqrt (n : ℝ))| := by
          rw [heq, abs_mul, abs_neg, abs_of_pos hC]
      _ ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (sqrt_diff_window_approx hb.le hm_le hn hwin) hC.le
  -- assemble
  rw [hdecomp]
  have hterm1 : |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)|
      ≤ σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ, abs_of_pos hw_pos]
    have hmm : |1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)| * w
        ≤ (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) * 1 :=
      mul_le_mul h1 hw_le_one hw_pos.le (by positivity)
    calc σR m * (|1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)| * w)
        ≤ σR m * ((2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) * 1) :=
          mul_le_mul_of_nonneg_left hmm hσ
      _ = σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ))) := by ring
  have hterm2 : |σR m * ((w - md) * (1 / (n : ℝ)))|
      ≤ σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hσ,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
    have hstep : |w - md| * (1 / (n : ℝ))
        ≤ C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    calc σR m * (|w - md| * (1 / (n : ℝ)))
        ≤ σR m * (C * (b ^ 2 / (2 * Real.sqrt (n : ℝ))) * (1 / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hσ
      _ = σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
          field_simp
  calc |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)
        + σR m * ((w - md) * (1 / (n : ℝ)))|
      ≤ |σR m * ((1 / ((n - m : ℕ) : ℝ) - 1 / (n : ℝ)) * w)|
        + |σR m * ((w - md) * (1 / (n : ℝ)))| := abs_add_le _ _
    _ ≤ σR m * (2 * b / ((n : ℝ) * Real.sqrt (n : ℝ)))
        + σR m * (C * b ^ 2 / 2 / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
        linarith [hterm1, hterm2]
    _ = σR m * ((2 * b + C * b ^ 2 / 2) / ((n : ℝ) * Real.sqrt (n : ℝ))) := by
        ring

/-- The masked divisor mass on the window is at most `B·b²·n`. -/
private lemma window_sigma_mass_le {a b : ℝ} (hb : 0 < b) {B : ℝ}
    (hB : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, σR m) ≤ B * (N : ℝ) ^ 2)
    (hBpos : 0 < B) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
       then σR m else 0))
      ≤ B * b ^ 2 * (n : ℝ) := by
  classical
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsub :
      (Finset.Icc 1 (n - 1)).filter
          (fun m : ℕ => a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ))
        ⊆ Finset.Icc 1 ⌊b * Real.sqrt (n : ℝ)⌋₊ := by
    intro m hm
    obtain ⟨hmIcc, hwin⟩ := Finset.mem_filter.mp hm
    have h1 : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
    have h2 : m ≤ ⌊b * Real.sqrt (n : ℝ)⌋₊ := Nat.le_floor hwin.2
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  calc (∑ m ∈ Finset.Icc 1 (n - 1),
        (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ) then σR m else 0))
      = ∑ m ∈ (Finset.Icc 1 (n - 1)).filter
          (fun m : ℕ => a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)), σR m := by
        rw [Finset.sum_filter]
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊b * Real.sqrt (n : ℝ)⌋₊, σR m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun m _ _ => sigmaR_nonneg m)
    _ ≤ B * (⌊b * Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ 2 := hB _
    _ ≤ B * (b * Real.sqrt (n : ℝ)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        have hfl : ((⌊b * Real.sqrt (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
          Nat.floor_le (by positivity)
        have h0 : (0 : ℝ) ≤ (⌊b * Real.sqrt (n : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
        nlinarith [hfl, h0]
    _ = B * b ^ 2 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    _ = B * b ^ 2 * (n : ℝ) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]

/--
**The true-kernel window limit** (HR Stage I.3):

  `Σ_{(a√n, b√n]} erdosWeight n m → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.
-/
theorem erdos_kernel_window {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto
      (fun n : ℕ => ∑ m ∈ Finset.Icc 1 (n - 1),
        (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
         then erdosWeight n m else 0))
      atTop (𝓝 (modelIntegral C a b)) := by
  classical
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hC := C_pos
  obtain ⟨B, hBpos, hB⟩ := sigma_summatory_quadratic_bound
  set D : ℝ := 2 * b + C * b ^ 2 / 2 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    positivity
  have hmodel := model_kernel_window (C := C) hC a b ha hab
  -- the difference tends to 0
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          (∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n)
        atTop (𝓝 0) := by
    -- squeeze against (B·b²·D)/√n
    have hbound : ∀ᶠ n : ℕ in atTop,
        ‖(∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n‖
          ≤ (B * b ^ 2 * D) / Real.sqrt (n : ℝ) := by
      have hev : ∀ᶠ n : ℕ in atTop, (⌈(4 : ℝ) * b ^ 2⌉₊ ≤ n ∧ 1 ≤ n) := by
        filter_upwards [eventually_ge_atTop ⌈(4 : ℝ) * b ^ 2⌉₊,
          eventually_ge_atTop 1] with n h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hev] with n ⟨hn4, hn1⟩
      have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnposR
      have hn4R : (4 : ℝ) * b ^ 2 ≤ (n : ℝ) := by
        calc (4 : ℝ) * b ^ 2 ≤ (⌈(4 : ℝ) * b ^ 2⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn4
      -- on the window, 2m ≤ n
      have h2m : ∀ m : ℕ, (m : ℝ) ≤ b * Real.sqrt (n : ℝ) → 2 * m ≤ n := by
        intro m hm
        have h2b : 2 * b ≤ Real.sqrt (n : ℝ) := by
          have h2b0 : (0 : ℝ) ≤ 2 * b := by positivity
          calc 2 * b = Real.sqrt ((2 * b) ^ 2) := (Real.sqrt_sq h2b0).symm
            _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
        have : 2 * (m : ℝ) ≤ (n : ℝ) := by
          calc 2 * (m : ℝ) ≤ 2 * (b * Real.sqrt (n : ℝ)) := by linarith
            _ = (2 * b) * Real.sqrt (n : ℝ) := by ring
            _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
                mul_le_mul_of_nonneg_right h2b hs.le
            _ = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
        exact_mod_cast this
      -- blockSum as a termwise-masked sum
      have hblock :
          blockSum C a b n =
            ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                  (1 / (n : ℝ))
               else 0) := by
        rw [blockSum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
        · rw [if_pos hwin, if_pos hwin]
          ring
        · rw [if_neg hwin, if_neg hwin, mul_zero]
      -- difference as one masked sum
      have hsumdiff :
          (∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0))
            - blockSum C a b n
          = ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then erdosWeight n m -
                  σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                    (1 / (n : ℝ))
               else 0) := by
        rw [hblock, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
        · rw [if_pos hwin, if_pos hwin, if_pos hwin]
        · rw [if_neg hwin, if_neg hwin, if_neg hwin, sub_zero]
      rw [hsumdiff, Real.norm_eq_abs]
      -- triangle inequality + per-term bound + mass bound
      calc |∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m -
                σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                  (1 / (n : ℝ))
             else 0)|
          ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              |if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then erdosWeight n m -
                  σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
                    (1 / (n : ℝ))
               else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (n - 1),
              (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                  (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
               then σR m * (D / ((n : ℝ) * Real.sqrt (n : ℝ)))
               else 0) := by
            refine Finset.sum_le_sum ?_
            intro m _hm
            by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
            · rw [if_pos hwin, if_pos hwin]
              exact kernel_term_diff_bound hb hn1 (h2m m hwin.2) hwin.2
            · rw [if_neg hwin, if_neg hwin, abs_zero]
        _ = (D / ((n : ℝ) * Real.sqrt (n : ℝ))) *
              ∑ m ∈ Finset.Icc 1 (n - 1),
                (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                    (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
                 then σR m else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m _hm
            by_cases hwin : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
            · rw [if_pos hwin, if_pos hwin]
              ring
            · rw [if_neg hwin, if_neg hwin, mul_zero]
        _ ≤ (D / ((n : ℝ) * Real.sqrt (n : ℝ))) * (B * b ^ 2 * (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_left
              (window_sigma_mass_le (a := a) hb hB hBpos n)
            positivity
        _ = (B * b ^ 2 * D) / Real.sqrt (n : ℝ) := by
            field_simp
    -- the bound tends to zero
    have hzero :
        Tendsto (fun n : ℕ => (B * b ^ 2 * D) / Real.sqrt (n : ℝ))
          atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    exact squeeze_zero_norm' hbound hzero
  -- combine: trueSum = (trueSum − blockSum) + blockSum
  have hcomb := hdiff.add hmodel
  rw [zero_add] at hcomb
  have hfun :
      (fun n : ℕ =>
        ((∑ m ∈ Finset.Icc 1 (n - 1),
          (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
              (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
           then erdosWeight n m else 0))
          - blockSum C a b n) + blockSum C a b n)
      = fun n : ℕ =>
          ∑ m ∈ Finset.Icc 1 (n - 1),
            (if a * Real.sqrt (n : ℝ) < (m : ℝ) ∧
                (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
             then erdosWeight n m else 0) := by
    funext n
    ring
  rwa [hfun] at hcomb

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
