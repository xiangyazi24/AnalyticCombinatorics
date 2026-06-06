import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpansion
import AnalyticCombinatorics.Ch8.Partitions.MassRateTail

/-!
# Mass-rate campaign: combined coefficient expansion (R8 §3.5)

The main local brick: on the regime `1 ≤ m`, `2m ≤ n`, `4Cm² ≤ √n³`,

  `|1/(n−m)·e^{−C·drop} − (1/n)·e_m·(1 + m/n − Cm²/(8√n³))|
      ≤ (3C² + 5C + 2)·e_m·(m²/√n⁶ + m³/√n⁷ + m⁴/√n⁸)`,

where `e_m = e^{−(C/2)m/√n}`.  Decomposition `true = (A + r₁)(B·e_m + r₂)` with
`A = 1/n + m/n²`, `B = 1 − Cm²/(8s³)`; the only cross term is `A·B − M = −Cm³/(8s⁷)`
exactly; `r₁·(true exp) ≤ 2m²/s⁶·e_m` via `drop ≥ m/(2s)` (no exponent weakening
needed).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/--
**Combined coefficient, second order** (R8 §3.5).
-/
lemma erdosWeight_coef_second_order {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m)
    (h2m : 2 * m ≤ n)
    (hsmall : 4 * C * (m : ℝ) ^ 2 ≤ Real.sqrt (n : ℝ) ^ 3) :
    |1 / (((n - m : ℕ) : ℝ)) *
        Real.exp (-C * (Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ)))
      - (1 / (n : ℝ)) * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          (1 + (m : ℝ) / (n : ℝ)
            - C * (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))|
      ≤ (3 * C ^ 2 + 5 * C + 2) *
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) *
          ((m : ℝ) ^ 2 / Real.sqrt (n : ℝ) ^ 6
            + (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 7
            + (m : ℝ) ^ 4 / Real.sqrt (n : ℝ) ^ 8) := by
  have hC := C_pos
  have hm_le : m ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set em : ℝ := Real.exp (-(C / 2) * (m : ℝ) / s) with hemdef
  have hem_pos : 0 < em := Real.exp_pos _
  -- pieces
  set A : ℝ := 1 / (n : ℝ) + (m : ℝ) / (n : ℝ) ^ 2 with hAdef
  set B : ℝ := 1 - C * (m : ℝ) ^ 2 / (8 * s ^ 3) with hBdef
  set r₁ : ℝ := 1 / (((n - m : ℕ) : ℝ)) - A with hr₁def
  set r₂ : ℝ := Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) - em * B with hr₂def
  have hr₁_abs : |r₁| ≤ 2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3 := by
    rw [hr₁def, hAdef]
    exact inv_sub_second_order hn h2m
  have hr₂_abs : |r₂| ≤ (C ^ 2 + 2 * C) * em *
      ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6) := by
    rw [hr₂def, hemdef, hBdef]
    have := exp_sqrt_drop_second_order hn hm_le hsmall
    rw [← hsdef] at this
    convert this using 2
  -- the true exponential is at most em
  have hexp_le_em : Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) ≤ em := by
    rw [hemdef]
    apply Real.exp_le_exp.mpr
    have hdrop := sqrt_drop_ge hn hm_le
    rw [← hsdef] at hdrop
    have h1 : (m : ℝ) / (2 * s) ≤ s - Real.sqrt ((n - m : ℕ) : ℝ) := hdrop
    have h2 : -(C / 2) * (m : ℝ) / s = -C * ((m : ℝ) / (2 * s)) := by
      field_simp
    rw [h2]
    nlinarith [h1, hC]
  have hexp_pos : 0 < Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) := Real.exp_pos _
  -- decomposition: true − main = (A·B − M)·em + A·r₂ + r₁·(true exp)
  -- where M = (1/n)(1 + m/n − Cm²/(8s³)) and A·B − M = −C·m³/(8·n²·s³)
  have hcross : A * B - (1 / (n : ℝ)) *
      (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = -(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3)) := by
    rw [hAdef, hBdef]
    field_simp
    ring
  have hdecomp : 1 / (((n - m : ℕ) : ℝ)) *
      Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
      - (1 / (n : ℝ)) * em *
          (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))
      = (A * B - (1 / (n : ℝ)) *
          (1 + (m : ℝ) / (n : ℝ) - C * (m : ℝ) ^ 2 / (8 * s ^ 3))) * em
        + A * r₂
        + r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ))) := by
    rw [hr₁def, hr₂def]
    ring
  rw [hdecomp, hcross]
  -- bound the three pieces
  have hA_le : A ≤ 2 / (n : ℝ) := by
    rw [hAdef]
    have h1 : (m : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hnpos]
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm_le
      nlinarith
    have h2 : (2 : ℝ) / (n : ℝ) = 1 / (n : ℝ) + 1 / (n : ℝ) := by ring
    linarith [le_of_eq h2]
  have hA_pos : 0 < A := by
    rw [hAdef]
    positivity
  -- piece 1: |cross·em| = C·m³/(8n²s³)·em = C·m³/(8s⁷)·em
  have hp1 : |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em|
      = C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em := by
    rw [abs_mul, abs_neg, abs_of_pos hem_pos,
      abs_of_pos (by positivity : (0:ℝ) < C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))]
    congr 1
    rw [show (n : ℝ) ^ 2 = (s ^ 2) ^ 2 by rw [hs2]]
    ring
  -- piece 2: |A·r₂| ≤ (2/n)·bound = (2C²+4C)·em·(m³/s⁷ + m⁴/s⁸)
  have hp2 : |A * r₂| ≤ (2 * C ^ 2 + 4 * C) * em *
      ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
    rw [abs_mul, abs_of_pos hA_pos]
    calc A * |r₂|
        ≤ (2 / (n : ℝ)) * ((C ^ 2 + 2 * C) * em *
            ((m : ℝ) ^ 3 / s ^ 5 + (m : ℝ) ^ 4 / s ^ 6)) := by
          apply mul_le_mul hA_le hr₂_abs (abs_nonneg _) (by positivity)
      _ = (2 * C ^ 2 + 4 * C) * em *
            ((m : ℝ) ^ 3 / ((n:ℝ) * s ^ 5) + (m : ℝ) ^ 4 / ((n:ℝ) * s ^ 6)) := by
          field_simp
          ring
      _ = (2 * C ^ 2 + 4 * C) * em *
            ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
          rw [show (n : ℝ) * s ^ 5 = s ^ 7 by rw [← hs2]; ring,
            show (n : ℝ) * s ^ 6 = s ^ 8 by rw [← hs2]; ring]
  -- piece 3: |r₁·exp| ≤ (2m²/n³)·em = 2·em·m²/s⁶
  have hp3 : |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))|
      ≤ 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
    rw [abs_mul, abs_of_pos hexp_pos]
    calc |r₁| * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))
        ≤ (2 * (m : ℝ) ^ 2 / (n : ℝ) ^ 3) * em := by
          apply mul_le_mul hr₁_abs hexp_le_em hexp_pos.le (by positivity)
      _ = 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
          rw [show (n : ℝ) ^ 3 = s ^ 6 by rw [← hs2]; ring]
          ring
  -- triangle inequality and final collection
  calc |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em
        + A * r₂
        + r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))|
      ≤ |(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em
          + A * r₂|
        + |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))| := abs_add_le _ _
    _ ≤ (|(-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em| + |A * r₂|)
        + |r₁ * Real.exp (-C * (s - Real.sqrt ((n - m : ℕ) : ℝ)))| := by
          linarith [abs_add_le ((-(C * (m : ℝ) ^ 3 / (8 * (n : ℝ) ^ 2 * s ^ 3))) * em) (A * r₂)]
    _ ≤ C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em
        + (2 * C ^ 2 + 4 * C) * em * ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8)
        + 2 * em * ((m : ℝ) ^ 2 / s ^ 6) := by
          rw [hp1] at *
          linarith [hp2, hp3]
    _ ≤ (3 * C ^ 2 + 5 * C + 2) * em *
          ((m : ℝ) ^ 2 / s ^ 6 + (m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by
        have hY2 : 0 ≤ em * ((m : ℝ) ^ 2 / s ^ 6) := by positivity
        have hY3 : 0 ≤ em * ((m : ℝ) ^ 3 / s ^ 7) := by positivity
        have hY4 : 0 ≤ em * ((m : ℝ) ^ 4 / s ^ 8) := by positivity
        have c2 : (0 : ℝ) ≤ 3 * C ^ 2 + 5 * C := by positivity
        have c3 : (0 : ℝ) ≤ C ^ 2 + 7 * C / 8 + 2 := by positivity
        have c4 : (0 : ℝ) ≤ C ^ 2 + C + 2 := by positivity
        have key : (C / 8) * (em * ((m : ℝ) ^ 3 / s ^ 7))
            + ((2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 4 / s ^ 8)))
            + 2 * (em * ((m : ℝ) ^ 2 / s ^ 6))
            ≤ (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 2 / s ^ 6))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 4 / s ^ 8)) := by
          nlinarith [mul_nonneg c2 hY2, mul_nonneg c3 hY3, mul_nonneg c4 hY4]
        calc C * (m : ℝ) ^ 3 / (8 * s ^ 7) * em
              + (2 * C ^ 2 + 4 * C) * em * ((m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8)
              + 2 * em * ((m : ℝ) ^ 2 / s ^ 6)
            = (C / 8) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + ((2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 3 / s ^ 7))
                + (2 * C ^ 2 + 4 * C) * (em * ((m : ℝ) ^ 4 / s ^ 8)))
              + 2 * (em * ((m : ℝ) ^ 2 / s ^ 6)) := by ring
          _ ≤ (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 2 / s ^ 6))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 3 / s ^ 7))
              + (3 * C ^ 2 + 5 * C + 2) * (em * ((m : ℝ) ^ 4 / s ^ 8)) := key
          _ = (3 * C ^ 2 + 5 * C + 2) * em *
              ((m : ℝ) ^ 2 / s ^ 6 + (m : ℝ) ^ 3 / s ^ 7 + (m : ℝ) ^ 4 / s ^ 8) := by ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
