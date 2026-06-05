import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# Uniform window replacements for the Erdős kernel

On the window `m ≤ b√n` the two kernel ingredients admit uniform `O(1/√n)`-quality replacements:

* `√n − √(n−m) = m/(√n + √(n−m))` (exact rationalization), with
  `|(√n − √(n−m)) − m/(2√n)| ≤ b²/(2√n)`;
* `|1/(n−m) − 1/n| ≤ 2b/n^{3/2}` (for `2m ≤ n`).

These are the estimates that convert `erdosWeight` into the model kernel
`(σ(m)/n)·e^{−(C/2)m/√n}` uniformly on fixed windows.  Opus-authored during the codex outage.
-/

noncomputable section

open Real

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Exact rationalization: `√n − √(n−m) = m/(√n + √(n−m))` for `m ≤ n`, `1 ≤ n`. -/
lemma sqrt_diff_eq {n m : ℕ} (hm : m ≤ n) (hn : 1 ≤ n) :
    Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)
      = (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) := by
  have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
    push_cast [Nat.cast_sub hm]; ring
  have hs : (0 : ℝ) < Real.sqrt n := by
    apply Real.sqrt_pos.mpr; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hden : (0 : ℝ) < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by
    have := Real.sqrt_nonneg ((n - m : ℕ) : ℝ); linarith
  rw [eq_div_iff hden.ne']
  have hsq1 : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hsq2 : Real.sqrt ((n - m : ℕ) : ℝ) * Real.sqrt ((n - m : ℕ) : ℝ)
      = ((n - m : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have expand :
      (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
        * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ))
      = (n : ℝ) - ((n - m : ℕ) : ℝ) := by
    have : (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
        * (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ))
        = Real.sqrt n * Real.sqrt n
          - Real.sqrt ((n - m : ℕ) : ℝ) * Real.sqrt ((n - m : ℕ) : ℝ) := by ring
    rw [this, hsq1, hsq2]
  rw [expand, hnm]; ring

/-- Uniform second-order bound on the window: `|(√n − √(n−m)) − m/(2√n)| ≤ b²/(2√n)`
for `m ≤ b√n`, `m ≤ n`, `1 ≤ n`. -/
lemma sqrt_diff_window_approx {b : ℝ} {n m : ℕ} (_hb : 0 ≤ b)
    (hm : m ≤ n) (hn : 1 ≤ n) (hwin : (m : ℝ) ≤ b * Real.sqrt n) :
    |(Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ)) - (m : ℝ) / (2 * Real.sqrt n)|
      ≤ b ^ 2 / (2 * Real.sqrt n) := by
  have hs : (0 : ℝ) < Real.sqrt n := by
    apply Real.sqrt_pos.mpr; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hs2 : (0 : ℝ) ≤ Real.sqrt ((n - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hden : (0 : ℝ) < Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ) := by linarith
  rw [sqrt_diff_eq hm hn]
  -- m/(√n+√(n−m)) − m/(2√n) = m·(2√n − (√n+√(n−m)))/((√n+√(n−m))·2√n)
  --                        = m·(√n − √(n−m))/((√n+√(n−m))·2√n)
  --                        = m²/((√n+√(n−m))²·2√n)
  have key :
      (m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) - (m : ℝ) / (2 * Real.sqrt n)
        = (m : ℝ) * (Real.sqrt n - Real.sqrt ((n - m : ℕ) : ℝ))
          / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n)) := by
    field_simp
    ring
  rw [key, sqrt_diff_eq hm hn]
  -- now the expression is m·(m/(√n+√(n−m))) / ((√n+√(n−m))·2√n) = m²/((√n+√(n−m))²·2√n)
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)))
      / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n)) := by positivity
  rw [abs_of_nonneg hnonneg]
  -- bound: denominator (√n+√(n−m))² ≥ n; numerator m² ≤ b²n
  have hm2 : (m : ℝ) ^ 2 ≤ b ^ 2 * (n : ℝ) := by
    have h1 : (m : ℝ) ^ 2 ≤ (b * Real.sqrt n) ^ 2 := by
      apply sq_le_sq' _ hwin
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [mul_nonneg _hb hs.le]
    calc (m : ℝ) ^ 2 ≤ (b * Real.sqrt n) ^ 2 := h1
      _ = b ^ 2 * (Real.sqrt n * Real.sqrt n) := by ring
      _ = b ^ 2 * (n : ℝ) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hdensq : (n : ℝ) ≤ (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) ^ 2 := by
    have h1 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    nlinarith [hs.le, hs2]
  -- assemble
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  calc (m : ℝ) * ((m : ℝ) / (Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)))
        / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) * (2 * Real.sqrt n))
      = (m : ℝ) ^ 2 / ((Real.sqrt n + Real.sqrt ((n - m : ℕ) : ℝ)) ^ 2 * (2 * Real.sqrt n)) := by
        field_simp
    _ ≤ b ^ 2 * (n : ℝ) / ((n : ℝ) * (2 * Real.sqrt n)) := by
        exact div_le_div₀ (by positivity) hm2 (by positivity)
          (mul_le_mul_of_nonneg_right hdensq (by positivity))
    _ = b ^ 2 / (2 * Real.sqrt n) := by
        field_simp

/-- Uniform reciprocal replacement: `|1/(n−m) − 1/n| ≤ 2b/n^{3/2}` for `m ≤ b√n`, `2m ≤ n`, `1 ≤ n`. -/
lemma inv_window_approx {b : ℝ} {n m : ℕ} (hb : 0 ≤ b)
    (h2 : 2 * m ≤ n) (hn : 1 ≤ n) (hwin : (m : ℝ) ≤ b * Real.sqrt n) :
    |1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)|
      ≤ 2 * b / ((n : ℝ) * Real.sqrt n) := by
  have hm : m ≤ n := le_trans (Nat.le_mul_of_pos_left m (by norm_num)) h2
  have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
    push_cast [Nat.cast_sub hm]; ring
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hhalf : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    rw [hnm]
    have : (2 * m : ℕ) ≤ n := h2
    have h2' : 2 * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hnmpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := lt_of_lt_of_le (by linarith) hhalf
  have hdiff : 1 / (((n - m : ℕ) : ℝ)) - 1 / (n : ℝ)
      = (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ)) := by
    have hne1 : ((n - m : ℕ) : ℝ) ≠ 0 := hnmpos.ne'
    have hne2 : (n : ℝ) ≠ 0 := hnpos.ne'
    rw [div_sub_div _ _ hne1 hne2]
    congr 1
    rw [hnm]; ring
  rw [hdiff]
  have hnonneg : (0 : ℝ) ≤ (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ)) := by positivity
  rw [abs_of_nonneg hnonneg]
  -- m/((n−m)·n) ≤ (b√n)/((n/2)·n) = 2b√n/n² = 2b/(n^{3/2})
  have hbound : (m : ℝ) / (((n - m : ℕ) : ℝ) * (n : ℝ))
      ≤ (b * Real.sqrt n) / (((n : ℝ) / 2) * (n : ℝ)) := by
    exact div_le_div₀ (by positivity) hwin (by positivity)
      (mul_le_mul_of_nonneg_right hhalf hnpos.le)
  refine hbound.trans ?_
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  have heq : b * Real.sqrt n * ((n : ℝ) * Real.sqrt n)
      = 2 * b * ((n : ℝ) / 2 * (n : ℝ)) := by
    calc b * Real.sqrt n * ((n : ℝ) * Real.sqrt n)
        = b * (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = b * (n : ℝ) * (n : ℝ) := by rw [hsq]
      _ = 2 * b * ((n : ℝ) / 2 * (n : ℝ)) := by ring
  exact le_of_eq heq

end AnalyticCombinatorics.Ch8.Partitions.Erdos
