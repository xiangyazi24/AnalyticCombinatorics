import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MuTilde
import AnalyticCombinatorics.Ch8.Partitions.MassRateExpansion

/-!
# Numerator model: the second-order `ρ`-drop and its error

The drift numerator is `muNum n = ∑_m erdosWeight n m · rhoDrop n m` with
`rhoDrop n m = 3(√n − √(n−m))`.  Its model replaces the `√`-drop by its two-term Taylor
expansion (`sqrt_drop_second_order`):

  `rhoDropModel n m = 3( m/(2√n) + m²/(8(√n)³) )`,   `|rhoDrop − rhoDropModel| ≤ 3 m³/(√n)⁵`.

This is the `ρ`-drop half of the `muNum` expansion (the kernel half is the banked `modelSummand`).
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The two-term Taylor model of the smooth-rank drop `3(√n − √(n−m))`. -/
noncomputable def rhoDropModel (n m : ℕ) : ℝ :=
  3 * ((m : ℝ) / (2 * Real.sqrt (n : ℝ)) + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))

/-- **ρ-drop model error**: `|rhoDrop n m − rhoDropModel n m| ≤ 3 m³/(√n)⁵`. -/
lemma rhoDrop_sub_model_le {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    |rhoDrop n m - rhoDropModel n m| ≤ 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 := by
  have hkey := sqrt_drop_second_order hn hm
  have heq : rhoDrop n m - rhoDropModel n m
      = 3 * ((Real.sqrt (n : ℝ) - Real.sqrt ((n - m : ℕ) : ℝ))
          - ((m : ℝ) / (2 * Real.sqrt (n : ℝ))
            + (m : ℝ) ^ 2 / (8 * Real.sqrt (n : ℝ) ^ 3))) := by
    rw [rhoDrop, rhoDropModel]; ring
  rw [heq, abs_mul, show |(3 : ℝ)| = 3 from by norm_num]
  have : 3 * (m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5 = 3 * ((m : ℝ) ^ 3 / Real.sqrt (n : ℝ) ^ 5) := by
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hkey (by norm_num)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
