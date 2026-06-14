import AnalyticCombinatorics.Ch8.Partitions.ProductSecondOrder
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# Hardy–Ramanujan constant: brick 5 algebra (HR constant avenue d)

The pure-`√` constant identity underlying `a = 1/(4√3)`:
`(4√π / C)·√(2π) = 4√3`, where `C = π√(2/3)` and `C² = 4A = 2π²/3`.

This is the arithmetic core that bricks 2–4 feed into: with `K = 4√π/C` the saddle
prefactor and `√(2π)` the Meinardus prefactor, the limit constant is
`a = 1/(K·√(2π)) = 1/(4√3)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- `C² = 2π²/3`. -/
lemma C_sq_eq : C ^ 2 = 2 * Real.pi ^ 2 / 3 := by
  rw [C_sq_eq_four_mul_A, Partitions.A]
  ring

/-- The saddle/Meinardus prefactor product collapses to `4√3`:
`(4√π / C)·√(2π) = 4√3`. -/
lemma saddle_meinardus_const_identity :
    (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi) = 4 * Real.sqrt 3 := by
  have hCpos : 0 < C := C_pos
  have hL : 0 ≤ (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi) :=
    mul_nonneg (div_nonneg (by positivity) hCpos.le) (Real.sqrt_nonneg _)
  have hR : 0 ≤ 4 * Real.sqrt 3 := by positivity
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have key :
      ((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2 = (4 * Real.sqrt 3) ^ 2 := by
    rw [show ((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2
          = 16 * (Real.sqrt Real.pi ^ 2) * (Real.sqrt (2 * Real.pi) ^ 2) / C ^ 2 by
        field_simp; ring,
      Real.sq_sqrt (le_of_lt Real.pi_pos),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi), C_sq_eq,
      show (4 * Real.sqrt 3) ^ 2 = 16 * (Real.sqrt 3 ^ 2) by ring,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  calc (4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)
      = Real.sqrt (((4 * Real.sqrt Real.pi / C) * Real.sqrt (2 * Real.pi)) ^ 2) :=
        (Real.sqrt_sq hL).symm
    _ = Real.sqrt ((4 * Real.sqrt 3) ^ 2) := by rw [key]
    _ = 4 * Real.sqrt 3 := Real.sqrt_sq hR

end

end AnalyticCombinatorics.Ch8.Partitions
