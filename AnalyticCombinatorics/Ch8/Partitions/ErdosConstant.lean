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

/-- The 1-D real-saddle model sum `∑_{k≥1} e^{C√k − tk}/k` (the `k=0` term is `0`). -/
noncomputable def modelSaddle (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)

/-- AM–GM exponent bound: `C√n − tn ≤ C²/(2t) − (t/2)n` for all `n` (`t > 0`),
since `(C − t√n)² ≥ 0`. -/
lemma modelSaddle_exponent_bound {t : ℝ} (ht : 0 < t) (n : ℕ) :
    C * Real.sqrt (n : ℝ) - t * (n : ℝ) ≤ C ^ 2 / (2 * t) - (t / 2) * (n : ℝ) := by
  have hsn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht2 : t ^ 2 * Real.sqrt (n : ℝ) ^ 2 = t ^ 2 * (n : ℝ) := by rw [hsn]
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * t)]
  nlinarith [sq_nonneg (C - t * Real.sqrt (n : ℝ)), ht2]

/-- The model-saddle summand is summable for `t > 0`. -/
lemma summable_modelSaddleTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)) := by
  -- exp-only majorant: `exp(C√n−tn) ≤ exp(C²/2t)·exp(−t/2)^n`, geometric
  have hexp_summ :
      Summable (fun n : ℕ => Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))) := by
    have hgeo :
        Summable (fun n : ℕ => Real.exp (C ^ 2 / (2 * t)) * Real.exp (-(t / 2)) ^ n) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)).mul_left _
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) ?_ hgeo
    intro n
    calc Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ))
        ≤ Real.exp (C ^ 2 / (2 * t) - (t / 2) * (n : ℝ)) :=
          Real.exp_le_exp.mpr (modelSaddle_exponent_bound ht n)
      _ = Real.exp (C ^ 2 / (2 * t)) * Real.exp (-(t / 2)) ^ n := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  -- divide by `n`: `/n ≤ 1`, so termwise `≤` the exp-only majorant
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hexp_summ
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp only [Nat.cast_zero, div_zero]; positivity
  · rw [div_le_iff₀ (by exact_mod_cast hpos : (0 : ℝ) < (n : ℝ))]
    nlinarith [Real.exp_pos (C * Real.sqrt (n : ℝ) - t * (n : ℝ)),
      (by exact_mod_cast hpos : (1 : ℝ) ≤ (n : ℝ))]

/-- The model-saddle sum is strictly positive for `t > 0`. -/
lemma modelSaddle_pos {t : ℝ} (ht : 0 < t) : 0 < modelSaddle t := by
  unfold modelSaddle
  refine (summable_modelSaddleTerm ht).tsum_pos (fun n => by positivity) 1 ?_
  positivity

/-- **Brick 5 (combination).** Given the Abelian comparison (brick 3,
`log P − log a − log modelSaddle → 0`) and the real-saddle asymptotic (brick 4,
`log modelSaddle − A/t − ½log t − log(4√π/C) → 0`), together with the second-order
Laplace law (brick 2, `log_partLaplace_second_order`), the Erdős limit constant is
`a = 1/(4√3)`. -/
theorem erdos_limit_constant_of_asymptotics
    {a : ℝ} (ha : 0 < a)
    (hB3 :
      Tendsto
        (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hB4 :
      Tendsto
        (fun t : ℝ =>
          Real.log (modelSaddle t) - A / t - (1 / 2 : ℝ) * Real.log t
            - Real.log (4 * Real.sqrt Real.pi / C))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    a = 1 / (4 * Real.sqrt 3) := by
  have hCpos : 0 < C := C_pos
  have hKpos : 0 < 4 * Real.sqrt Real.pi / C := div_pos (by positivity) hCpos
  -- combine brick 3 + brick 4 - brick 2 → a constant tending to 0
  have hdiff := (hB3.add hB4).sub log_partLaplace_second_order
  simp only [add_zero, sub_zero] at hdiff
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          -Real.log a - Real.log (4 * Real.sqrt Real.pi / C)
            - (1 / 2 : ℝ) * Real.log (2 * Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hdiff.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [Real.log_div (ne_of_gt htpos) (by positivity)]
    ring
  have hzero :
      -Real.log a - Real.log (4 * Real.sqrt Real.pi / C)
        - (1 / 2 : ℝ) * Real.log (2 * Real.pi) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  -- solve `log a = log (1/(4√3))`, conclude by injectivity
  have h2pi : (1 / 2 : ℝ) * Real.log (2 * Real.pi) = Real.log (Real.sqrt (2 * Real.pi)) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have hlog_a : Real.log a = Real.log (1 / (4 * Real.sqrt 3)) := by
    have hstep : Real.log a
        = -(Real.log (4 * Real.sqrt Real.pi / C) + Real.log (Real.sqrt (2 * Real.pi))) := by
      rw [← h2pi]; linarith [hzero]
    rw [hstep, ← Real.log_mul (ne_of_gt hKpos)
        (ne_of_gt (Real.sqrt_pos.mpr (by positivity))), saddle_meinardus_const_identity,
      ← Real.log_inv, one_div]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha)
    (Set.mem_Ioi.mpr (by positivity)) hlog_a

end

end AnalyticCombinatorics.Ch8.Partitions
