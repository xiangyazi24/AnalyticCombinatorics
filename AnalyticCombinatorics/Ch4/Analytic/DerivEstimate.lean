import AnalyticCombinatorics.Ch4.Analytic.DeltaGeometry
import Mathlib.Analysis.Complex.Liouville

open Complex
open scoped Real

private lemma deltaLocalKappa_pos {R R' φ φ' : ℝ} (hR'0 : 0 < R')
    (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2) :
    0 < deltaLocalKappa R R' φ φ' := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hcos_lt : Real.cos φ' < Real.cos φ := by
    exact (Real.strictAntiOn_cos.lt_iff_gt
      (Set.mem_Icc.mpr ⟨hφ'.le, hφ'π.le⟩)
      (Set.mem_Icc.mpr ⟨hφ.le, hφπ.le⟩)).2 hφlt
  have hcos_pos : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
  have hRdiff_pos : 0 < R - R' := by linarith
  have hdenR_pos : 0 < 2 * (1 + R') := by nlinarith
  have hdenA_pos : 0 < 2 * (1 + Real.cos φ) := by nlinarith
  unfold deltaLocalKappa
  exact lt_min (by norm_num) (lt_min (div_pos hRdiff_pos hdenR_pos)
    (div_pos (by linarith) hdenA_pos))

private lemma deltaLocalKappa_le_half {R R' φ φ' : ℝ} :
    deltaLocalKappa R R' φ φ' ≤ 1 / 2 := by
  unfold deltaLocalKappa
  exact min_le_left _ _

private lemma rpow_scale_nat_eq {a x β M B : ℝ} {k : ℕ}
    (ha : 0 < a) (hx : 0 < x) :
    ((k.factorial : ℝ) * (M * B * x ^ (-β)) / ((a * x) ^ k)) =
      ((k.factorial : ℝ) * M * B * a ^ (-(k : ℝ))) * x ^ (-β - k) := by
  have hasplit : a ^ (-(k : ℝ)) = (a ^ k)⁻¹ := by
    rw [Real.rpow_neg ha.le (k : ℝ), Real.rpow_natCast]
  have hxsplit : x ^ (-β - (k : ℝ)) = x ^ (-β) * (x ^ k)⁻¹ := by
    rw [show -β - (k : ℝ) = -β + -(k : ℝ) by ring]
    rw [Real.rpow_add hx]
    rw [Real.rpow_neg hx.le (k : ℝ), Real.rpow_natCast]
  rw [hasplit, hxsplit, div_eq_mul_inv, mul_pow]
  field_simp [ha.ne', hx.ne']

private lemma rpow_neg_le_two_abs_mul {β x y : ℝ} (hx : 0 < x)
    (hhalf : (1 / 2) * x ≤ y) (hupper : y ≤ 2 * x) :
    y ^ (-β) ≤ 2 ^ |β| * x ^ (-β) := by
  by_cases hβ : 0 ≤ β
  · have hlower_pos : 0 < (1 / 2 : ℝ) * x := by positivity
    have hmono : y ^ (-β) ≤ ((1 / 2 : ℝ) * x) ^ (-β) := by
      exact Real.rpow_le_rpow_of_nonpos hlower_pos hhalf (by linarith)
    have hrewrite : ((1 / 2 : ℝ) * x) ^ (-β) = 2 ^ β * x ^ (-β) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hx.le]
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num
    rw [abs_of_nonneg hβ]
    exact hmono.trans_eq hrewrite
  · have hβlt : β < 0 := lt_of_not_ge hβ
    have hlower_pos : 0 < (1 / 2 : ℝ) * x := by positivity
    have hy0 : 0 ≤ y := le_trans hlower_pos.le hhalf
    have hmono : y ^ (-β) ≤ (2 * x) ^ (-β) := by
      exact Real.rpow_le_rpow hy0 hupper (by linarith)
    have hrewrite : (2 * x) ^ (-β) = 2 ^ (-β) * x ^ (-β) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
    rw [abs_of_neg hβlt]
    exact hmono.trans_eq hrewrite

theorem iteratedDeriv_norm_le_of_local_delta_bound
    {R φ β M κ : ℝ} {f : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hM0 : 0 ≤ M) (hκpos : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hz_ne : z ≠ 1)
    (hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ)
    (hbound : ∀ w ∈ DeltaDomainArg R φ,
      ‖f w‖ ≤ M * ‖(1 : ℂ) - w‖ ^ (-β)) :
    ‖iteratedDeriv k f z‖ ≤
      ((k.factorial : ℝ) * M * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        ‖(1 : ℂ) - z‖ ^ (-β - k) := by
  let x : ℝ := ‖(1 : ℂ) - z‖
  let ρ : ℝ := (κ / 2) * x
  have hxpos : 0 < x := by
    dsimp [x]
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_big : ρ < κ * x := by
    dsimp [ρ]
    nlinarith [hκpos, hxpos]
  have hclosed_sub_big : Metric.closedBall z ρ ⊆ Metric.ball z (κ * x) := by
    intro w hw
    have hdist : dist w z ≤ ρ := by
      simpa [Metric.mem_closedBall] using hw
    have hlt : dist w z < κ * x := lt_of_le_of_lt hdist hρ_lt_big
    simpa [Metric.mem_ball] using hlt
  have hclosed_sub_delta : Metric.closedBall z ρ ⊆ DeltaDomainArg R φ :=
    hclosed_sub_big.trans (by simpa [x] using hlocal)
  have hdiff : DiffContOnCl ℂ f (Metric.ball z ρ) := by
    have hd_closed : DifferentiableOn ℂ f (Metric.closedBall z ρ) :=
      han.differentiableOn.mono hclosed_sub_delta
    exact (hd_closed.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hsphere_bound : ∀ w ∈ Metric.sphere z ρ,
      ‖f w‖ ≤ M * 2 ^ |β| * x ^ (-β) := by
    intro w hw
    have hw_big : w ∈ Metric.ball z (κ * x) := by
      have hdist : dist w z = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have hlt : dist w z < κ * x := by
        rw [hdist]
        exact hρ_lt_big
      simpa [Metric.mem_ball] using hlt
    have hlocal_x : Metric.ball z (κ * x) ⊆ DeltaDomainArg R φ := by
      simpa [x] using hlocal
    have hw_delta : w ∈ DeltaDomainArg R φ := hlocal_x hw_big
    have hfw := hbound w hw_delta
    have hcomp := local_disk_norm_comparable_half hκpos.le hκhalf (by simpa [x] using hw_big)
    have hpow : ‖(1 : ℂ) - w‖ ^ (-β) ≤ 2 ^ |β| * x ^ (-β) := by
      exact rpow_neg_le_two_abs_mul (β := β) (x := x) (y := ‖(1 : ℂ) - w‖)
        hxpos (by simpa [x] using hcomp.1) (by simpa [x] using hcomp.2)
    calc
      ‖f w‖ ≤ M * ‖(1 : ℂ) - w‖ ^ (-β) := hfw
      _ ≤ M * (2 ^ |β| * x ^ (-β)) := mul_le_mul_of_nonneg_left hpow hM0
      _ = M * 2 ^ |β| * x ^ (-β) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (F := ℂ) (c := z) (R := ρ) (C := M * 2 ^ |β| * x ^ (-β))
    k hρpos hdiff hsphere_bound
  have hscale := rpow_scale_nat_eq (a := κ / 2) (x := x) (β := β)
    (M := M) (B := 2 ^ |β|) (k := k) (by positivity) hxpos
  calc
    ‖iteratedDeriv k f z‖ ≤
        (k.factorial : ℝ) * (M * 2 ^ |β| * x ^ (-β)) / ρ ^ k := hcauchy
    _ = ((k.factorial : ℝ) * M * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        x ^ (-β - k) := by
          simpa [ρ] using hscale
    _ = ((k.factorial : ℝ) * M * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        ‖(1 : ℂ) - z‖ ^ (-β - k) := by simp [x]

theorem exists_iteratedDeriv_norm_le_deltaDomain
    {R R' φ φ' β M : ℝ} {f : ℂ → ℂ} (k : ℕ)
    (hR'1 : 1 < R') (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hM0 : 0 ≤ M)
    (hbound : ∀ z ∈ DeltaDomainArg R φ,
      ‖f z‖ ≤ M * ‖(1 : ℂ) - z‖ ^ (-β)) :
    ∃ M' : ℝ, 0 ≤ M' ∧
      ∀ z ∈ DeltaDomainArg R' φ',
        ‖iteratedDeriv k f z‖ ≤ M' * ‖(1 : ℂ) - z‖ ^ (-β - k) := by
  let κ : ℝ := deltaLocalKappa R R' φ φ'
  have hR'0 : 0 < R' := by linarith
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact deltaLocalKappa_pos hR'0 hRR hφ hφlt hφ'2
  have hκhalf : κ ≤ 1 / 2 := by
    dsimp [κ]
    exact deltaLocalKappa_le_half
  refine ⟨(k.factorial : ℝ) * M * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ)), ?_, ?_⟩
  · positivity
  · intro z hz
    have hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ := by
      dsimp [κ]
      exact local_disk_subset_deltaDomain_deltaLocalKappa hR'0 hRR hφ hφlt hφ'2 hz
    exact iteratedDeriv_norm_le_of_local_delta_bound (R := R) (φ := φ) (β := β)
      (M := M) (κ := κ) (f := f) (z := z) (k := k) han hM0 hκpos hκhalf
      hz.2.1 hlocal hbound
