import AnalyticCombinatorics.Ch4.Analytic.CoeffDescent
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer

/-!
# Coefficient descent for little-o transfer

This file bootstraps the `β > 1` little-o transfer theorem to all real `β`.
-/

open Complex Filter Asymptotics
open scoped Topology Real BigOperators

noncomputable section

private lemma deltaLocalKappa_pos' {R R' φ φ' : ℝ} (hR'0 : 0 < R')
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
  have hRdiff_pos : 0 < R - R' := by linarith
  have hdenR_pos : 0 < 2 * (1 + R') := by nlinarith
  have hdenA_pos : 0 < 2 * (1 + Real.cos φ) := by
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
    nlinarith
  unfold deltaLocalKappa
  exact lt_min (by norm_num) (lt_min (div_pos hRdiff_pos hdenR_pos)
    (div_pos (by linarith) hdenA_pos))

private lemma deltaLocalKappa_le_half' {R R' φ φ' : ℝ} :
    deltaLocalKappa R R' φ φ' ≤ 1 / 2 := by
  unfold deltaLocalKappa
  exact min_le_left _ _

private lemma rpow_scale_nat_eq' {a x β M B : ℝ} {k : ℕ}
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

private lemma rpow_neg_le_two_abs_mul' {β x y : ℝ} (hx : 0 < x)
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

private lemma exists_delta_littleO_kernel_bound'
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ, hδpos, hδ⟩ := hf_o ε hε
  refine ⟨δ, hδpos, fun z hz hnear => ?_⟩
  have hdist_z : dist z (1 : ℂ) < δ := by
    simpa [dist_eq_norm, norm_sub_rev] using hnear
  have hgdist := hδ hz hdist_z
  have hg_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β := by positivity
  have hg_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε := by
    simpa [dist_eq_norm, Real.norm_of_nonneg hg_nonneg] using hgdist
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hpow_mul :
      ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos β (-β)]
    simp
  calc
    ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) *
        ‖(1 : ℂ) - z‖ ^ (-β) := by
      rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) :=
      mul_le_mul_of_nonneg_right (le_of_lt hg_lt) (by positivity)

private theorem iteratedDeriv_norm_le_of_local_delta_littleO_bound
    {R φ β ε κ : ℝ} {f : ℂ → ℂ} {z : ℂ} {k : ℕ}
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hε0 : 0 ≤ ε) (hκpos : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hz_ne : z ≠ 1)
    (hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ)
    (hnear_bound : ∀ w ∈ Metric.ball z (κ * ‖(1 : ℂ) - z‖),
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β)) :
    ‖iteratedDeriv k f z‖ ≤
      ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
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
      ‖f w‖ ≤ ε * 2 ^ |β| * x ^ (-β) := by
    intro w hw
    have hw_big : w ∈ Metric.ball z (κ * x) := by
      have hdist : dist w z = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      have hlt : dist w z < κ * x := by
        rw [hdist]
        exact hρ_lt_big
      simpa [Metric.mem_ball] using hlt
    have hfw := hnear_bound w (by simpa [x] using hw_big)
    have hcomp := local_disk_norm_comparable_half hκpos.le hκhalf (by simpa [x] using hw_big)
    have hpow : ‖(1 : ℂ) - w‖ ^ (-β) ≤ 2 ^ |β| * x ^ (-β) := by
      exact rpow_neg_le_two_abs_mul' (β := β) (x := x) (y := ‖(1 : ℂ) - w‖)
        hxpos (by simpa [x] using hcomp.1) (by simpa [x] using hcomp.2)
    calc
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β) := hfw
      _ ≤ ε * (2 ^ |β| * x ^ (-β)) := mul_le_mul_of_nonneg_left hpow hε0
      _ = ε * 2 ^ |β| * x ^ (-β) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (F := ℂ) (c := z) (R := ρ) (C := ε * 2 ^ |β| * x ^ (-β))
    k hρpos hdiff hsphere_bound
  have hscale := rpow_scale_nat_eq' (a := κ / 2) (x := x) (β := β)
    (M := ε) (B := 2 ^ |β|) (k := k) (by positivity) hxpos
  calc
    ‖iteratedDeriv k f z‖ ≤
        (k.factorial : ℝ) * (ε * 2 ^ |β| * x ^ (-β)) / ρ ^ k := hcauchy
    _ = ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        x ^ (-β - k) := by
          simpa [ρ] using hscale
    _ = ((k.factorial : ℝ) * ε * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))) *
        ‖(1 : ℂ) - z‖ ^ (-β - k) := by simp [x]

theorem iteratedDeriv_littleO_of_delta_littleO
    {R R' φ φ' β : ℝ} {f : ℂ → ℂ} (k : ℕ)
    (hR'1 : 1 < R') (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + k))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
  let κ : ℝ := deltaLocalKappa R R' φ φ'
  have hR'0 : 0 < R' := by linarith
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact deltaLocalKappa_pos' hR'0 hRR hφ hφlt hφ'2
  have hκhalf : κ ≤ 1 / 2 := by
    dsimp [κ]
    exact deltaLocalKappa_le_half'
  let A : ℝ := (k.factorial : ℝ) * 2 ^ |β| * (κ / 2) ^ (-(k : ℝ))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hAε_le : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hsmall⟩ :=
    exists_delta_littleO_kernel_bound' (R := R) (φ := φ) (β := β) (f := f)
      hf_o hεpos
  refine ⟨δ / 2, by positivity, fun z hz hdist_z => ?_⟩
  let x : ℝ := ‖(1 : ℂ) - z‖
  have hxpos : 0 < x := by
    dsimp [x]
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz.2.1)
  have hxnear : x < δ / 2 := by
    dsimp [x]
    simpa [dist_eq_norm, norm_sub_rev] using hdist_z
  have hlocal : Metric.ball z (κ * ‖(1 : ℂ) - z‖) ⊆ DeltaDomainArg R φ := by
    dsimp [κ]
    exact local_disk_subset_deltaDomain_deltaLocalKappa hR'0 hRR hφ hφlt hφ'2 hz
  have hnear_bound : ∀ w ∈ Metric.ball z (κ * ‖(1 : ℂ) - z‖),
      ‖f w‖ ≤ ε * ‖(1 : ℂ) - w‖ ^ (-β) := by
    intro w hw
    have hw_delta : w ∈ DeltaDomainArg R φ := hlocal hw
    have hcomp := local_disk_norm_comparable_half hκpos.le hκhalf hw
    have hw_near : ‖(1 : ℂ) - w‖ < δ := by
      have hupper : ‖(1 : ℂ) - w‖ ≤ 2 * x := by
        simpa [x] using hcomp.2
      have hxδ : 2 * x < δ := by linarith
      exact lt_of_le_of_lt hupper hxδ
    exact hsmall w hw_delta hw_near
  have hderiv := iteratedDeriv_norm_le_of_local_delta_littleO_bound
    (R := R) (φ := φ) (β := β) (ε := ε) (κ := κ) (f := f) (z := z) (k := k)
    han hεpos.le hκpos hκhalf hz.2.1 hlocal hnear_bound
  have hderivA :
      ‖iteratedDeriv k f z‖ ≤ A * ε * x ^ (-β - (k : ℝ)) := by
    simpa [A, x, mul_comm, mul_left_comm, mul_assoc] using hderiv
  have hpow_cancel : x ^ (-β - (k : ℝ)) * x ^ (β + (k : ℝ)) = 1 := by
    rw [← Real.rpow_add hxpos]
    ring_nf
    simp
  have htarget_nonneg :
      0 ≤ ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by positivity
  have hmain :
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) ≤ η / 2 := by
    calc
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ))
          ≤ (A * ε * x ^ (-β - (k : ℝ))) *
              ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hderivA htarget_nonneg
      _ = A * ε := by
            dsimp [x]
            rw [mul_assoc, hpow_cancel, mul_one]
      _ ≤ η / 2 := hAε_le
  have hnonneg :
      0 ≤ ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ)) := by
    positivity
  have hdist0 :
      dist (‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + (k : ℝ))) 0 < η := by
    rw [dist_eq_norm, sub_zero, Real.norm_of_nonneg hnonneg]
    exact lt_of_le_of_lt hmain (by linarith)
  simpa using hdist0

private lemma rpow_mul_nat_add_eventually (k : ℕ) (β : ℝ) :
    (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ)) * (m : ℝ) ^ (β + k - 1)) =ᶠ[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
  refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  change (m : ℝ) ^ (-(k : ℝ)) * (m : ℝ) ^ (β + (k : ℝ) - 1) =
    (m : ℝ) ^ (β - 1)
  rw [← Real.rpow_add hmpos]
  congr 1
  ring

lemma tail_isLittleO_of_iterated_coeff_isLittleO
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) (β : ℝ)
    (hderiv : (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β + k - 1))) :
    (fun m : ℕ => ‖p.coeff (m + k)‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
  let P : ℕ → ℝ := fun m => ∏ j ∈ Finset.range k, (m + 1 + j : ℝ)
  have heq : (fun m : ℕ => ‖p.coeff (m + k)‖) =ᶠ[atTop]
      (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) := by
    refine eventually_atTop.mpr ⟨0, fun m _hm => ?_⟩
    have hPpos : 0 < P m := by
      dsimp [P]
      exact desc_prod_pos k m
    have hdesc := scalarIteratedDerivSeries_coeff_norm p k m
    dsimp [P]
    calc
      ‖p.coeff (m + k)‖ = ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖)) := by
            field_simp [hPpos.ne']
      _ = (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ‖(scalarIteratedDerivSeries k p).coeff m‖ := by rw [hdesc]
  have hinvO : (fun m : ℕ => (P m)⁻¹) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ))) := by
    simpa [P] using inv_desc_prod_isBigO k
  have hmul : (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
    have hprod := hinvO.mul_isLittleO hderiv
    exact hprod.trans_eventuallyEq (rpow_mul_nat_add_eventually k β)
  exact heq.trans_isLittleO hmul

lemma isLittleO_of_shift {E : Type*} [Norm E] (a : ℕ → E) (k : ℕ) (e : ℝ)
    (h : (fun m : ℕ => a (m + k)) =o[atTop] (fun m : ℕ => (m : ℝ) ^ e)) :
    a =o[atTop] (fun n : ℕ => (n : ℝ) ^ e) := by
  have hcomp := h.comp_tendsto (Filter.tendsto_sub_atTop_nat k)
  have hcomp' : (fun n : ℕ => a ((n - k) + k)) =o[atTop]
      (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ e) := by
    simpa [Function.comp_apply] using hcomp
  have heq : a =ᶠ[atTop] (fun n : ℕ => a ((n - k) + k)) := by
    refine eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
    simp [Nat.sub_add_cancel hn]
  exact heq.trans_isLittleO (hcomp'.trans_isBigO (nat_sub_const_rpow_isBigO k e))

theorem coeff_norm_isLittleO_atTop_of_delta_littleO
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0)) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  obtain ⟨k, hkraw⟩ := exists_nat_gt (1 - β)
  have hβk : 1 < β + (k : ℝ) := by linarith
  let R' : ℝ := (1 + R) / 2
  have hR'1 : 1 < R' := by dsimp [R']; linarith
  have hRR' : R' < R := by dsimp [R']; linarith
  let φ' : ℝ := (φ + Real.pi / 2) / 2
  have hφ'0 : 0 < φ' := by dsimp [φ']; linarith [hφ0, Real.pi_pos]
  have hφlt : φ < φ' := by dsimp [φ']; linarith [hφ2]
  have hφ'2 : φ' < Real.pi / 2 := by dsimp [φ']; linarith [hφ2]
  have hsubset : DeltaDomainArg R' φ' ⊆ DeltaDomainArg R φ := by
    intro z hz
    exact ⟨lt_trans hz.1 hRR', hz.2.1, lt_trans hφlt hz.2.2⟩
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_iter : HasFPowerSeriesAt (iteratedDeriv k f)
      (scalarIteratedDerivSeries k p) (0 : ℂ) := hp.scalar_iteratedDeriv k
  have hΔ_iter : AnalyticOnNhd ℂ (iteratedDeriv k f) (DeltaDomainArg R' φ') := by
    simpa [iteratedDeriv_eq_iterate] using hΔ'.iterated_deriv k
  have hderiv_o : Tendsto (fun z : ℂ =>
      ‖iteratedDeriv k f z‖ * ‖(1 : ℂ) - z‖ ^ (β + k))
      (𝓝[DeltaDomainArg R' φ'] (1 : ℂ)) (𝓝 0) := by
    exact iteratedDeriv_littleO_of_delta_littleO
      (R := R) (R' := R') (φ := φ) (φ' := φ') (β := β) (f := f) k
      hR'1 hRR' hφ0 hφlt hφ'2 hΔ hf_o
  have hderivLittleO :
      (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =o[atTop]
        (fun m : ℕ => (m : ℝ) ^ (β + k - 1)) := by
    exact coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R') (φ := φ') (β := β + (k : ℝ))
      (f := iteratedDeriv k f) (p := scalarIteratedDerivSeries k p)
      hR'1 hφ'0 hφ'2 hp_iter hΔ_iter hderiv_o hβk
  have htail := tail_isLittleO_of_iterated_coeff_isLittleO p k β hderivLittleO
  exact isLittleO_of_shift (fun n : ℕ => ‖p.coeff n‖) k (β - 1) htail
