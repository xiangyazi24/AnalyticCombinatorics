import AnalyticCombinatorics.Ch4.Analytic.OTransfer

/-!
# Little-o transfer for Δ-analytic functions, β > 1

This file contains the coefficient-level `o` transfer companion to the
circle-only `O` transfer in `OTransfer.lean`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal

noncomputable section

private def transferCircleBound (f : ℂ → ℂ) (n : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((1 : ℝ) - 1 / n)⁻¹ ^ n *
    ∫ θ in (-Real.pi)..Real.pi,
      ‖f ((((1 : ℝ) - 1 / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖

private lemma circlePoint_mem_delta {R φ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrR : r < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I)) ∈ DeltaDomainArg R φ := by
  refine closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2 ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc
    ‖((r : ℂ) * Complex.exp (θ * Complex.I)) - 0‖
        = r := by
          simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr0]
    _ ≤ r := le_rfl

private lemma circleKernel_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β))
      volume (-Real.pi) Real.pi := by
  refine ((by fun_prop :
      Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖)
    |>.continuousOn.rpow_const ?_).intervalIntegrable
  intro θ _hθ
  left
  have hnorm_exp : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  have hne : (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro hzero
    have hmul_eq : (r : ℂ) * Complex.exp (θ * Complex.I) = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [hmul_eq, norm_one]
    have habs : |r| = 1 := by
      simpa [norm_mul, hnorm_exp] using hnorm
    have hr_eq_one : r = 1 := by
      simpa [abs_of_nonneg hr0] using habs
    linarith
  exact (norm_pos_iff.mpr hne).ne'

private lemma circleFunction_intervalIntegrable
    {R φ r : ℝ} {f : ℂ → ℂ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hrR : r < R)
    (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    IntervalIntegrable
      (fun θ : ℝ => ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
      volume (-Real.pi) Real.pi := by
  have hcont_delta : ContinuousOn f (DeltaDomainArg R φ) :=
    han.differentiableOn.continuousOn
  have hcont_circle : ContinuousOn
      (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (Set.uIcc (-Real.pi) Real.pi) := by
    refine hcont_delta.comp ?_ ?_
    · exact (by fun_prop : Continuous fun θ : ℝ =>
        ((r : ℂ) * Complex.exp (θ * Complex.I))).continuousOn
    · intro θ _hθ
      exact circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
  exact hcont_circle.norm.intervalIntegrable

private lemma closedUnitAway_subset_delta {R φ δ : ℝ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (hδ : 0 < δ) :
    {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} ⊆ DeltaDomainArg R φ := by
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  rw [delta_arg_eq_geom hφ0.le hφπ]
  intro z hz
  rcases hz with ⟨hz1, haway⟩
  refine ⟨?_, ?_⟩
  · have hzR : ‖z‖ < R := lt_of_le_of_lt hz1 hR
    simpa [Metric.mem_ball, dist_eq_norm] using hzR
  · have hleft : (z - 1).re ≤ 0 := by
      rw [Complex.sub_re, Complex.one_re]
      exact sub_nonpos.mpr (Complex.re_le_norm z |>.trans hz1)
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ0, Real.pi_pos], hφ2⟩
    have hnorm_pos : 0 < ‖z - 1‖ := by
      rw [← norm_sub_rev]
      exact lt_of_lt_of_le hδ haway
    have hright_pos : 0 < Real.cos φ * ‖z - 1‖ :=
      mul_pos hcos_pos hnorm_pos
    exact lt_of_le_of_lt hleft hright_pos

private lemma isCompact_closedUnitAway (δ : ℝ) :
    IsCompact {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} := by
  have hclosed : IsClosed {z : ℂ | δ ≤ ‖(1 : ℂ) - z‖} :=
    isClosed_le continuous_const ((continuous_const.sub continuous_id).norm)
  have hset :
      {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖} =
        Metric.closedBall (0 : ℂ) 1 ∩ {z : ℂ | δ ≤ ‖(1 : ℂ) - z‖} := by
    ext z
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hset]
  exact (isCompact_closedBall (0 : ℂ) 1).inter_right hclosed

private lemma exists_bound_on_closedUnitAway
    {R φ δ : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2) (hδ : 0 < δ)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    ∃ M, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → δ ≤ ‖(1 : ℂ) - z‖ → ‖f z‖ ≤ M := by
  let S : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 ∧ δ ≤ ‖(1 : ℂ) - z‖}
  have hScompact : IsCompact S := isCompact_closedUnitAway δ
  have hSsub : S ⊆ DeltaDomainArg R φ :=
    closedUnitAway_subset_delta hR hφ0 hφ2 hδ
  have hcont : ContinuousOn f S :=
    han.differentiableOn.continuousOn.mono hSsub
  obtain ⟨M₀, hM₀⟩ := hScompact.exists_bound_of_continuousOn hcont
  refine ⟨max M₀ 0, le_max_right _ _, fun z hz1 haway => ?_⟩
  exact (hM₀ z ⟨hz1, haway⟩).trans (le_max_left _ _)

private lemma exists_delta_littleO_kernel_bound
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

/--
The hard analytic estimate behind the little-o transfer.

It is the Cauchy-circle integral split at radius `1 - 1/n`: the part with
`‖1 - z‖` small uses the little-o hypothesis, the complementary moving arc is
uniformly bounded on a compact subset of the Δ-domain and is `O(1)`, hence
negligible against `n^(β-1)` because `β > 1`.
-/
private lemma transferCircleBound_isLittleO_atTop_of_delta_littleO_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop] fun n : ℕ => (n : ℝ) ^ (β - 1) := by
  obtain ⟨C, hC0, hC⟩ := circleKernel_integral_bound_nat hβ
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound (R := R) (φ := φ) (β := β) (f := f)
      hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway (R := R) (φ := φ) (δ := δ) (f := f)
      hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))
  have hscale_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop := by
    have hβ1 : 0 < β - 1 := by linarith
    exact (tendsto_rpow_atTop hβ1).comp tendsto_natCast_atTop_atTop
  have hscale_eventually :
      ∀ᶠ n : ℕ in atTop, B / (η / 2) ≤ (n : ℝ) ^ (β - 1) :=
    hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
  have haway_eventually :
      ∀ᶠ n : ℕ in atTop, B ≤ (η / 2) * (n : ℝ) ^ (β - 1) := by
    filter_upwards [hscale_eventually] with n hn
    calc
      B = (η / 2) * (B / (η / 2)) := by
        field_simp [hhalfpos.ne']
      _ ≤ (η / 2) * (n : ℝ) ^ (β - 1) :=
        mul_le_mul_of_nonneg_left hn hhalfpos.le
  filter_upwards [eventually_atTop.mpr ⟨2, fun n hn => hn⟩, haway_eventually]
    with n hn haway_n
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    dsimp [r]
    have hdiv : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn1
    linarith
  have hrpos : 0 < r := by
    dsimp [r]
    have htwo_le : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv_lt : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hnpos]
      linarith
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    have hdiv_pos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
    linarith
  have hrR : r < R := lt_trans hr1 hR
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernel_intervalIntegrable (β := β) hr0 hr1
  have hright_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M)
        volume (-Real.pi) Real.pi :=
    (hkernel_int.const_mul ε).add intervalIntegrable_const
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hleft_int hright_int ?_
    intro θ _hθ
    let z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I)
    have hz_delta : z ∈ DeltaDomainArg R φ :=
      circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal : ‖f z‖ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) :=
        hnear z hz_delta hz_near
      have hMadd :
          ε * ‖(1 : ℂ) - z‖ ^ (-β) ≤
            ε * ‖(1 : ℂ) - z‖ ^ (-β) + M := by
        linarith
      exact hlocal.trans hMadd
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        calc
          ‖z‖ = r := by
            simp [z, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr0]
          _ ≤ 1 := hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      have hkernel_nonneg :
          0 ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) := by positivity
      calc
        ‖f z‖ ≤ M := hbound
        _ ≤ ε * ‖(1 : ℂ) - z‖ ^ (-β) + M := by linarith
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ε * (∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
          M * (2 * Real.pi) := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
          ≤ ∫ θ in (-Real.pi)..Real.pi,
              ε * ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) + M :=
            hInt_le
      _ = ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
            M * (2 * Real.pi) := by
          rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp [mul_comm]
          left
          ring
  have hkernel_nonneg_int :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_
    intro θ _hθ
    positivity
  have hbracket_nonneg :
      0 ≤ ε * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
        M * (2 * Real.pi) := by positivity
  have hpow4 : r⁻¹ ^ n ≤ 4 := by
    dsimp [r]
    exact one_sub_inv_pow_nat_le_four hn
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) ≤
        C * (n : ℝ) ^ (β - 1) := by
    dsimp [r]
    have h := hC n hn1
    simpa [Complex.real_smul] using h
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) := by positivity
  have htransfer_le :
      transferCircleBound f n ≤ A * ε * (n : ℝ) ^ (β - 1) + B := by
    calc
      transferCircleBound f n =
          (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi,
              ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
            simp [transferCircleBound, r]
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
              M * (2 * Real.pi)) := by
            exact mul_le_mul_of_nonneg_left hInt_bound
              (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (∫ θ in (-Real.pi)..Real.pi,
              ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
              M * (2 * Real.pi)) := by
            calc
              (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
                    (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))
                  = (2 * Real.pi)⁻¹ *
                    (r⁻¹ ^ n * (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))) := by
                    ring
              _ ≤ (2 * Real.pi)⁻¹ *
                    (4 * (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi))) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hpow4 hbracket_nonneg)
                      (by positivity)
              _ = (2 * Real.pi)⁻¹ * 4 *
                    (ε * (∫ θ in (-Real.pi)..Real.pi,
                      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β)) +
                      M * (2 * Real.pi)) := by
                    ring
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1)) + M * (2 * Real.pi)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact add_le_add
              (mul_le_mul_of_nonneg_left hkernel_bound hεpos.le) le_rfl
      _ = A * ε * (n : ℝ) ^ (β - 1) + B := by
            dsimp [A, B]
            ring
  have hnear_n :
      A * ε * (n : ℝ) ^ (β - 1) ≤ (η / 2) * (n : ℝ) ^ (β - 1) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg
  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg :
        0 ≤ ∫ θ in (-Real.pi)..Real.pi,
          ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) ?_
      intro θ _hθ
      positivity
    rw [transferCircleBound]
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg
  calc
    ‖transferCircleBound f n‖ = transferCircleBound f n :=
      Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * (n : ℝ) ^ (β - 1) + B := htransfer_le
    _ ≤ (η / 2) * (n : ℝ) ^ (β - 1) +
        (η / 2) * (n : ℝ) ^ (β - 1) :=
      add_le_add hnear_n haway_n
    _ = η * (n : ℝ) ^ (β - 1) := by ring
    _ = η * ‖(n : ℝ) ^ (β - 1)‖ := by
      rw [Real.norm_of_nonneg hscale_nonneg]

private lemma coeff_norm_le_transferCircleBound
    {R φ : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) :
    ∀ᶠ n in atTop, ‖p.coeff n‖ ≤ transferCircleBound f n := by
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hrpos : 0 < r := by
    dsimp [r]
    have htwo_le : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv_lt : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hnpos]
      linarith
    linarith
  have hr1 : r < 1 := by
    dsimp [r]
    have hdiv_pos : 0 < (1 : ℝ) / n := div_pos zero_lt_one hnpos
    linarith
  have hrR : r < R := lt_trans hr1 hR
  have hsubset : Metric.closedBall (0 : ℂ) r ⊆ DeltaDomainArg R φ :=
    closedBall_subset_deltaDomain hr1 hrR hφ0 hφ2
  have hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r) :=
    han.differentiableOn.mono hsubset
  have hcauchy := norm_coeff_le_integral_circle (p := p) hrpos hp hd n
  simpa [transferCircleBound, r] using hcauchy

theorem coeff_norm_isLittleO_atTop_of_delta_littleO_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  have hcircle :=
    transferCircleBound_isLittleO_atTop_of_delta_littleO_beta_gt_one
      (R := R) (φ := φ) (β := β) (f := f) hR hφ0 hφ2 han hf_o hβ
  have hcoeff :=
    coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
      hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n :=
    (norm_nonneg (p.coeff n)).trans hncoeff
  calc
    ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1)‖ := hnbound
