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

/-! ### Log-weighted kernel estimate for the natural-remainder transfer

The natural-remainder logarithmic transfer needs the contour integral of
`‖1-z‖^{-β}·(1+|log‖1-z‖|)` (the strong-remainder transfer used the un-weighted
`‖1-z‖^{-β}`).  The crude uniform bound `-log(ρ²+θ²) ≤ 2 log(1/ρ)` collapses the
log-weighted model integral onto the banked no-log `modelKernel_integral_bound`,
so no new contour estimate is required beyond a pointwise real inequality. -/

/-- Pointwise log majorant: `1 + |log t| ≤ 4 - 2 log t` for `0 < t ≤ 2`. -/
private lemma one_add_abs_log_le_four_sub {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) :
    1 + |Real.log t| ≤ 4 - 2 * Real.log t := by
  by_cases h : t ≤ 1
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le h
    rw [abs_of_nonpos hlog]; linarith
  · have h' : 1 < t := not_le.mp h
    have hlog : 0 ≤ Real.log t := Real.log_nonneg h'.le
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hle1 : Real.log t ≤ 1 := by
      calc Real.log t ≤ Real.log 2 := Real.log_le_log ht0 ht2
        _ ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
        _ = 1 := Real.log_exp 1
    rw [abs_of_nonneg hlog]; linarith

/-- Continuity of `θ ↦ (ρ²+θ²)^{-β/2}` (`ρ > 0`). -/
private lemma model_rpow_continuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) :=
  (continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun θ => Or.inl (by positivity : (0 : ℝ) < ρ ^ 2 + θ ^ 2).ne')

/-- Continuity of `θ ↦ (ρ²+θ²)^{-β/2}·log(ρ²+θ²)` (`ρ > 0`). -/
private lemma model_log_continuous (ρ β : ℝ) (hρ : 0 < ρ) :
    Continuous fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2) :=
  (model_rpow_continuous ρ β hρ).mul
    ((continuous_const.add (continuous_id.pow 2)).log
      (fun θ => (by positivity : (0 : ℝ) < ρ ^ 2 + θ ^ 2).ne'))

/-- **Log-weighted model integral bound** via the crude `-log(ρ²+θ²) ≤ 2 log(1/ρ)`. -/
private lemma modelKernelLog_integral_bound {ρ β K : ℝ}
    (hρ : 0 < ρ) (hρle : ρ ≤ 1) (hβ : 1 < β) (hK : 0 ≤ K) :
    ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * (K - Real.log (ρ ^ 2 + θ ^ 2)) ≤
      (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) * (K + 2 * Real.log (1 / ρ)) := by
  have hm_int : IntervalIntegrable (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      volume (-Real.pi) Real.pi := (model_rpow_continuous ρ β hρ).intervalIntegrable _ _
  have hmK_int : IntervalIntegrable (fun θ : ℝ => K * (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      volume (-Real.pi) Real.pi := hm_int.const_mul K
  have hmlog_int : IntervalIntegrable
      (fun θ : ℝ => (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
      volume (-Real.pi) Real.pi := (model_log_continuous ρ β hρ).intervalIntegrable _ _
  have hlog_inv_nonneg : 0 ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_nonpos hρ.le hρle]
  rw [intervalIntegral.integral_congr
    (g := fun θ => K * (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
      - (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
    (fun θ _ => by ring)]
  rw [intervalIntegral.integral_sub hmK_int hmlog_int, intervalIntegral.integral_const_mul]
  have hmbound : ∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)
      ≤ (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := modelKernel_integral_bound hρ hρle hβ
  have hlog_le : -(∫ θ in (-Real.pi)..Real.pi,
        (ρ ^ 2 + θ ^ 2) ^ (-β / 2) * Real.log (ρ ^ 2 + θ ^ 2))
      ≤ 2 * Real.log (1 / ρ) * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2)) := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hmlog_int.neg (hm_int.const_mul _) (fun θ _ => ?_)
    have hmnn : 0 ≤ (ρ ^ 2 + θ ^ 2) ^ (-β / 2) := by positivity
    have hloglb : -Real.log (ρ ^ 2 + θ ^ 2) ≤ 2 * Real.log (1 / ρ) := by
      have h1 : Real.log (ρ ^ 2) ≤ Real.log (ρ ^ 2 + θ ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg θ])
      have h2 : Real.log (ρ ^ 2) = 2 * Real.log ρ := by
        rw [show ρ ^ 2 = ρ ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      have h3 : Real.log (1 / ρ) = -Real.log ρ := by rw [one_div, Real.log_inv]
      rw [h3]; nlinarith [h1, h2]
    nlinarith [mul_le_mul_of_nonneg_left hloglb hmnn, hmnn]
  have hP : (0 : ℝ) ≤ (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) := by
    have : 0 < β - 1 := by linarith
    have : (0 : ℝ) ≤ ρ ^ (1 - β) := (Real.rpow_pos_of_pos hρ _).le
    positivity
  have hKbound : K * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      ≤ K * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := mul_le_mul_of_nonneg_left hmbound hK
  have h2logbound : 2 * Real.log (1 / ρ) * (∫ θ in (-Real.pi)..Real.pi, (ρ ^ 2 + θ ^ 2) ^ (-β / 2))
      ≤ 2 * Real.log (1 / ρ) * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) :=
    mul_le_mul_of_nonneg_left hmbound (by linarith [hlog_inv_nonneg])
  have hexp : (2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β) * (K + 2 * Real.log (1 / ρ))
      = K * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β))
        + 2 * Real.log (1 / ρ) * ((2 + 2 * (β - 1)⁻¹) * ρ ^ (1 - β)) := by ring
  linarith [hKbound, hlog_le, h2logbound, hexp]

/-- **Log-weighted circle kernel bound.**  For `β > 1` and `n ≥ 2`, the contour integral
of `‖1-z‖^{-β}(1+|log‖1-z‖|)` on the circle of radius `1-1/n` is `≤ C·n^{β-1}·log n`. -/
private lemma circleKernelLog_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
            Complex.exp (θ * Complex.I)‖|))
        ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := by
  have hβ0 : 0 ≤ β := by linarith
  have hπ2pos : (0 : ℝ) < 2 / Real.pi ^ 2 := by positivity
  have hπ2lt1 : 2 / Real.pi ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith [Real.pi_gt_three]
  set K₁ : ℝ := (2 / Real.pi ^ 2) ^ (-β / 2) with hK₁
  set B₀ : ℝ := 2 + 2 * (β - 1)⁻¹ with hB₀
  set K₂ : ℝ := 4 - Real.log (2 / Real.pi ^ 2) with hK₂
  have hβ1pos : (0 : ℝ) < β - 1 := by linarith
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity
  have hK₂pos : 0 < K₂ := by
    rw [hK₂]; have := Real.log_neg hπ2pos hπ2lt1; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K₁ * B₀ * (K₂ / Real.log 2 + 2), by positivity, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set r : ℝ := (1 : ℝ) - (1 : ℝ) / n with hr_def
  have hρeq : (1 : ℝ) - r = 1 / n := by rw [hr_def]; ring
  have hr_half : (1 : ℝ) / 2 ≤ r := by
    have hle : (1 : ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn2R
    rw [hr_def]; linarith
  have hr1 : r < 1 := by
    have hpos : 0 < (1 : ℝ) / n := by positivity
    rw [hr_def]; linarith
  have h1r : 0 < 1 - r := by rw [hρeq]; positivity
  -- pointwise contour bound
  have hpt : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)
      ≤ K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := by
    intro θ hθ
    have hθabs : |θ| ≤ Real.pi := abs_le.mpr ⟨hθ.1, hθ.2⟩
    set w : ℝ := ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ with hw
    have hwpos : 0 < w := by
      rw [hw, norm_pos_iff, sub_ne_zero]
      intro hcon
      have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by rw [← hcon]; simp
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hnorm
      linarith
    have hwle2 : w ≤ 2 := by
      rw [hw]
      calc ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖
          ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_sub_le _ _
        _ = 1 + r := by
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)]; norm_num
        _ ≤ 2 := by linarith
    have hwbound : w ^ (-β) ≤ K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) :=
      circleKernel_rpow_le_model r θ β hθabs hr_half h1r hβ0
    have hsqlb : (2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2) ≤ w ^ 2 :=
      circleKernel_norm_sq_lower r θ hθabs hr_half
    have hApos : 0 < (1 - r) ^ 2 + θ ^ 2 := by nlinarith [sq_pos_of_pos h1r, sq_nonneg θ]
    have hlogbound : 1 + |Real.log w| ≤ K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2) := by
      have hstep1 : 1 + |Real.log w| ≤ 4 - 2 * Real.log w :=
        one_add_abs_log_le_four_sub hwpos hwle2
      have hlogsq : 2 * Real.log w = Real.log (w ^ 2) := by
        rw [Real.log_pow]; push_cast; ring
      have hmono : Real.log ((2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2)) ≤ Real.log (w ^ 2) :=
        Real.log_le_log (by positivity) hsqlb
      have hsplit : Real.log ((2 / Real.pi ^ 2) * ((1 - r) ^ 2 + θ ^ 2))
          = Real.log (2 / Real.pi ^ 2) + Real.log ((1 - r) ^ 2 + θ ^ 2) :=
        Real.log_mul (by positivity) (by positivity)
      rw [hK₂]; nlinarith [hstep1, hlogsq, hmono, hsplit]
    have hKnn : 0 ≤ K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2) := by
      have h1le : (1 : ℝ) ≤ 1 + |Real.log w| := le_add_of_nonneg_right (abs_nonneg _)
      linarith [hlogbound, h1le]
    have hwbnn : 0 ≤ w ^ (-β) := by positivity
    have hmodnn : 0 ≤ K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) := by positivity
    calc w ^ (-β) * (1 + |Real.log w|)
        ≤ (K₁ * ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)) :=
          mul_le_mul hwbound hlogbound (by positivity) hmodnn
      _ = K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2) * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := by
          ring
  -- integrability of both sides
  have hg : Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)))).norm
  have hgne : ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [← sub_eq_zero.mp hcon]; simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ r)] at hnorm
    linarith
  have hgpos : ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  have hLHS_int : IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
      volume (-Real.pi) Real.pi :=
    ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
      (continuous_const.add (hg.log (fun θ => (hgpos θ).ne')).abs)).intervalIntegrable _ _
  have hRHS_int : IntervalIntegrable
      (fun θ : ℝ => K₁ * (((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
        * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)))) volume (-Real.pi) Real.pi := by
    have : Continuous fun θ : ℝ => ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
        * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2)) := by
      have hbase : Continuous fun θ : ℝ => (1 - r) ^ 2 + θ ^ 2 :=
        continuous_const.add (continuous_id.pow 2)
      exact (hbase.rpow_const (fun θ => Or.inl (by positivity : (0:ℝ) < (1-r)^2+θ^2).ne')).mul
        (continuous_const.sub (hbase.log (fun θ => (by positivity : (0:ℝ) < (1-r)^2+θ^2).ne')))
    exact (this.const_mul K₁).intervalIntegrable _ _
  -- integrate the pointwise bound, then apply the model bound
  have hint_le := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    hLHS_int hRHS_int hpt
  rw [intervalIntegral.integral_const_mul] at hint_le
  have hmodel := modelKernelLog_integral_bound (ρ := 1 - r) (β := β) (K := K₂)
    h1r (by rw [hρeq, div_le_one hnpos]; exact_mod_cast hnpos_nat) hβ hK₂pos.le
  have hconv : (1 - r) ^ (1 - β) = (n : ℝ) ^ (β - 1) := by
    rw [hρeq, one_div, Real.inv_rpow hnpos.le, ← Real.rpow_neg hnpos.le]
    congr 1; ring
  have hloginv : Real.log (1 / (1 - r)) = Real.log n := by rw [hρeq, one_div_one_div]
  rw [hconv, hloginv, ← hB₀] at hmodel
  -- chain: LHS ≤ K₁ * (B₀ n^{β-1}(K₂+2log n)) ≤ C n^{β-1} log n
  have hlogn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2R
  have hnp0 : 0 ≤ (n : ℝ) ^ (β - 1) := (Real.rpow_pos_of_pos hnpos _).le
  have hKstep : K₂ + 2 * Real.log n ≤ (K₂ / Real.log 2 + 2) * Real.log n := by
    have h1 : K₂ = (K₂ / Real.log 2) * Real.log 2 := by field_simp
    have h2 : (K₂ / Real.log 2) * Real.log 2 ≤ (K₂ / Real.log 2) * Real.log n :=
      mul_le_mul_of_nonneg_left hlogn2 (by positivity)
    nlinarith [h1, h2]
  have hcoef : 0 ≤ K₁ * B₀ * (n : ℝ) ^ (β - 1) := mul_nonneg (mul_nonneg hK₁0 hB₀0) hnp0
  have hfinal : K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n))
      ≤ K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := by
    calc K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n))
        = K₁ * B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n) := by ring
      _ ≤ K₁ * B₀ * (n : ℝ) ^ (β - 1) * ((K₂ / Real.log 2 + 2) * Real.log n) :=
          mul_le_mul_of_nonneg_left hKstep hcoef
      _ = K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := by ring
  calc ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)
      ≤ K₁ * (∫ θ in (-Real.pi)..Real.pi, ((1 - r) ^ 2 + θ ^ 2) ^ (-β / 2)
          * (K₂ - Real.log ((1 - r) ^ 2 + θ ^ 2))) := hint_le
    _ ≤ K₁ * (B₀ * (n : ℝ) ^ (β - 1) * (K₂ + 2 * Real.log n)) :=
        mul_le_mul_of_nonneg_left hmodel hK₁0
    _ ≤ K₁ * B₀ * (K₂ / Real.log 2 + 2) * (n : ℝ) ^ (β - 1) * Real.log n := hfinal

/-- Integrability of the log-weighted circle kernel integrand. -/
private lemma circleKernelLog_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
      volume (-Real.pi) Real.pi := by
  have hg : Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))).norm
  have hgne : ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [← sub_eq_zero.mp hcon]; simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0] at hnorm
    linarith
  have hgpos : ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  exact ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
    (continuous_const.add (hg.log (fun θ => (hgpos θ).ne')).abs)).intervalIntegrable _ _

/-- Extract a pointwise `(1+|log|)`-weighted bound from the log-weighted little-o hypothesis. -/
private lemma exists_delta_littleO_kernel_bound_log
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|)) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hf_o ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, fun z hz hnear => ?_⟩
  have hnear0 : ‖(1 : ℂ) - z‖ < δ₀ := lt_of_lt_of_le hnear (min_le_left _ _)
  have hnear1 : ‖(1 : ℂ) - z‖ < 1 := lt_of_lt_of_le hnear (min_le_right _ _)
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]; simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hlogneg : Real.log ‖(1 : ℂ) - z‖ ≤ 0 := Real.log_nonpos hnorm_pos.le hnear1.le
  have hlogeq : Real.log (‖(1 : ℂ) - z‖⁻¹) = |Real.log ‖(1 : ℂ) - z‖| := by
    rw [Real.log_inv, abs_of_nonpos hlogneg]
  have hloginv_pos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]; have := Real.log_neg hnorm_pos hnear1; linarith
  have hdist_z : dist z (1 : ℂ) < δ₀ := by simpa [dist_eq_norm, norm_sub_rev] using hnear0
  have hratio := hδ₀ hz hdist_z
  have hratio_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ := by
    positivity
  have hratio_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹ < ε := by
    have h := hratio
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg] at h
    exact h
  have hXL : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹
      = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) / Real.log (‖(1 : ℂ) - z‖⁻¹) := by rw [div_eq_mul_inv]
  rw [hXL] at hratio_lt
  have hstep : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε * Real.log (‖(1 : ℂ) - z‖⁻¹) :=
    (div_lt_iff₀ hloginv_pos).mp hratio_lt
  have hpow_mul : ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos]; simp
  calc ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) * ‖(1 : ℂ) - z‖ ^ (-β) := by
        rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ (ε * Real.log (‖(1 : ℂ) - z‖⁻¹)) * ‖(1 : ℂ) - z‖ ^ (-β) :=
        mul_le_mul_of_nonneg_right hstep.le (by positivity)
    _ = ε * (‖(1 : ℂ) - z‖ ^ (-β) * Real.log (‖(1 : ℂ) - z‖⁻¹)) := by ring
    _ ≤ ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|)) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hlogeq]; linarith [abs_nonneg (Real.log ‖(1 : ℂ) - z‖)]

/-- **Log-weighted little-o circle transfer.**  Under the natural-remainder hypothesis
`‖f z‖·‖1-z‖^β / log(1/‖1-z‖) → 0`, the Cauchy bound is `o(n^{β-1} log n)`. -/
private lemma transferCircleBoundLog_isLittleO
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop] fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n := by
  obtain ⟨C, hC0, hC⟩ := circleKernelLog_integral_bound_nat hβ
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hA1pos : 0 < A + 1 := by linarith
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound_log (R := R) (φ := φ) (β := β) (f := f) hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway (R := R) (φ := φ) (δ := δ) (f := f) hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))
  have hscale_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀
      ((tendsto_rpow_atTop (by linarith : (0:ℝ) < β - 1)).comp tendsto_natCast_atTop_atTop)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have haway_eventually :
      ∀ᶠ n : ℕ in atTop, B ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) := by
    have := hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
    filter_upwards [this] with n hn
    calc B = (η / 2) * (B / (η / 2)) := by field_simp
      _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) := mul_le_mul_of_nonneg_left hn hhalfpos.le
  filter_upwards [eventually_atTop.mpr ⟨2, fun n hn => hn⟩, haway_eventually]
    with n hn haway_n
  have hn1 : 1 ≤ n := le_trans (by norm_num : (1 : ℕ) ≤ 2) hn
  have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast hn1
    dsimp [r]; linarith
  have hrpos : 0 < r := by
    have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) / n < 1 := by rw [div_lt_one hnpos]; linarith
    dsimp [r]; linarith
  have hr1 : r < 1 := by
    have : 0 < (1 : ℝ) / n := by positivity
    dsimp [r]; linarith
  have hrR : r < R := lt_trans hr1 hR
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) * Real.log n := by
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    positivity
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernelLog_intervalIntegrable (β := β) (r := r) hr0 hr1
  have hright_int : IntervalIntegrable
      (fun θ : ℝ => ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) + M)
      volume (-Real.pi) Real.pi := (hkernel_int.const_mul ε).add intervalIntegrable_const
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hleft_int hright_int ?_
    intro θ _hθ
    set z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hz
    have hz_delta : z ∈ DeltaDomainArg R φ := circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    have hknn : 0 ≤ ‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|) := by positivity
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal := hnear z hz_delta hz_near
      nlinarith [hlocal, hM0]
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0]; exact hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      nlinarith [hbound, mul_nonneg hεpos.le hknn]
  have hr_inv4 : r⁻¹ ^ n ≤ 4 := by dsimp [r]; exact one_sub_inv_pow_nat_le_four hn
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
        ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := by
    have h := hC n hn
    dsimp [r]; convert h using 3 <;> norm_num
  have hkernel_nonneg :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) := by
    refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi) := by
    refine hInt_le.trans ?_
    rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have h1 : ε * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
        ≤ ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) :=
      mul_le_mul_of_nonneg_left hkernel_bound hεpos.le
    have h2 : (Real.pi - -Real.pi) • M ≤ M * (2 * Real.pi) := by
      rw [smul_eq_mul]; nlinarith [hM0, Real.pi_pos]
    linarith [h1, h2]
  have htransfer_le : transferCircleBound f n ≤ A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := by
    have hbracket_nonneg : 0 ≤ ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi) := by
      have : 0 ≤ C * (n : ℝ) ^ (β - 1) * Real.log n := le_trans hkernel_nonneg hkernel_bound
      positivity
    have hI_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    have hpi_inv : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    calc transferCircleBound f n
        = (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
          simp [transferCircleBound, r]
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hInt_bound
            (mul_nonneg hpi_inv (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1) * Real.log n) + M * (2 * Real.pi)) := by
          have hstep := mul_le_mul_of_nonneg_right hr_inv4 hbracket_nonneg
          nlinarith [hstep, hbracket_nonneg, mul_nonneg hpi_inv hbracket_nonneg, Real.pi_pos,
            mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0) n) hbracket_nonneg]
      _ = A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := by dsimp [A, B]; ring
  have hnear_n : A * ε * ((n : ℝ) ^ (β - 1) * Real.log n)
      ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg
  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    rw [transferCircleBound]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg
  calc ‖transferCircleBound f n‖ = transferCircleBound f n := Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * ((n : ℝ) ^ (β - 1) * Real.log n) + B := htransfer_le
    _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) + (η / 2) * ((n : ℝ) ^ (β - 1) * Real.log n) :=
        add_le_add hnear_n haway_n
    _ = η * ((n : ℝ) ^ (β - 1) * Real.log n) := by ring
    _ = η * ‖(n : ℝ) ^ (β - 1) * Real.log n‖ := by rw [Real.norm_of_nonneg hscale_nonneg]

/-- **Coefficient-level natural-remainder little-o transfer** (`β > 1`):
`‖f z‖·‖1-z‖^β / log(1/‖1-z‖) → 0` ⟹ `‖[zⁿ]f‖ = o(n^{β-1} log n)`. -/
theorem coeff_norm_isLittleO_atTop_of_delta_littleO_log_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * (Real.log (‖(1 : ℂ) - z‖⁻¹))⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (β - 1) * Real.log n) := by
  have hcircle := transferCircleBoundLog_isLittleO (R := R) (φ := φ) (β := β) (f := f)
    hR hφ0 hφ2 han hf_o hβ
  have hcoeff := coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
    hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n := (norm_nonneg (p.coeff n)).trans hncoeff
  calc ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1) * Real.log n‖ := hnbound

/-! ### Squared-log-weighted kernel + little-o transfer (natural-remainder log²) -/

/-- On the Cauchy circle of radius `1-1/n` (`n ≥ 2`), `|log‖1-z‖| ≤ log n`. -/
private lemma abs_log_circle_le {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    |Real.log ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖|
      ≤ Real.log n := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set r : ℝ := (1 : ℝ) - (1 : ℝ) / n with hr
  have hr0 : 0 ≤ r := by
    rw [hr]; have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact hn1
    linarith
  have hexpn : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  set w : ℝ := ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ with hw
  have hznorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 - 1 / n := by
    rw [norm_mul, hexpn, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0, hr]
  have hwle : w ≤ 2 := by
    rw [hw]
    calc ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ := norm_sub_le _ _
      _ = 1 + (1 - 1 / n) := by rw [hznorm, norm_one]
      _ ≤ 2 := by have h := (by positivity : (0 : ℝ) < (1 : ℝ) / n); linarith
  have hwge : (1 : ℝ) / n ≤ w := one_sub_norm_ge_on_circle (by omega : 1 ≤ n) hznorm
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity) hwge
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < 1 / n) hwge
    rw [Real.log_div one_ne_zero hnpos.ne', Real.log_one, zero_sub] at h
    linarith
  · calc Real.log w ≤ Real.log 2 := Real.log_le_log hwpos hwle
      _ ≤ Real.log n := Real.log_le_log (by norm_num) hn2

/-- Integrability of the squared-log circle kernel integrand. -/
private lemma circleKernelLogSq_intervalIntegrable {β r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2)
      volume (-Real.pi) Real.pi := by
  have hg : Continuous fun θ : ℝ => ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))).norm
  have hgne : ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by rw [← sub_eq_zero.mp hcon]; simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0] at hnorm
    linarith
  have hgpos : ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  exact ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
    ((continuous_const.add (hg.log (fun θ => (hgpos θ).ne')).abs).pow 2)).intervalIntegrable _ _

/-- **Squared-log circle kernel bound**: reuses the log-weighted kernel times `(1+log n)`. -/
private lemma circleKernelLogSq_integral_bound_nat {β : ℝ} (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
            Complex.exp (θ * Complex.I)‖|) ^ 2)
        ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := circleKernelLog_integral_bound_nat hβ
  refine ⟨2 * C₁, by positivity, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hlognpos : 0 ≤ Real.log n := by linarith
  set r : ℝ := (1 : ℝ) - (1 : ℝ) / n with hr
  have hnpos : 0 < (n : ℝ) := by positivity
  have hr0 : 0 ≤ r := by
    rw [hr]; have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have hr1 : r < 1 := by rw [hr]; have h := (by positivity : (0 : ℝ) < (1 : ℝ) / n); linarith
  -- pointwise: (1+|log w|)² ≤ (1+log n)·(1+|log w|)
  have hint_mono : (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2)
      ≤ ∫ θ in (-Real.pi)..Real.pi,
          (1 + Real.log n) * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (circleKernelLogSq_intervalIntegrable hr0 hr1)
      ((circleKernelLog_intervalIntegrable hr0 hr1).const_mul _) (fun θ _ => ?_)
    have hlogw : |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖| ≤ Real.log n := by
      exact abs_log_circle_le hn2 θ
    have habs0 : 0 ≤ |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖| := abs_nonneg _
    have hwpow : 0 ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) := by positivity
    have hsq : (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2
        ≤ (1 + Real.log n) * (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) := by
      rw [pow_two]
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      linarith
    calc ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2
        ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            ((1 + Real.log n) * (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) :=
          mul_le_mul_of_nonneg_left hsq hwpow
      _ = (1 + Real.log n) * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|)) := by ring
  rw [intervalIntegral.integral_const_mul] at hint_mono
  have hlog1 := hC₁ n (by omega : 2 ≤ n)
  have hstep : (1 + Real.log n) * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|))
      ≤ (1 + Real.log n) * (C₁ * (n : ℝ) ^ (β - 1) * Real.log n) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [hr]; exact hlog1
  refine le_trans hint_mono (le_trans hstep ?_)
  -- (1+log n)·C₁·n^{β-1}·log n ≤ 2C₁·n^{β-1}·(log n)²
  have hnp : 0 ≤ (n : ℝ) ^ (β - 1) := (Real.rpow_pos_of_pos hnpos _).le
  have h1logle : 1 + Real.log n ≤ 2 * Real.log n := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h1logle (by positivity : (0:ℝ) ≤ C₁ * (n:ℝ)^(β-1) * Real.log n),
    hC₁0, hnp, hlognpos]

/-- Extract a pointwise `(1+|log|)²`-weighted bound from the log²-weighted little-o hypothesis. -/
private lemma exists_delta_littleO_kernel_bound_logSq
    {R φ β ε : ℝ} {f : ℂ → ℂ}
    (hf_o : Tendsto
      (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ 2) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hf_o ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, fun z hz hnear => ?_⟩
  have hnear0 : ‖(1 : ℂ) - z‖ < δ₀ := lt_of_lt_of_le hnear (min_le_left _ _)
  have hnear1 : ‖(1 : ℂ) - z‖ < 1 := lt_of_lt_of_le hnear (min_le_right _ _)
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]; simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hlogneg : Real.log ‖(1 : ℂ) - z‖ ≤ 0 := Real.log_nonpos hnorm_pos.le hnear1.le
  have hlogeq : Real.log (‖(1 : ℂ) - z‖⁻¹) = |Real.log ‖(1 : ℂ) - z‖| := by
    rw [Real.log_inv, abs_of_nonpos hlogneg]
  have hloginv_pos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]; have := Real.log_neg hnorm_pos hnear1; linarith
  have hsqpos : 0 < (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2 := by positivity
  have hdist_z : dist z (1 : ℂ) < δ₀ := by simpa [dist_eq_norm, norm_sub_rev] using hnear0
  have hratio := hδ₀ hz hdist_z
  have hratio_nonneg : 0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹ := by
    positivity
  have hratio_lt : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹ < ε := by
    have h := hratio
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg] at h
    exact h
  have hXL : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹
      = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) / (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2 := by rw [div_eq_mul_inv]
  rw [hXL] at hratio_lt
  have hstep : ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β < ε * (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2 :=
    (div_lt_iff₀ hsqpos).mp hratio_lt
  have hpow_mul : ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos]; simp
  have hmaj : (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2 ≤ (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ 2 := by
    rw [hlogeq]
    have h1 : |Real.log ‖(1 : ℂ) - z‖| ≤ 1 + |Real.log ‖(1 : ℂ) - z‖| := by linarith [abs_nonneg (Real.log ‖(1 : ℂ) - z‖)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ‖f z‖ = (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) * ‖(1 : ℂ) - z‖ ^ (-β) := by
        rw [mul_assoc, hpow_mul, mul_one]
    _ ≤ (ε * (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2) * ‖(1 : ℂ) - z‖ ^ (-β) :=
        mul_le_mul_of_nonneg_right hstep.le (by positivity)
    _ ≤ (ε * (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ 2) * ‖(1 : ℂ) - z‖ ^ (-β) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hmaj hε.le
    _ = ε * (‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ 2) := by ring

/-- **Log²-weighted little-o circle transfer.** -/
private lemma transferCircleBoundLogSq_isLittleO
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto
      (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop] fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := circleKernelLogSq_integral_bound_nat hβ
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]; field_simp [hdenpos.ne']; nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound_logSq (R := R) (φ := φ) (β := β) (f := f) hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway (R := R) (φ := φ) (δ := δ) (f := f) hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))
  have hscale_atTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) atTop atTop := by
    have hr : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0:ℝ) < β - 1)).comp tendsto_natCast_atTop_atTop
    have hl : Tendsto (fun n : ℕ => (Real.log n) ^ 2) atTop atTop := by
      have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      simpa [pow_two] using hlog.atTop_mul_atTop₀ hlog
    exact hr.atTop_mul_atTop₀ hl
  have haway_eventually :
      ∀ᶠ n : ℕ in atTop, B ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) := by
    have := hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
    filter_upwards [this] with n hn
    calc B = (η / 2) * (B / (η / 2)) := by field_simp
      _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) := mul_le_mul_of_nonneg_left hn hhalfpos.le
  filter_upwards [eventually_atTop.mpr ⟨3, fun n hn => hn⟩, haway_eventually] with n hn haway_n
  have hn1 : 1 ≤ n := by omega
  have hnpos_nat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    have h : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast hn1
    dsimp [r]; linarith
  have hrpos : 0 < r := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have h : (1 : ℝ) / n < 1 := by rw [div_lt_one hnpos]; linarith
    dsimp [r]; linarith
  have hr1 : r < 1 := by
    have h : 0 < (1 : ℝ) / n := by positivity
    dsimp [r]; linarith
  have hrR : r < R := lt_trans hr1 hR
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2 := by
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    positivity
  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int := circleKernelLogSq_intervalIntegrable (β := β) (r := r) hr0 hr1
  have hright_int : IntervalIntegrable
      (fun θ : ℝ => ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
        (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2) + M)
      volume (-Real.pi) Real.pi := (hkernel_int.const_mul ε).add intervalIntegrable_const
  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ∫ θ in (-Real.pi)..Real.pi,
          ε * (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hleft_int hright_int ?_
    intro θ _hθ
    set z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hz
    have hz_delta : z ∈ DeltaDomainArg R φ := circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    have hknn : 0 ≤ ‖(1 : ℂ) - z‖ ^ (-β) * (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ 2 := by positivity
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal := hnear z hz_delta hz_near
      nlinarith [hlocal, hM0]
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0]; exact hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      nlinarith [hbound, mul_nonneg hεpos.le hknn]
  have hr_inv4 : r⁻¹ ^ n ≤ 4 := by dsimp [r]; exact one_sub_inv_pow_nat_le_four (by omega : 2 ≤ n)
  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2)
        ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2 := by
    have h := hC n hn
    dsimp [r]; convert h using 3 <;> norm_num
  have hkernel_nonneg :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖) ≤
        ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + M * (2 * Real.pi) := by
    refine hInt_le.trans ?_
    rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have h1 : ε * (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖|) ^ 2)
        ≤ ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) :=
      mul_le_mul_of_nonneg_left hkernel_bound hεpos.le
    have h2 : (Real.pi - -Real.pi) • M ≤ M * (2 * Real.pi) := by
      rw [smul_eq_mul]; nlinarith [hM0, Real.pi_pos]
    linarith [h1, h2]
  have htransfer_le : transferCircleBound f n
      ≤ A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + B := by
    have hbracket_nonneg : 0 ≤ ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + M * (2 * Real.pi) := by
      have : 0 ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2 := le_trans hkernel_nonneg hkernel_bound
      positivity
    have hpi_inv : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    calc transferCircleBound f n
        = (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
          simp [transferCircleBound, r]
      _ ≤ (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + M * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hInt_bound
            (mul_nonneg hpi_inv (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤ (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + M * (2 * Real.pi)) := by
          have hstep := mul_le_mul_of_nonneg_right hr_inv4 hbracket_nonneg
          nlinarith [hstep, hbracket_nonneg, mul_nonneg hpi_inv hbracket_nonneg, Real.pi_pos,
            mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0) n) hbracket_nonneg]
      _ = A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + B := by dsimp [A, B]; ring
  have hnear_n : A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2)
      ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg
  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg : 0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    rw [transferCircleBound]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg
  calc ‖transferCircleBound f n‖ = transferCircleBound f n := Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) + B := htransfer_le
    _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2)
        + (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) := add_le_add hnear_n haway_n
    _ = η * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) := by ring
    _ = η * ‖(n : ℝ) ^ (β - 1) * (Real.log n) ^ 2‖ := by rw [Real.norm_of_nonneg hscale_nonneg]

/-! ### Log^k-weighted circle kernel (k ≥ 1), reducing to the banked log¹ kernel. -/

private lemma one_add_pow_le_pred_mul_one_add_of_le {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    (1 + a) ^ k ≤ (1 + b) ^ (k - 1) * (1 + a) := by
  cases k with
  | zero =>
      simp
      linarith
  | succ m =>
      have h1a0 : 0 ≤ 1 + a := by linarith
      have hbase : 1 + a ≤ 1 + b := by linarith
      have hpow : (1 + a) ^ m ≤ (1 + b) ^ m :=
        pow_le_pow_left₀ h1a0 hbase m
      calc
        (1 + a) ^ Nat.succ m = (1 + a) ^ m * (1 + a) := by
          rw [pow_succ]
        _ ≤ (1 + b) ^ m * (1 + a) :=
          mul_le_mul_of_nonneg_right hpow h1a0
        _ = (1 + b) ^ (Nat.succ m - 1) * (1 + a) := by
          simp

/-- Integrability of the `log^k` circle kernel integrand. -/
private lemma circleKernelLogK_intervalIntegrable {β r : ℝ} (k : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖|) ^ k)
      volume (-Real.pi) Real.pi := by
  have hg : Continuous fun θ : ℝ =>
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)))).norm
  have hgne :
      ∀ θ : ℝ, (1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
    intro θ hcon
    have hnorm : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [← sub_eq_zero.mp hcon]
      simp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0] at hnorm
    linarith
  have hgpos :
      ∀ θ : ℝ, 0 < ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
    fun θ => norm_pos_iff.mpr (hgne θ)
  exact
    ((hg.rpow_const (fun θ => Or.inl (hgpos θ).ne')).mul
      ((continuous_const.add
        (hg.log (fun θ => (hgpos θ).ne')).abs).pow k)).intervalIntegrable _ _

/--
`log^k` circle-kernel bound.

For `k = 0`, this is the banked no-log circle kernel.  For `k = m+1`,
the pointwise estimate
`(1+|log w|)^(m+1) ≤ (1+log n)^m * (1+|log w|)`
reduces the integral to the banked log¹ kernel, then
`1 + log n ≤ 2 log n` for `n ≥ 3`.
-/

private lemma circleKernelLogK_integral_bound_nat {β : ℝ} (hβ : 1 < β) {k : ℕ}
    (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
            Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) -
            (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
              Complex.exp (θ * Complex.I)‖|) ^ k)
        ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨C₁, hC₁0, hC₁⟩ := circleKernelLog_integral_bound_nat hβ
  refine ⟨(2 : ℝ) ^ m * C₁, ?_, fun n hn => ?_⟩
  · exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m) hC₁0
  · have hn2 : 2 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hnpos_nat : 0 < n := by omega
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn

    have hlogn1 : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hnpos]
      have := Real.exp_one_lt_d9
      linarith
    have hlognpos : 0 ≤ Real.log n := by linarith
    have h1log_nonneg : 0 ≤ 1 + Real.log n := by linarith

    set r : ℝ := (1 : ℝ) - (1 : ℝ) / n with hr
    have hr0 : 0 ≤ r := by
      rw [hr]
      have hdiv : (1 : ℝ) / n ≤ 1 := by
        rw [div_le_one hnpos]
        exact_mod_cast hn1
      linarith
    have hr1 : r < 1 := by
      rw [hr]
      have hdiv_pos : 0 < (1 : ℝ) / n := by positivity
      linarith

    have hint_mono :
        (∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
              Complex.exp (θ * Complex.I)‖|) ^ (1 + m))
        ≤ ∫ θ in (-Real.pi)..Real.pi,
            (1 + Real.log n) ^ m *
              (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
                (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                  Complex.exp (θ * Complex.I)‖|)) := by
      refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        (circleKernelLogK_intervalIntegrable (β := β) (r := r) (1 + m) hr0 hr1)
        ((circleKernelLog_intervalIntegrable (β := β) (r := r) hr0 hr1).const_mul _)
        ?_
      intro θ _hθ
      have hlogw :
          |Real.log ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖| ≤ Real.log n := by
        rw [hr]
        exact abs_log_circle_le hn2 θ
      have hwpow :
          0 ≤ ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖ ^ (-β) := by
        positivity
      have hweight :
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖|) ^ (1 + m)
            ≤ (1 + Real.log n) ^ m *
              (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                Complex.exp (θ * Complex.I)‖|) := by
        have hpred : (1 + m) - 1 = m := by omega
        simpa [hpred] using
          one_add_pow_le_pred_mul_one_add_of_le
            (a := |Real.log ‖(1 : ℂ) - (r : ℂ) *
              Complex.exp (θ * Complex.I)‖|)
            (b := Real.log n)
            (abs_nonneg _) hlogw (1 + m)
      calc
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
              Complex.exp (θ * Complex.I)‖|) ^ (1 + m)
            ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
              ((1 + Real.log n) ^ m *
                (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                  Complex.exp (θ * Complex.I)‖|)) :=
          mul_le_mul_of_nonneg_left hweight hwpow
        _ = (1 + Real.log n) ^ m *
              (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
                (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                  Complex.exp (θ * Complex.I)‖|)) := by
          ring

    rw [intervalIntegral.integral_const_mul] at hint_mono

    have hlog1 :
        (∫ θ in (-Real.pi)..Real.pi,
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
              Complex.exp (θ * Complex.I)‖|))
        ≤ C₁ * (n : ℝ) ^ (β - 1) * Real.log n := by
      rw [hr]
      exact hC₁ n hn2

    have hstep :
        (1 + Real.log n) ^ m *
          (∫ θ in (-Real.pi)..Real.pi,
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
              (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                Complex.exp (θ * Complex.I)‖|))
        ≤ (1 + Real.log n) ^ m *
            (C₁ * (n : ℝ) ^ (β - 1) * Real.log n) :=
      mul_le_mul_of_nonneg_left hlog1 (pow_nonneg h1log_nonneg m)

    have h1logle : 1 + Real.log n ≤ 2 * Real.log n := by
      linarith
    have hpowle : (1 + Real.log n) ^ m ≤ (2 * Real.log n) ^ m :=
      pow_le_pow_left₀ h1log_nonneg h1logle m
    have hnp : 0 ≤ (n : ℝ) ^ (β - 1) :=
      (Real.rpow_pos_of_pos hnpos _).le
    have hcoef_nonneg :
        0 ≤ C₁ * (n : ℝ) ^ (β - 1) * Real.log n :=
      mul_nonneg (mul_nonneg hC₁0 hnp) hlognpos
    have hlogpow :
        (Real.log n) ^ m * Real.log n = (Real.log n) ^ (1 + m) := by
      rw [show (1 + m : ℕ) = m + 1 by omega, pow_succ]

    have hfinal :
        (1 + Real.log n) ^ m *
            (C₁ * (n : ℝ) ^ (β - 1) * Real.log n)
          ≤ ((2 : ℝ) ^ m * C₁) * (n : ℝ) ^ (β - 1) *
              (Real.log n) ^ (1 + m) := by
      calc
        (1 + Real.log n) ^ m *
            (C₁ * (n : ℝ) ^ (β - 1) * Real.log n)
            ≤ (2 * Real.log n) ^ m *
                (C₁ * (n : ℝ) ^ (β - 1) * Real.log n) :=
          mul_le_mul_of_nonneg_right hpowle hcoef_nonneg
        _ = ((2 : ℝ) ^ m * C₁) * (n : ℝ) ^ (β - 1) *
              (Real.log n) ^ (1 + m) := by
          rw [mul_pow, ← hlogpow]
          ring

    calc
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
            Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) -
            (((1 : ℝ) - (1 : ℝ) / n : ℝ) : ℂ) *
              Complex.exp (θ * Complex.I)‖|) ^ (1 + m))
          ≤ (1 + Real.log n) ^ m *
              (∫ θ in (-Real.pi)..Real.pi,
                ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
                  (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                    Complex.exp (θ * Complex.I)‖|)) := by
            simpa [hr] using hint_mono
      _ ≤ (1 + Real.log n) ^ m *
            (C₁ * (n : ℝ) ^ (β - 1) * Real.log n) := hstep
      _ ≤ ((2 : ℝ) ^ m * C₁) * (n : ℝ) ^ (β - 1) *
            (Real.log n) ^ (1 + m) := hfinal


/-! ### Log^k bridge: kernel → coefficient little-o (k ≥ 1). -/

private lemma exists_delta_littleO_kernel_bound_logK
    {R φ β ε : ℝ} {f : ℂ → ℂ} (k : ℕ)
    (hf_o : Tendsto
      (fun z : ℂ =>
        ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β *
          ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ z ∈ DeltaDomainArg R φ, ‖(1 : ℂ) - z‖ < δ →
      ‖f z‖ ≤ ε *
        (‖(1 : ℂ) - z‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ k) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf_o
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hf_o ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, fun z hz hnear => ?_⟩
  have hnear0 : ‖(1 : ℂ) - z‖ < δ₀ := lt_of_lt_of_le hnear (min_le_left _ _)
  have hnear1 : ‖(1 : ℂ) - z‖ < 1 := lt_of_lt_of_le hnear (min_le_right _ _)
  have hz_ne : z ≠ 1 := hz.2.1
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ := by
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz_ne)
  have hlogneg : Real.log ‖(1 : ℂ) - z‖ ≤ 0 :=
    Real.log_nonpos hnorm_pos.le hnear1.le
  have hlogeq :
      Real.log (‖(1 : ℂ) - z‖⁻¹) = |Real.log ‖(1 : ℂ) - z‖| := by
    rw [Real.log_inv, abs_of_nonpos hlogneg]
  have hloginv_pos : 0 < Real.log (‖(1 : ℂ) - z‖⁻¹) := by
    rw [Real.log_inv]
    have := Real.log_neg hnorm_pos hnear1
    linarith
  have hlogpow_pos : 0 < (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k :=
    pow_pos hloginv_pos k
  have hdist_z : dist z (1 : ℂ) < δ₀ := by
    simpa [dist_eq_norm, norm_sub_rev] using hnear0
  have hratio := hδ₀ hz hdist_z
  have hratio_nonneg :
      0 ≤ ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β *
        ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹ := by
    positivity
  have hratio_lt :
      ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β *
          ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹ < ε := by
    have h := hratio
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hratio_nonneg] at h
    exact h
  have hXL :
      ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β *
          ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹
        =
      (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) /
        (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k := by
    rw [div_eq_mul_inv]
  rw [hXL] at hratio_lt
  have hstep :
      ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β <
        ε * (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k :=
    (div_lt_iff₀ hlogpow_pos).mp hratio_lt
  have hpow_mul :
      ‖(1 : ℂ) - z‖ ^ β * ‖(1 : ℂ) - z‖ ^ (-β) = 1 := by
    rw [← Real.rpow_add hnorm_pos]
    simp
  have hmaj :
      (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k
        ≤ (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ k := by
    rw [hlogeq]
    have h1 :
        |Real.log ‖(1 : ℂ) - z‖|
          ≤ 1 + |Real.log ‖(1 : ℂ) - z‖| := by
      linarith [abs_nonneg (Real.log ‖(1 : ℂ) - z‖)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 k
  calc
    ‖f z‖ =
        (‖f z‖ * ‖(1 : ℂ) - z‖ ^ β) *
          ‖(1 : ℂ) - z‖ ^ (-β) := by
      rw [mul_assoc, hpow_mul, mul_one]
    _ ≤
        (ε * (Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k) *
          ‖(1 : ℂ) - z‖ ^ (-β) :=
      mul_le_mul_of_nonneg_right hstep.le (by positivity)
    _ ≤
        (ε * (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ k) *
          ‖(1 : ℂ) - z‖ ^ (-β) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hmaj hε.le
    _ =
        ε * (‖(1 : ℂ) - z‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ k) := by
      ring

/-- **Log^k-weighted little-o circle transfer.** -/
private lemma transferCircleBoundLogK_isLittleO
    {R φ β : ℝ} {f : ℂ → ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ)) (k : ℕ) (hk : 1 ≤ k)
    (hf_o : Tendsto
      (fun z : ℂ =>
        ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β *
          ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    transferCircleBound f =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ k := by
  obtain ⟨C, hC0, hC⟩ := circleKernelLogK_integral_bound_nat hβ hk
  let A : ℝ := (2 * Real.pi)⁻¹ * 4 * C
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  refine IsLittleO.of_bound ?_
  intro η hη
  let ε : ℝ := η / (2 * (A + 1))
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hhalfpos : 0 < η / 2 := by positivity
  have hdenpos : 0 < 2 * (A + 1) := by positivity
  have hnear_coeff : A * ε ≤ η / 2 := by
    dsimp [ε]
    field_simp [hdenpos.ne']
    nlinarith [hA0, hη]
  obtain ⟨δ, hδpos, hnear⟩ :=
    exists_delta_littleO_kernel_bound_logK
      (R := R) (φ := φ) (β := β) (f := f) k hf_o hεpos
  obtain ⟨M, hM0, hM⟩ :=
    exists_bound_on_closedUnitAway
      (R := R) (φ := φ) (δ := δ) (f := f) hR hφ0 hφ2 hδpos han
  let B : ℝ := (2 * Real.pi)⁻¹ * 4 * (M * (2 * Real.pi))

  have hscale_atTop :
      Tendsto
        (fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ k)
        atTop atTop := by
    have hr : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < β - 1)).comp
        tendsto_natCast_atTop_atTop
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hlogPow_succ :
        ∀ m : ℕ, Tendsto (fun n : ℕ => (Real.log n) ^ (m + 1)) atTop atTop := by
      intro m
      induction m with
      | zero =>
          simpa using hlog
      | succ m ih =>
          have hmul :
              Tendsto
                (fun n : ℕ => (Real.log n) ^ (m + 1) * Real.log n)
                atTop atTop :=
            ih.atTop_mul_atTop₀ hlog
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ] using hmul
    have hl : Tendsto (fun n : ℕ => (Real.log n) ^ k) atTop atTop := by
      obtain ⟨m, hkm⟩ := Nat.exists_eq_add_of_le hk
      subst k
      simpa [Nat.add_comm] using hlogPow_succ m
    exact hr.atTop_mul_atTop₀ hl

  have haway_eventually :
      ∀ᶠ n : ℕ in atTop,
        B ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) := by
    have := hscale_atTop.eventually (eventually_ge_atTop (B / (η / 2)))
    filter_upwards [this] with n hn
    calc
      B = (η / 2) * (B / (η / 2)) := by
        field_simp [hhalfpos.ne']
      _ ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) :=
        mul_le_mul_of_nonneg_left hn hhalfpos.le

  filter_upwards [eventually_atTop.mpr ⟨3, fun n hn => hn⟩, haway_eventually]
    with n hn haway_n
  have hn1 : 1 ≤ n := by omega
  have hnpos_nat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  let r : ℝ := 1 - (1 : ℝ) / n
  have hr0 : 0 ≤ r := by
    have h : (1 : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]
      exact_mod_cast hn1
    dsimp [r]
    linarith
  have hrpos : 0 < r := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have h : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hnpos]
      linarith
    dsimp [r]
    linarith
  have hr1 : r < 1 := by
    have h : 0 < (1 : ℝ) / n := by positivity
    dsimp [r]
    linarith
  have hrR : r < R := lt_trans hr1 hR
  have hscale_nonneg : 0 ≤ (n : ℝ) ^ (β - 1) * (Real.log n) ^ k := by
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    positivity

  have hleft_int := circleFunction_intervalIntegrable (f := f) hr0 hr1 hrR hφ0 hφ2 han
  have hkernel_int :=
    circleKernelLogK_intervalIntegrable (β := β) (r := r) k hr0 hr1
  have hright_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          ε *
            (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
              (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                Complex.exp (θ * Complex.I)‖|) ^ k) + M)
        volume (-Real.pi) Real.pi :=
    (hkernel_int.const_mul ε).add intervalIntegrable_const

  have hInt_le :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        ≤
      ∫ θ in (-Real.pi)..Real.pi,
        ε *
          (‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
            (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
              Complex.exp (θ * Complex.I)‖|) ^ k) + M := by
    refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      hleft_int hright_int ?_
    intro θ _hθ
    set z : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hz
    have hz_delta : z ∈ DeltaDomainArg R φ :=
      circlePoint_mem_delta hr0 hr1 hrR hφ0 hφ2 θ
    have hknn :
        0 ≤ ‖(1 : ℂ) - z‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - z‖|) ^ k := by
      positivity
    by_cases hz_near : ‖(1 : ℂ) - z‖ < δ
    · have hlocal := hnear z hz_delta hz_near
      nlinarith [hlocal, hM0]
    · have hz_away : δ ≤ ‖(1 : ℂ) - z‖ := le_of_not_gt hz_near
      have hz_norm_le : ‖z‖ ≤ 1 := by
        rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hr0]
        exact hr1.le
      have hbound : ‖f z‖ ≤ M := hM z hz_norm_le hz_away
      nlinarith [hbound, mul_nonneg hεpos.le hknn]

  have hr_inv4 : r⁻¹ ^ n ≤ 4 := by
    dsimp [r]
    exact one_sub_inv_pow_nat_le_four (by omega : 2 ≤ n)

  have hkernel_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖|) ^ k)
        ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k := by
    have h := hC n hn
    dsimp [r]
    convert h using 3 <;> norm_num

  have hkernel_nonneg :
      0 ≤ ∫ θ in (-Real.pi)..Real.pi,
        ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
          (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
            Complex.exp (θ * Complex.I)‖|) ^ k :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)

  have hInt_bound :
      (∫ θ in (-Real.pi)..Real.pi,
        ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        ≤ ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) +
            M * (2 * Real.pi) := by
    refine hInt_le.trans ?_
    rw [intervalIntegral.integral_add (hkernel_int.const_mul ε) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    have h1 :
        ε *
          (∫ θ in (-Real.pi)..Real.pi,
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp (θ * Complex.I)‖ ^ (-β) *
              (1 + |Real.log ‖(1 : ℂ) - (r : ℂ) *
                Complex.exp (θ * Complex.I)‖|) ^ k)
          ≤ ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) :=
      mul_le_mul_of_nonneg_left hkernel_bound hεpos.le
    have h2 : (Real.pi - -Real.pi) • M ≤ M * (2 * Real.pi) := by
      rw [smul_eq_mul]
      nlinarith [hM0, Real.pi_pos]
    linarith [h1, h2]

  have htransfer_le :
      transferCircleBound f n
        ≤ A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) + B := by
    have hbracket_nonneg :
        0 ≤ ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) +
          M * (2 * Real.pi) := by
      have : 0 ≤ C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k :=
        le_trans hkernel_nonneg hkernel_bound
      positivity
    have hpi_inv : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    calc
      transferCircleBound f n =
          (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi,
              ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
        simp [transferCircleBound, r]
      _ ≤
          (2 * Real.pi)⁻¹ * r⁻¹ ^ n *
            (ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) +
              M * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hInt_bound
          (mul_nonneg hpi_inv (pow_nonneg (inv_nonneg.mpr hr0) n))
      _ ≤
          (2 * Real.pi)⁻¹ * 4 *
            (ε * (C * (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) +
              M * (2 * Real.pi)) := by
        have hstep := mul_le_mul_of_nonneg_right hr_inv4 hbracket_nonneg
        nlinarith [hstep, hbracket_nonneg, mul_nonneg hpi_inv hbracket_nonneg,
          Real.pi_pos, mul_nonneg (pow_nonneg (inv_nonneg.mpr hr0) n) hbracket_nonneg]
      _ =
          A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) + B := by
        dsimp [A, B]
        ring

  have hnear_n :
      A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k)
        ≤ (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) :=
    mul_le_mul_of_nonneg_right hnear_coeff hscale_nonneg

  have htransfer_nonneg : 0 ≤ transferCircleBound f n := by
    have hI_nonneg :
        0 ≤ ∫ θ in (-Real.pi)..Real.pi,
          ‖f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => by positivity)
    rw [transferCircleBound]
    exact mul_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.mpr hr0) n)) hI_nonneg

  calc
    ‖transferCircleBound f n‖ = transferCircleBound f n :=
      Real.norm_of_nonneg htransfer_nonneg
    _ ≤ A * ε * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) + B :=
      htransfer_le
    _ ≤
        (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) +
          (η / 2) * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) :=
      add_le_add hnear_n haway_n
    _ = η * ((n : ℝ) ^ (β - 1) * (Real.log n) ^ k) := by
      ring
    _ = η * ‖(n : ℝ) ^ (β - 1) * (Real.log n) ^ k‖ := by
      rw [Real.norm_of_nonneg hscale_nonneg]

/-- **Coefficient-level natural-remainder log^k little-o transfer** (`β > 1`, `k ≥ 1`). -/
theorem coeff_norm_isLittleO_atTop_of_delta_littleO_logK_beta_gt_one
    {R φ β : ℝ} {k : ℕ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto
      (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ k)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) (hk : 1 ≤ k) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ k) := by
  have hcircle := transferCircleBoundLogK_isLittleO (R := R) (φ := φ) (β := β) (f := f)
    hR hφ0 hφ2 han k hk hf_o hβ
  have hcoeff := coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
    hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n := (norm_nonneg (p.coeff n)).trans hncoeff
  calc ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1) * (Real.log n) ^ k‖ := hnbound


/-- **Coefficient-level natural-remainder log² little-o transfer** (`β > 1`). -/
theorem coeff_norm_isLittleO_atTop_of_delta_littleO_logSq_beta_gt_one
    {R φ β : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (han : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hf_o : Tendsto
      (fun z : ℂ => ‖f z‖ * ‖(1 : ℂ) - z‖ ^ β * ((Real.log (‖(1 : ℂ) - z‖⁻¹)) ^ 2)⁻¹)
      (𝓝[DeltaDomainArg R φ] (1 : ℂ)) (𝓝 0))
    (hβ : 1 < β) :
    (fun n : ℕ => ‖p.coeff n‖) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (β - 1) * (Real.log n) ^ 2) := by
  have hcircle := transferCircleBoundLogSq_isLittleO (R := R) (φ := φ) (β := β) (f := f)
    hR hφ0 hφ2 han hf_o hβ
  have hcoeff := coeff_norm_le_transferCircleBound (R := R) (φ := φ) (f := f) (p := p)
    hR hφ0 hφ2 hp han
  refine IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hcoeff, hcircle.bound hc] with n hncoeff hnbound
  have hcircle_nonneg : 0 ≤ transferCircleBound f n := (norm_nonneg (p.coeff n)).trans hncoeff
  calc ‖(‖p.coeff n‖ : ℝ)‖ = ‖p.coeff n‖ := norm_norm _
    _ ≤ transferCircleBound f n := hncoeff
    _ = ‖transferCircleBound f n‖ := (Real.norm_of_nonneg hcircle_nonneg).symm
    _ ≤ c * ‖(n : ℝ) ^ (β - 1) * (Real.log n) ^ 2‖ := hnbound
