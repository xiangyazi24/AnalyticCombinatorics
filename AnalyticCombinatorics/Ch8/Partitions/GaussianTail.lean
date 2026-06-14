import AnalyticCombinatorics.Ch8.Partitions.ModelSaddleIntegral

/-!
# Moving-limit Gaussian DCT core (HR brick 4)

The transformed Gaussian kernel `e^{-u²}/(1+βu)` (with `β = 2√s/C → 0`), restricted to
the moving domain `u > α(s) = -C/(4√s) → -∞`, converges in `L¹`-dominated fashion to
`e^{-u²}`, hence its integral → `√π` (`integral_gaussian`). This is the analytic heart
of `∫_{Ioi 1} e^{-s(v-v₀)²}/v ~ (2√π/C)√s`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos
open scoped Topology Interval

noncomputable section

/-- `∫_ℝ e^{-u²} = √π` (real wrapper around `integral_gaussian`). -/
lemma integral_exp_neg_sq : (∫ u : ℝ, Real.exp (-(u ^ 2))) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simp only [neg_one_mul, div_one] at h
  simpa using h

/-- Moving lower limit `α(s) = -C/(4√s) → -∞` as `s → 0⁺`. -/
def gaussianTailAlpha (s : ℝ) : ℝ := -C / (4 * Real.sqrt s)

/-- Shrinking distortion `β(s) = 2√s/C → 0`. -/
def gaussianTailBeta (s : ℝ) : ℝ := 2 * Real.sqrt s / C

/-- The transformed kernel `e^{-u²}/(1+βu)` cut off below `α(s)`. -/
noncomputable def gaussianTailKernel (s u : ℝ) : ℝ :=
  Set.indicator (Set.Ioi (gaussianTailAlpha s))
    (fun u : ℝ => Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u)) u

/-- `√s → 0⁺` within `𝓝[>] 0`. -/
lemma sqrt_tendsto_nhdsGT_zero :
    Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have h0 : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [Real.sqrt_zero] at this
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h0, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact Real.sqrt_pos.mpr hs

lemma gaussianTailAlpha_tendsto_atBot :
    Tendsto gaussianTailAlpha (𝓝[>] (0 : ℝ)) atBot := by
  have hCpos : 0 < C := C_pos
  unfold gaussianTailAlpha
  have hinv : Tendsto (fun s : ℝ => 1 / Real.sqrt s) (𝓝[>] (0 : ℝ)) atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp sqrt_tendsto_nhdsGT_zero
  have hmul : Tendsto (fun s : ℝ => -(C / 4) * (1 / Real.sqrt s)) (𝓝[>] (0 : ℝ)) atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -(C / 4) < 0)).mpr hinv
  refine hmul.congr (fun s => ?_)
  rw [div_eq_mul_inv]; ring

lemma gaussianTailBeta_tendsto_zero :
    Tendsto gaussianTailBeta (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsqrt0 : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    sqrt_tendsto_nhdsGT_zero.mono_right nhdsWithin_le_nhds
  have h := hsqrt0.const_mul (2 / C)
  rw [mul_zero] at h
  exact h.congr (fun s => by unfold gaussianTailBeta; ring)

/-- Pointwise: for fixed `u`, the kernel → `e^{-u²}` (`α(s) < u` eventually, denominator → 1). -/
lemma gaussianTailKernel_pointwise :
    ∀ᵐ u : ℝ, Tendsto (fun s : ℝ => gaussianTailKernel s u)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(u ^ 2)))) := by
  refine ae_of_all _ (fun u => ?_)
  have hα_event : ∀ᶠ s in 𝓝[>] (0 : ℝ), gaussianTailAlpha s < u := by
    filter_upwards [tendsto_atBot.mp gaussianTailAlpha_tendsto_atBot (u - 1)] with s hs
    linarith
  have hden : Tendsto (fun s : ℝ => 1 + gaussianTailBeta s * u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (gaussianTailBeta_tendsto_zero.mul_const u)
  have hquot : Tendsto (fun s : ℝ => Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp (-(u ^ 2)) / 1)) :=
    tendsto_const_nhds.div hden (by norm_num)
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [hα_event] with s hs
  simp [gaussianTailKernel, hs]

/-- Dominating function `2e^{-u²}` (denominator `≥ 1/2` on the cut domain). -/
lemma gaussianTailKernel_dom :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᵐ u : ℝ,
      ‖gaussianTailKernel s u‖ ≤ 2 * Real.exp (-(u ^ 2)) := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hCpos : 0 < C := C_pos
  refine ae_of_all _ (fun u => ?_)
  by_cases hu : gaussianTailAlpha s < u
  · have hden_lb : (1 : ℝ) / 2 ≤ 1 + gaussianTailBeta s * u := by
      have hmul := mul_lt_mul_of_pos_left hu (show (0 : ℝ) < 2 * Real.sqrt s / C by positivity)
      have hleft : (2 * Real.sqrt s / C) * gaussianTailAlpha s = -(1 / 2 : ℝ) := by
        unfold gaussianTailAlpha
        field_simp
        ring
      rw [hleft] at hmul
      unfold gaussianTailBeta
      nlinarith [hmul]
    have hden_pos : 0 < 1 + gaussianTailBeta s * u := by linarith
    simp only [gaussianTailKernel, Set.indicator_of_mem (Set.mem_Ioi.mpr hu), Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hden_pos, abs_of_pos (Real.exp_pos _)]
    rw [div_le_iff₀ hden_pos]
    nlinarith [Real.exp_pos (-(u ^ 2)), hden_lb]
  · have hzero : gaussianTailKernel s u = 0 := by
      simp only [gaussianTailKernel]
      exact Set.indicator_of_notMem (by rw [Set.mem_Ioi]; exact hu) _
    rw [hzero, norm_zero]
    positivity

lemma integrable_gaussian_dom : Integrable (fun u : ℝ => 2 * Real.exp (-(u ^ 2))) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  exact (hbase.const_mul 2).congr (by filter_upwards with u; simp [neg_one_mul])

/-- The cut Gaussian kernel integral → `√π` (DCT, moving lower limit). -/
lemma gaussianTailKernel_integral_tendsto :
    Tendsto (fun s : ℝ => ∫ u : ℝ, gaussianTailKernel s u)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
  have Hmeas : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (gaussianTailKernel s) volume := by
    refine Eventually.of_forall (fun s => ?_)
    unfold gaussianTailKernel
    refine (AEStronglyMeasurable.indicator ?_ measurableSet_Ioi)
    exact Measurable.aestronglyMeasurable (by measurability)
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun u : ℝ => 2 * Real.exp (-(u ^ 2)))
    Hmeas gaussianTailKernel_dom integrable_gaussian_dom gaussianTailKernel_pointwise
  rwa [integral_exp_neg_sq] at hlim

/-- Saddle cutoff `q(s) = C/(4s) = v₀/2`. -/
def gaussianTailCut (s : ℝ) : ℝ := C / (4 * s)

/-- `√s·(c/(k·s)) = c/(k·√s)` (one `√s` cancels). -/
lemma sqrt_mul_div_self {s k : ℝ} (hs : 0 < s) (hk : 0 < k) (c : ℝ) :
    Real.sqrt s * (c / (k * s)) = c / (k * Real.sqrt s) := by
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hkne : k ≠ 0 := ne_of_gt hk
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsqne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  field_simp
  linear_combination c * hss

/-- Key denominator identity: `C/(2√s) + √s·(v − C/(2s)) = √s·v`. -/
lemma gaussianTail_denom_id {s : ℝ} (hs : 0 < s) (v : ℝ) :
    C / (2 * Real.sqrt s) + Real.sqrt s * (v - C / (2 * s)) = Real.sqrt s * v := by
  rw [mul_sub, sqrt_mul_div_self (k := 2) hs (by norm_num) C]; ring

/-- Finite-interval affine substitution `u = √s(v − v₀)` for the cut Gaussian:
`∫_{cut}^B e^{−s(v−v₀)²}/v = ∫_{α}^{√s(B−v₀)} e^{−u²}/(C/(2√s)+u)`. -/
lemma gaussianTail_affine_interval {s B : ℝ} (hs : 0 < s)
    (hcutB : gaussianTailCut s ≤ B) :
    (∫ v in gaussianTailCut s..B, Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = ∫ u in gaussianTailAlpha s..(Real.sqrt s * (B - C / (2 * s))),
          Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) := by
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hCpos : 0 < C := C_pos
  have hcutpos : 0 < gaussianTailCut s := by
    rw [gaussianTailCut]; exact div_pos hCpos (by positivity)
  set f : ℝ → ℝ := fun v => Real.sqrt s * (v - C / (2 * s)) with hf
  set g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) with hg
  have hderiv : ∀ v ∈ Set.uIcc (gaussianTailCut s) B, HasDerivAt f (Real.sqrt s) v := by
    intro v _
    simpa using ((hasDerivAt_id v).sub_const (C / (2 * s))).const_mul (Real.sqrt s)
  have hcont' : ContinuousOn (fun _ : ℝ => Real.sqrt s) (Set.uIcc (gaussianTailCut s) B) :=
    continuousOn_const
  have hcontg : ContinuousOn g (f '' Set.uIcc (gaussianTailCut s) B) := by
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) ?_
    rintro u ⟨v, hv, rfl⟩
    rw [Set.uIcc_of_le hcutB] at hv
    have hvpos : 0 < v := lt_of_lt_of_le hcutpos hv.1
    rw [hf, gaussianTail_denom_id hs v]
    exact ne_of_gt (mul_pos hsqrtpos hvpos)
  have hsqrtne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  have hfcut : f (gaussianTailCut s) = gaussianTailAlpha s := by
    simp only [hf, gaussianTailCut, gaussianTailAlpha]
    rw [mul_sub, sqrt_mul_div_self (k := 4) hs (by norm_num) C,
      sqrt_mul_div_self (k := 2) hs (by norm_num) C]
    field_simp
    ring
  have hsub := intervalIntegral.integral_comp_mul_deriv' hderiv hcont' hcontg
  rw [hfcut] at hsub
  rw [← hsub]
  refine (intervalIntegral.integral_congr ?_)
  intro v hv
  rw [Set.uIcc_of_le hcutB] at hv
  have hvpos : 0 < v := lt_of_lt_of_le hcutpos hv.1
  have hvne : v ≠ 0 := ne_of_gt hvpos
  have hsne : Real.sqrt s ≠ 0 := ne_of_gt hsqrtpos
  simp only [Function.comp, hf, hg]
  rw [show -(Real.sqrt s * (v - C / (2 * s))) ^ 2 = -s * (v - C / (2 * s)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hs.le]; ring, gaussianTail_denom_id hs v]
  field_simp

lemma gaussianTailCut_pos {s : ℝ} (hs : 0 < s) : 0 < gaussianTailCut s := by
  rw [gaussianTailCut]; exact div_pos C_pos (by positivity)

/-- Shifted Gaussian over `v` is integrable on all of `ℝ`. -/
lemma integrable_gaussShift {s : ℝ} (hs : 0 < s) :
    Integrable (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq hs).comp_sub_right (C / (2 * s))
  simpa using h

/-- `e^{-s(v-v₀)²}/v` integrable on `(cut,∞)` (dominated by `(1/cut)·gauss`). -/
lemma integrableOn_gaussShift_div {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (Set.Ioi (gaussianTailCut s)) := by
  have hcutpos : 0 < gaussianTailCut s := gaussianTailCut_pos hs
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      (volume.restrict (Set.Ioi (gaussianTailCut s))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine Integrable.mono'
    ((integrable_gaussShift hs).integrableOn.const_mul (1 / gaussianTailCut s)) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with v hv
  have hvcut : gaussianTailCut s < v := hv
  have hvpos : 0 < v := lt_trans hcutpos hvcut
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.exp (-s * (v - C / (2 * s)) ^ 2) / v
      ≤ Real.exp (-s * (v - C / (2 * s)) ^ 2) / gaussianTailCut s := by
        gcongr
    _ = 1 / gaussianTailCut s * Real.exp (-s * (v - C / (2 * s)) ^ 2) := by
        rw [div_eq_inv_mul, one_div]

/-- `e^{-u²}/(C/(2√s)+u)` integrable on `(α,∞)` (denominator `≥ C/(4√s)`). -/
lemma integrableOn_uKernel {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u))
      (Set.Ioi (gaussianTailAlpha s)) := by
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hgauss : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    simpa [neg_one_mul] using this
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u))
      (volume.restrict (Set.Ioi (gaussianTailAlpha s))) := by
    apply Measurable.aestronglyMeasurable; fun_prop
  refine Integrable.mono'
    (hgauss.integrableOn.const_mul (4 * Real.sqrt s / C)) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu_lb : gaussianTailAlpha s < u := hu
  have hkey : C / (2 * Real.sqrt s) - C / (4 * Real.sqrt s) = C / (4 * Real.sqrt s) := by
    field_simp; ring
  have hden_lb : C / (4 * Real.sqrt s) ≤ C / (2 * Real.sqrt s) + u := by
    unfold gaussianTailAlpha at hu_lb
    have h2 : -C / (4 * Real.sqrt s) = -(C / (4 * Real.sqrt s)) := by ring
    rw [h2] at hu_lb
    linarith [hu_lb, hkey]
  have hden_pos : 0 < C / (2 * Real.sqrt s) + u :=
    lt_of_lt_of_le (by positivity) hden_lb
  have hge : (1 : ℝ) ≤ (4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u) := by
    have hone : (4 * Real.sqrt s / C) * (C / (4 * Real.sqrt s)) = 1 := by field_simp
    calc (1 : ℝ) = (4 * Real.sqrt s / C) * (C / (4 * Real.sqrt s)) := hone.symm
      _ ≤ (4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u) :=
        mul_le_mul_of_nonneg_left hden_lb (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hden_pos]
  calc Real.exp (-(u ^ 2)) = Real.exp (-(u ^ 2)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(u ^ 2)) * ((4 * Real.sqrt s / C) * (C / (2 * Real.sqrt s) + u)) :=
        mul_le_mul_of_nonneg_left hge (Real.exp_pos _).le
    _ = 4 * Real.sqrt s / C * Real.exp (-(u ^ 2)) * (C / (2 * Real.sqrt s) + u) := by ring

/-- `∫_{Ioi cut} e^{-s(v-v₀)²}/v = (2√s/C)·∫_ℝ gaussianTailKernel s` (affine subst + B→∞). -/
lemma modelGaussCut_eq {s : ℝ} (hs : 0 < s) :
    (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
      = (2 * Real.sqrt s / C) * ∫ u : ℝ, gaussianTailKernel s u := by
  have hCpos : 0 < C := C_pos
  have hsqrtpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  -- step 1: ∫_{Ioi cut} = ∫_{Ioi α} e^{-u²}/(C/2√s+u)
  have hb : Tendsto (fun B : ℝ => Real.sqrt s * (B - C / (2 * s))) atTop atTop := by
    have h1 : Tendsto (fun B : ℝ => B - C / (2 * s)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_id
    exact Tendsto.const_mul_atTop hsqrtpos h1
  have hlimL := intervalIntegral_tendsto_integral_Ioi (gaussianTailCut s)
    (integrableOn_gaussShift_div hs) (tendsto_id (α := ℝ))
  have hlimR := intervalIntegral_tendsto_integral_Ioi (gaussianTailAlpha s)
    (integrableOn_uKernel hs) hb
  have heq : ∀ᶠ B : ℝ in atTop,
      (∫ v in gaussianTailCut s..B, Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
        = ∫ u in gaussianTailAlpha s..(Real.sqrt s * (B - C / (2 * s))),
            Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) := by
    filter_upwards [eventually_ge_atTop (gaussianTailCut s)] with B hB
    exact gaussianTail_affine_interval hs hB
  have step1 :
      (∫ v in Set.Ioi (gaussianTailCut s), Real.exp (-s * (v - C / (2 * s)) ^ 2) / v)
        = ∫ u in Set.Ioi (gaussianTailAlpha s),
            Real.exp (-(u ^ 2)) / (C / (2 * Real.sqrt s) + u) :=
    tendsto_nhds_unique (hlimL.congr' heq) hlimR
  rw [step1]
  -- step 2: kernel integral = ∫_{Ioi α} e^{-u²}/(1+βu); pull (2√s/C)
  have hkernel_int : (∫ u, gaussianTailKernel s u)
      = ∫ u in Set.Ioi (gaussianTailAlpha s),
          Real.exp (-(u ^ 2)) / (1 + gaussianTailBeta s * u) := by
    simp only [gaussianTailKernel]
    exact integral_indicator measurableSet_Ioi
  rw [hkernel_int, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu_lb : gaussianTailAlpha s < u := hu
  have hbpos : 0 < 1 + gaussianTailBeta s * u := by
    have hmono : gaussianTailBeta s * gaussianTailAlpha s < gaussianTailBeta s * u :=
      mul_lt_mul_of_pos_left hu_lb (by unfold gaussianTailBeta; positivity)
    have hval : gaussianTailBeta s * gaussianTailAlpha s = -(1 / 2 : ℝ) := by
      unfold gaussianTailBeta gaussianTailAlpha; rw [neg_div, mul_neg]; field_simp; ring
    rw [hval] at hmono; linarith
  have hdenpos : 0 < C / (2 * Real.sqrt s) + u := by
    have h2 : gaussianTailAlpha s = -(C / (4 * Real.sqrt s)) := by
      unfold gaussianTailAlpha; ring
    have hval2 : C / (2 * Real.sqrt s) + gaussianTailAlpha s = C / (4 * Real.sqrt s) := by
      rw [h2, ← sub_eq_add_neg]; field_simp; ring
    have hlt : C / (2 * Real.sqrt s) + gaussianTailAlpha s < C / (2 * Real.sqrt s) + u := by
      linarith
    rw [hval2] at hlt
    exact lt_trans (by positivity) hlt
  have hbne : (1 + gaussianTailBeta s * u) ≠ 0 := ne_of_gt hbpos
  have hdne : (C / (2 * Real.sqrt s) + u) ≠ 0 := ne_of_gt hdenpos
  unfold gaussianTailBeta
  field_simp

end

end AnalyticCombinatorics.Ch8.Partitions
