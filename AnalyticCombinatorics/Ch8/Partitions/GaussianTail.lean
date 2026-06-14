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

end

end AnalyticCombinatorics.Ch8.Partitions
