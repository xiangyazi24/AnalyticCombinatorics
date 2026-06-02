import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The exponential saddle testbed

This file instantiates the saddle assembly machinery for `f z = exp z`.
The hard local-analysis estimates are isolated as explicitly documented
lemmas: the second-order exponential limit, the central domination estimate,
and the tail estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

def expSaddleRadius (n : ℕ) : ℝ := n

def expSaddleB (n : ℕ) : ℝ := n

def expSaddleDelta (n : ℕ) : ℝ := (n : ℝ) ^ (-(2 / 5 : ℝ))

noncomputable abbrev expSeriesC : FormalMultilinearSeries ℂ ℂ ℂ :=
  NormedSpace.expSeries ℂ ℂ

lemma exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp expSeriesC (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt expSeriesC.sum expSeriesC (0 : ℂ) := by
    exact (expSeriesC.hasFPowerSeriesOnBall
      (by
        rw [expSeriesC, NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : expSeriesC.sum = Complex.exp := by
    funext z
    calc
      expSeriesC.sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rwa [hfun] at hsum

lemma expCarrier_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) := by
  simpa [expSeriesC] using
    (show HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) by
      simpa [_root_.expCarrier_toFMLS_eq_expSeries] using exp_hasFPowerSeriesAt_zero)

lemma expSaddleRadius_pos_eventually :
    ∀ᶠ n in atTop, 0 < expSaddleRadius n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [expSaddleRadius] using (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))

lemma expSaddleB_pos_eventually :
    ∀ᶠ n in atTop, 0 < expSaddleB n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [expSaddleB] using (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))

lemma exp_differentiableOn_eventually :
    ∀ᶠ n in atTop,
      DifferentiableOn ℂ Complex.exp (Metric.closedBall 0 (expSaddleRadius n)) :=
  Eventually.of_forall fun _ => Complex.differentiable_exp.differentiableOn

lemma exp_saddle_nonzero_eventually :
    ∀ᶠ n in atTop, Complex.exp (expSaddleRadius n : ℂ) ≠ 0 :=
  Eventually.of_forall fun _ => Complex.exp_ne_zero _

lemma exp_saddleG_continuous (n : ℕ) :
    Continuous fun θ : ℝ => saddleG Complex.exp expSaddleRadius n θ := by
  unfold saddleG saddleGAt expSaddleRadius
  fun_prop

lemma exp_saddleG_intervalIntegrable (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (saddleG Complex.exp expSaddleRadius n) volume a b :=
  (exp_saddleG_continuous n).intervalIntegrable a b

lemma exp_saddleG_norm (n : ℕ) (θ : ℝ) :
    ‖saddleG Complex.exp expSaddleRadius n θ‖ =
      Real.exp ((n : ℝ) * (Real.cos θ - 1)) := by
  simp [saddleG, saddleGAt, expSaddleRadius, Complex.norm_exp, Complex.exp_re]
  rw [← Real.exp_sub]
  congr 1
  ring

lemma exp_saddle_left_integrable_eventually :
    ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG Complex.exp expSaddleRadius n) volume
        (-Real.pi) (-(expSaddleDelta n)) :=
  Eventually.of_forall fun n => exp_saddleG_intervalIntegrable n _ _

lemma exp_saddle_center_integrable_eventually :
    ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG Complex.exp expSaddleRadius n) volume
        (-(expSaddleDelta n)) (expSaddleDelta n) :=
  Eventually.of_forall fun n => exp_saddleG_intervalIntegrable n _ _

lemma exp_saddle_right_integrable_eventually :
    ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG Complex.exp expSaddleRadius n) volume
        (expSaddleDelta n) Real.pi :=
  Eventually.of_forall fun n => exp_saddleG_intervalIntegrable n _ _

lemma exp_delta_mul_sqrt_eq_rpow_eventually :
    (fun n : ℕ => expSaddleDelta n * Real.sqrt (expSaddleB n)) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR_nonneg : 0 ≤ (n : ℝ) := hnR.le
  calc
    expSaddleDelta n * Real.sqrt (expSaddleB n)
        = (n : ℝ) ^ (-(2 / 5 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          simp [expSaddleDelta, expSaddleB, Real.sqrt_eq_rpow]
    _ = (n : ℝ) ^ (-(2 / 5 : ℝ) + (1 / 2 : ℝ)) := by
          rw [Real.rpow_add hnR]
    _ = (n : ℝ) ^ (1 / 10 : ℝ) := by norm_num

lemma exp_delta_mul_sqrt_tendsto_atTop :
    Tendsto (fun n : ℕ => expSaddleDelta n * Real.sqrt (expSaddleB n))
      atTop atTop := by
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact Tendsto.congr' exp_delta_mul_sqrt_eq_rpow_eventually.symm hpow

lemma exp_delta_tendsto_zero :
    Tendsto expSaddleDelta atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

lemma exp_delta_le_pi_eventually :
    ∀ᶠ n in atTop, expSaddleDelta n ≤ Real.pi :=
  exp_delta_tendsto_zero.eventually_le_const Real.pi_pos

/-- The explicit normalized exponent after scaling by `sqrt n`.

This is the genuinely hard local Taylor step: one needs
`exp (i w) - 1 - i w = -w^2/2 + o(w^2)` and then `w = x / sqrt n`.
-/
lemma exp_scaled_phase_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℂ) *
          (Complex.exp (Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)) -
            1 - Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)))
      atTop (𝓝 (-(x ^ 2) / 2 : ℂ)) := by
  by_cases hx : x = 0
  · subst x
    simp
  · let w : ℕ → ℝ := fun n => x / Real.sqrt (n : ℝ)
    have hsplit : ∀ n : ℕ,
        (n : ℂ) *
            (Complex.exp (Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)) -
              1 - Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)) =
          ((n : ℝ) * (Real.cos (w n) - 1) : ℂ) +
            ((n : ℝ) * (Real.sin (w n) - w n) : ℂ) * Complex.I := by
      intro n
      dsimp [w]
      rw [mul_comm Complex.I (x / Real.sqrt (n : ℝ) : ℂ)]
      rw [← Complex.ofReal_div]
      rw [Complex.exp_ofReal_mul_I]
      ring
    have hw0 : Tendsto w atTop (𝓝 (0 : ℝ)) := by
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      convert (hpow.const_mul x) using 1
      · ext n
        simp [w, Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg]
      · simp
    have hw_ne : Tendsto w atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hw0 ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        positivity
      exact div_ne_zero hx hsqrt_ne
    have hnw2 : Tendsto (fun n : ℕ => (n : ℝ) * (w n) ^ 2) atTop (𝓝 (x ^ 2)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      dsimp [w]
      rw [div_pow, Real.sq_sqrt hnR.le]
      field_simp [hnR.ne']
    have hsin_o : (fun t : ℝ => Real.sin t - t) =o[𝓝 (0 : ℝ)] fun t => t ^ 2 := by
      have h := (taylor_isLittleO_univ (f := Real.sin) (x₀ := (0 : ℝ)) (n := 2)
        Real.contDiff_sin)
      have hpoly : taylorWithinEval Real.sin 2 Set.univ (0 : ℝ) = fun t : ℝ => t := by
        funext t
        rw [taylorWithinEval_succ]
        rw [taylorWithinEval_succ]
        simp [iteratedDerivWithin_univ]
      simpa [hpoly] using h
    have hsin_q : Tendsto (fun t : ℝ => (Real.sin t - t) / t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      exact (isLittleO_iff_tendsto (fun t ht => by
        have ht0 : t = 0 := by exact eq_zero_of_pow_eq_zero ht
        simp [ht0])).mp (hsin_o.mono nhdsWithin_le_nhds)
    have hcos_o : (fun t : ℝ => Real.cos t - (1 - t ^ 2 / 2)) =o[𝓝 (0 : ℝ)]
        fun t => t ^ 2 := by
      have h := (taylor_isLittleO_univ (f := Real.cos) (x₀ := (0 : ℝ)) (n := 2)
        Real.contDiff_cos)
      have hpoly :
          taylorWithinEval Real.cos 2 Set.univ (0 : ℝ) = fun t : ℝ => 1 - t ^ 2 / 2 := by
        funext t
        rw [taylorWithinEval_succ]
        rw [taylorWithinEval_succ]
        simp [iteratedDerivWithin_univ]
        ring
      convert h using 1
      · ext t
        rw [hpoly]
      · ext t
        ring
    have hcos_q : Tendsto (fun t : ℝ => (Real.cos t - 1) / t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 / 2 : ℝ))) := by
      have herr : Tendsto (fun t : ℝ => (Real.cos t - (1 - t ^ 2 / 2)) / t ^ 2)
          (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        exact (isLittleO_iff_tendsto (fun t ht => by
          have ht0 : t = 0 := by exact eq_zero_of_pow_eq_zero ht
          simp [ht0])).mp (hcos_o.mono nhdsWithin_le_nhds)
      have hlim : Tendsto
          (fun t : ℝ => (Real.cos t - (1 - t ^ 2 / 2)) / t ^ 2 - (1 / 2 : ℝ))
          (𝓝[≠] (0 : ℝ)) (𝓝 (-(1 / 2 : ℝ))) := by
        simpa using herr.sub tendsto_const_nhds
      refine Tendsto.congr' ?_ hlim
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      field_simp [pow_ne_zero 2 ht0]
      ring
    have hcos_seq : Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (w n) - 1))
        atTop (𝓝 (-(x ^ 2) / 2)) := by
      have hprod := hnw2.mul (hcos_q.comp hw_ne)
      have hprod' : Tendsto
          (fun n : ℕ => ((n : ℝ) * (w n) ^ 2) *
            ((Real.cos (w n) - 1) / (w n) ^ 2))
          atTop (𝓝 (-(x ^ 2) / 2)) := by
        convert hprod using 1
        ring
      refine Tendsto.congr' ?_ hprod'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hwn : w n ≠ 0 := by
        have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
          have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
          positivity
        exact div_ne_zero hx hsqrt_ne
      field_simp [hwn]
    have hsin_seq : Tendsto (fun n : ℕ => (n : ℝ) * (Real.sin (w n) - w n)) atTop
        (𝓝 0) := by
      have hprod := hnw2.mul (hsin_q.comp hw_ne)
      have hprod' : Tendsto
          (fun n : ℕ => ((n : ℝ) * (w n) ^ 2) *
            ((Real.sin (w n) - w n) / (w n) ^ 2))
          atTop (𝓝 0) := by
        simpa [Function.comp_def] using hprod
      refine Tendsto.congr' ?_ hprod'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hwn : w n ≠ 0 := by
        have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
          have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
          positivity
        exact div_ne_zero hx hsqrt_ne
      field_simp [hwn]
    have hcosC : Tendsto (fun n : ℕ => ((n : ℝ) * (Real.cos (w n) - 1) : ℂ))
        atTop (𝓝 ((-(x ^ 2) / 2 : ℝ) : ℂ)) := by
      simpa [Function.comp_def, Complex.ofReal_mul, Complex.ofReal_sub] using
        (Complex.continuous_ofReal.tendsto _).comp hcos_seq
    have hsinC : Tendsto
        (fun n : ℕ => ((n : ℝ) * (Real.sin (w n) - w n) : ℂ) * Complex.I)
        atTop (𝓝 0) := by
      simpa [Function.comp_def, Complex.ofReal_mul, Complex.ofReal_sub] using
        ((Complex.continuous_ofReal.tendsto _).comp hsin_seq).mul_const Complex.I
    have hsum : Tendsto
        (fun n : ℕ => ((n : ℝ) * (Real.cos (w n) - 1) : ℂ) +
          ((n : ℝ) * (Real.sin (w n) - w n) : ℂ) * Complex.I)
        atTop (𝓝 (-(x ^ 2) / 2 : ℂ)) := by
      simpa using hcosC.add hsinC
    refine Tendsto.congr' ?_ hsum
    filter_upwards with n
    exact (hsplit n).symm

lemma exp_scaled_saddleG_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        saddleG Complex.exp expSaddleRadius n
          (x / Real.sqrt (expSaddleB n)))
      atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
  have hphase := exp_scaled_phase_tendsto x
  have hcongr :
      (fun n : ℕ =>
        saddleG Complex.exp expSaddleRadius n
          (x / Real.sqrt (expSaddleB n))) =ᶠ[atTop]
      (fun n : ℕ =>
        Complex.exp
          ((n : ℂ) *
            (Complex.exp (Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)) -
              1 - Complex.I * (x / Real.sqrt (n : ℝ) : ℂ)))) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    simp [saddleG, saddleGAt, expSaddleRadius, expSaddleB]
    rw [← Complex.exp_sub]
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  exact Tendsto.congr' hcongr.symm hphase.cexp

lemma exp_Hfun_pointwise :
    ∀ᵐ x : ℝ,
      Tendsto (fun n : ℕ =>
        Hfun Complex.exp expSaddleRadius expSaddleB expSaddleDelta n x)
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
  refine ae_of_all _ fun x => ?_
  have hinside :
      ∀ᶠ n in atTop, |x| ≤ expSaddleDelta n * Real.sqrt (expSaddleB n) :=
    exp_delta_mul_sqrt_tendsto_atTop.eventually_ge_atTop |x|
  have hH :
      (fun n : ℕ =>
        Hfun Complex.exp expSaddleRadius expSaddleB expSaddleDelta n x) =ᶠ[atTop]
      (fun n : ℕ =>
        saddleG Complex.exp expSaddleRadius n
          (x / Real.sqrt (expSaddleB n))) := by
    filter_upwards [hinside] with n hn
    simp [Hfun, hn]
  exact Tendsto.congr' hH.symm (exp_scaled_saddleG_tendsto x)

lemma exp_Hfun_aestronglyMeasurable_eventually :
    ∀ᶠ n in atTop,
      AEStronglyMeasurable
        (Hfun Complex.exp expSaddleRadius expSaddleB expSaddleDelta n) volume := by
  refine Eventually.of_forall fun n => ?_
  classical
  let L : ℝ := expSaddleDelta n * Real.sqrt (expSaddleB n)
  let g : ℝ → ℂ :=
    fun x => saddleG Complex.exp expSaddleRadius n (x / Real.sqrt (expSaddleB n))
  have hgcont : Continuous g := by
    dsimp [g]
    unfold saddleG saddleGAt expSaddleRadius expSaddleB
    fun_prop
  have hsm : StronglyMeasurable (Set.indicator (Set.Icc (-L) L) g) :=
    hgcont.stronglyMeasurable.indicator measurableSet_Icc
  have heq :
      Hfun Complex.exp expSaddleRadius expSaddleB expSaddleDelta n =
        Set.indicator (Set.Icc (-L) L) g := by
    funext x
    simp [Hfun, Set.indicator, abs_le, L, g]
  rw [heq]
  exact hsm.aestronglyMeasurable

def expCentralDominator (x : ℝ) : ℝ :=
  Real.exp (-(2 / Real.pi ^ 2) * x ^ 2)

lemma expCentralDominator_integrable :
    Integrable expCentralDominator := by
  unfold expCentralDominator
  exact integrable_exp_neg_mul_sq (by positivity : 0 < 2 / Real.pi ^ 2)

/-- Gaussian domination on the scaled central window.

The proof is the cosine estimate
`cos θ ≤ 1 - (2 / π^2) θ^2` for `|θ| ≤ π`, plus the exact norm
of the normalized exponential saddle integrand (`exp_saddleG_norm`).  The
remaining proof is a real-inequality bookkeeping step: from the cutoff
`|x| ≤ δ_n sqrt n` and `δ_n ≤ π`, derive `|x / sqrt n| ≤ π` and then
`n * (x / sqrt n)^2 = x^2`.
-/
lemma exp_Hfun_dominated :
    ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
      ‖Hfun Complex.exp expSaddleRadius expSaddleB expSaddleDelta n x‖ ≤
        expCentralDominator x := by
  filter_upwards [eventually_gt_atTop 0, exp_delta_le_pi_eventually] with n hn hδπ
  refine ae_of_all _ fun x => ?_
  by_cases hx : |x| ≤ expSaddleDelta n * Real.sqrt (expSaddleB n)
  · have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsqrt_pos : 0 < Real.sqrt (expSaddleB n) := by
      simp [expSaddleB, hnRpos]
    have htheta_abs : |x / Real.sqrt (expSaddleB n)| ≤ Real.pi := by
      have hdiv :
          |x / Real.sqrt (expSaddleB n)| =
            |x| / Real.sqrt (expSaddleB n) := by
        rw [abs_div, abs_of_pos hsqrt_pos]
      rw [hdiv]
      have hle_delta : |x| / Real.sqrt (expSaddleB n) ≤ expSaddleDelta n :=
        (div_le_iff₀ hsqrt_pos).mpr hx
      exact hle_delta.trans hδπ
    have hcos := Real.cos_le_one_sub_mul_cos_sq htheta_abs
    have hexp_le :
        (n : ℝ) * (Real.cos (x / Real.sqrt (expSaddleB n)) - 1) ≤
          -(2 / Real.pi ^ 2) * x ^ 2 := by
      have hcos_sub :
          Real.cos (x / Real.sqrt (expSaddleB n)) - 1 ≤
            -(2 / Real.pi ^ 2) * (x / Real.sqrt (expSaddleB n)) ^ 2 := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left hcos_sub hnRpos.le
      calc
        (n : ℝ) * (Real.cos (x / Real.sqrt (expSaddleB n)) - 1)
            ≤ (n : ℝ) *
                (-(2 / Real.pi ^ 2) * (x / Real.sqrt (expSaddleB n)) ^ 2) := hmul
        _ = -(2 / Real.pi ^ 2) * x ^ 2 := by
          simp [expSaddleB, sq, div_eq_mul_inv]
          field_simp [hnRpos.ne']
          rw [Real.sq_sqrt hnRpos.le]
          ring
    simp [Hfun, hx, expCentralDominator, exp_saddleG_norm]
    have hexp_le' :
        (n : ℝ) * (Real.cos (x / Real.sqrt (expSaddleB n)) - 1) ≤
          -(2 / Real.pi ^ 2 * x ^ 2) := by
      nlinarith [hexp_le]
    exact hexp_le'
  · simp [Hfun, hx, expCentralDominator]
    positivity

theorem exp_central_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
          saddleJc Complex.exp expSaddleRadius expSaddleDelta n)
      atTop (𝓝 1) := by
  exact central_tendsto_one_of_dominated_of_aestronglyMeasurable
    Complex.exp expSaddleRadius expSaddleB expSaddleDelta
    expSaddleB_pos_eventually exp_delta_mul_sqrt_tendsto_atTop
    exp_Hfun_aestronglyMeasurable_eventually exp_Hfun_pointwise
    expCentralDominator expCentralDominator_integrable exp_Hfun_dominated

/-- Tail negligibility for the exponential saddle.

This packages the standard bound
`sqrt(2πn) * J_t = O(sqrt n * exp(-c n^(1/5))) = o(1)`.
-/
theorem exp_tail_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
          saddleJt Complex.exp expSaddleRadius expSaddleDelta n)
      atTop (𝓝 0) := by
  let c : ℝ := 2 / Real.pi ^ 2
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hdecay : Tendsto
      (fun n : ℕ => K * Real.sqrt (2 * Real.pi * (n : ℝ)) *
        Real.exp (-c * ((n : ℝ) ^ (1 / 5 : ℝ)))) atTop (𝓝 0) := by
    have hy : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hbase : Tendsto (fun y : ℝ => y ^ (5 / 2 : ℝ) * Real.exp (-c * y)) atTop
        (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) c hc
    have hcomp : Tendsto
        (fun n : ℕ => ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (5 / 2 : ℝ) *
          Real.exp (-c * ((n : ℝ) ^ (1 / 5 : ℝ)))) atTop (𝓝 0) :=
      hbase.comp hy
    have hscaled : Tendsto
        (fun n : ℕ => (K * Real.sqrt (2 * Real.pi)) *
          (((n : ℝ) ^ (1 / 5 : ℝ)) ^ (5 / 2 : ℝ) *
            Real.exp (-c * ((n : ℝ) ^ (1 / 5 : ℝ))))) atTop (𝓝 0) := by
      simpa using hcomp.const_mul (K * Real.sqrt (2 * Real.pi))
    refine Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have h2pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
    rw [Real.sqrt_mul h2pi_nonneg (n : ℝ)]
    rw [Real.sqrt_eq_rpow (2 * Real.pi)]
    rw [Real.sqrt_eq_rpow (n : ℝ)]
    rw [← Real.rpow_mul hnR.le]
    norm_num
    ring
  have hbound : ∀ᶠ n in atTop,
      ‖(Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
          saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖ ≤
        K * Real.sqrt (2 * Real.pi * (n : ℝ)) *
          Real.exp (-c * ((n : ℝ) ^ (1 / 5 : ℝ))) := by
    filter_upwards [eventually_gt_atTop 0, exp_delta_le_pi_eventually] with n hn hδπ
    let E : ℝ := Real.exp (-c * ((n : ℝ) * (expSaddleDelta n) ^ 2))
    have hδ_nonneg : 0 ≤ expSaddleDelta n := by
      unfold expSaddleDelta
      positivity
    have hE_nonneg : 0 ≤ E := by
      dsimp [E]
      positivity
    have hnδ : (n : ℝ) * (expSaddleDelta n) ^ 2 = (n : ℝ) ^ (1 / 5 : ℝ) := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      rw [expSaddleDelta]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hnR]
      norm_num
    have htail (θ : ℝ) (hδθ : expSaddleDelta n ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
        ‖saddleG Complex.exp expSaddleRadius n θ‖ ≤ E := by
      rw [exp_saddleG_norm]
      dsimp [E, c]
      apply Real.exp_le_exp.mpr
      have hnR_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have hcos := Real.cos_le_one_sub_mul_cos_sq hθπ
      have hcos_sub : Real.cos θ - 1 ≤ -(2 / Real.pi ^ 2) * θ ^ 2 := by
        linarith
      have hθsq : (expSaddleDelta n) ^ 2 ≤ θ ^ 2 := by
        calc
          (expSaddleDelta n) ^ 2 ≤ |θ| ^ 2 :=
            pow_le_pow_left₀ hδ_nonneg hδθ 2
          _ = θ ^ 2 := by rw [sq_abs]
      have hcoef_nonpos : -(2 / Real.pi ^ 2) ≤ 0 := by
        have hcpos : 0 < 2 / Real.pi ^ 2 := by positivity
        linarith
      have hsquare_bound :
          -(2 / Real.pi ^ 2) * θ ^ 2 ≤
            -(2 / Real.pi ^ 2) * (expSaddleDelta n) ^ 2 :=
        mul_le_mul_of_nonpos_left hθsq hcoef_nonpos
      calc
        (n : ℝ) * (Real.cos θ - 1)
            ≤ (n : ℝ) * (-(2 / Real.pi ^ 2) * θ ^ 2) :=
              mul_le_mul_of_nonneg_left hcos_sub hnR_nonneg
        _ ≤ (n : ℝ) * (-(2 / Real.pi ^ 2) * (expSaddleDelta n) ^ 2) :=
              mul_le_mul_of_nonneg_left hsquare_bound hnR_nonneg
        _ = -(2 / Real.pi ^ 2) * ((n : ℝ) * (expSaddleDelta n) ^ 2) := by
              ring
    have hleft :
        ‖∫ θ in (-Real.pi)..(-(expSaddleDelta n)), saddleG Complex.exp expSaddleRadius n θ‖ ≤
          E * |(-(expSaddleDelta n)) - (-Real.pi)| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro θ hθ
      have hθI : -Real.pi < θ ∧ θ ≤ -(expSaddleDelta n) := by
        simpa [Set.uIoc_of_le (by linarith : -Real.pi ≤ -(expSaddleDelta n))] using hθ
      have hθ_nonpos : θ ≤ 0 := by linarith
      have hδθ : expSaddleDelta n ≤ |θ| := by
        rw [abs_of_nonpos hθ_nonpos]
        linarith
      have hθπ : |θ| ≤ Real.pi := by
        rw [abs_of_nonpos hθ_nonpos]
        linarith
      exact htail θ hδθ hθπ
    have hright :
        ‖∫ θ in (expSaddleDelta n)..Real.pi, saddleG Complex.exp expSaddleRadius n θ‖ ≤
          E * |Real.pi - expSaddleDelta n| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro θ hθ
      have hθI : expSaddleDelta n < θ ∧ θ ≤ Real.pi := by
        simpa [Set.uIoc_of_le hδπ] using hθ
      have hθ_nonneg : 0 ≤ θ := by linarith
      have hδθ : expSaddleDelta n ≤ |θ| := by
        rw [abs_of_nonneg hθ_nonneg]
        linarith
      have hθπ : |θ| ≤ Real.pi := by
        rw [abs_of_nonneg hθ_nonneg]
        exact hθI.2
      exact htail θ hδθ hθπ
    have hlen_right : |Real.pi - expSaddleDelta n| ≤ Real.pi := by
      rw [abs_of_nonneg (sub_nonneg.mpr hδπ)]
      linarith
    have hlen_left : |(-(expSaddleDelta n)) - (-Real.pi)| ≤ Real.pi := by
      rw [show (-(expSaddleDelta n)) - (-Real.pi) = Real.pi - expSaddleDelta n by ring]
      exact hlen_right
    have hleft_pi :
        ‖∫ θ in (-Real.pi)..(-(expSaddleDelta n)), saddleG Complex.exp expSaddleRadius n θ‖ ≤
          E * Real.pi :=
      hleft.trans (mul_le_mul_of_nonneg_left hlen_left hE_nonneg)
    have hright_pi :
        ‖∫ θ in (expSaddleDelta n)..Real.pi, saddleG Complex.exp expSaddleRadius n θ‖ ≤
          E * Real.pi :=
      hright.trans (mul_le_mul_of_nonneg_left hlen_right hE_nonneg)
    have hJ : ‖saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖ ≤ K * E := by
      unfold saddleJt saddleJtAt
      dsimp [K]
      calc
        ‖(2 * Real.pi : ℂ)⁻¹ *
            ((∫ θ in (-Real.pi)..(-(expSaddleDelta n)),
                saddleGAt Complex.exp (expSaddleRadius n) n θ) +
              ∫ θ in (expSaddleDelta n)..Real.pi,
                saddleGAt Complex.exp (expSaddleRadius n) n θ)‖
            ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ *
              (‖∫ θ in (-Real.pi)..(-(expSaddleDelta n)),
                  saddleG Complex.exp expSaddleRadius n θ‖ +
                ‖∫ θ in (expSaddleDelta n)..Real.pi,
                  saddleG Complex.exp expSaddleRadius n θ‖) := by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ * (E * Real.pi + E * Real.pi) := by
              exact mul_le_mul_of_nonneg_left (add_le_add hleft_pi hright_pi) (norm_nonneg _)
        _ = ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi) * E := by
              ring
    have hscaled_norm :
        ‖(Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
            saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖ ≤
          K * Real.sqrt (2 * Real.pi * (n : ℝ)) * E := by
      calc
        ‖(Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
            saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖
            = Real.sqrt (2 * Real.pi * (n : ℝ)) *
                ‖saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
              · simp [expSaddleB]
              · positivity
        _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) * (K * E) := by
              exact mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = K * Real.sqrt (2 * Real.pi * (n : ℝ)) * E := by
              ring
    dsimp [E] at hscaled_norm
    rw [hnδ] at hscaled_norm
    simpa [c, mul_assoc] using hscaled_norm
  have hnorm : Tendsto
      (fun n : ℕ => ‖(Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) *
        saddleJt Complex.exp expSaddleRadius expSaddleDelta n‖) atTop (𝓝 0) := by
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hdecay
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

lemma exp_saddleScale_nonzero_eventually :
    ∀ᶠ n in atTop,
      saddleScale Complex.exp expSaddleRadius expSaddleB n ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsqrt : (Real.sqrt (2 * Real.pi * expSaddleB n) : ℂ) ≠ 0 := by
    have hpos : 0 < Real.sqrt (2 * Real.pi * expSaddleB n) := by
      rw [expSaddleB]
      positivity
    exact_mod_cast hpos.ne'
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  simp [saddleScale, saddlePref, saddlePrefAt, expSaddleRadius, expSaddleB,
    Complex.exp_ne_zero, hnR, hsqrtpi]

theorem exp_coeff_isEquivalent_saddle :
    (fun n : ℕ => (PowerSeries.toFMLS expCarrier).coeff n) ~[atTop]
      (fun n : ℕ => saddleScale Complex.exp expSaddleRadius expSaddleB n) := by
  exact coeff_isEquivalent_saddle_assembly_of_cauchy
    expSaddleRadius expSaddleB expSaddleDelta
    expCarrier_hasFPowerSeriesAt_zero
    expSaddleRadius_pos_eventually exp_differentiableOn_eventually
    exp_saddle_nonzero_eventually
    exp_saddle_left_integrable_eventually
    exp_saddle_center_integrable_eventually
    exp_saddle_right_integrable_eventually
    exp_central_tendsto_one exp_tail_tendsto_zero
    exp_saddleScale_nonzero_eventually

lemma exp_saddleScale_eq_stirling_scale_eventually :
    (fun n : ℕ => saddleScale Complex.exp expSaddleRadius expSaddleB n) =ᶠ[atTop]
      fun n : ℕ =>
        ((Real.exp n / ((n : ℝ) ^ n * Real.sqrt (2 * Real.pi * n))) : ℂ) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [saddleScale, saddlePref, saddlePrefAt, expSaddleRadius, expSaddleB,
    Complex.ofReal_exp, div_eq_mul_inv]
  ring

theorem exp_coeff_isEquivalent_stirling_scale_complex :
    (fun n : ℕ => (PowerSeries.toFMLS expCarrier).coeff n) ~[atTop]
      (fun n : ℕ =>
        ((Real.exp n / ((n : ℝ) ^ n * Real.sqrt (2 * Real.pi * n))) : ℂ)) :=
  exp_coeff_isEquivalent_saddle.congr_right exp_saddleScale_eq_stirling_scale_eventually

lemma expCarrier_toFMLS_coeff_eq_inv_factorial (n : ℕ) :
    (PowerSeries.toFMLS expCarrier).coeff n = ((1 : ℝ) / n.factorial : ℂ) := by
  rw [PowerSeries.coeff_toFMLS]
  exact expCarrier_coeff n

theorem inv_factorial_isEquivalent_stirling_complex :
    (fun n : ℕ => ((1 : ℝ) / n.factorial : ℂ)) ~[atTop]
      (fun n : ℕ =>
        ((Real.exp n / ((n : ℝ) ^ n * Real.sqrt (2 * Real.pi * n))) : ℂ)) :=
  exp_coeff_isEquivalent_stirling_scale_complex.congr_left
    (Eventually.of_forall expCarrier_toFMLS_coeff_eq_inv_factorial)

lemma ofReal_isEquivalent_iff_expStirling {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn

theorem inv_factorial_isEquivalent_stirling :
    (fun n : ℕ => (1 : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp n / ((n : ℝ) ^ n * Real.sqrt (2 * Real.pi * n))) := by
  rw [← ofReal_isEquivalent_iff_expStirling]
  simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast] using inv_factorial_isEquivalent_stirling_complex

theorem inv_factorial_isEquivalent_stirling_crosscheck :
    (fun n : ℕ => (1 : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp n / ((n : ℝ) ^ n * Real.sqrt (2 * Real.pi * n))) := by
  have h := Stirling.factorial_isEquivalent_stirling.inv
  refine (h.congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun n => by
      simp [Pi.inv_apply, div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hsqrt_ne' : Real.sqrt (2 * Real.pi * (n : ℝ)) ≠ 0 := by positivity
    have hexp_ne : Real.exp (1 : ℝ) ≠ 0 := Real.exp_ne_zero _
    have hsqrt_eq :
        Real.sqrt (2 * (n : ℝ) * Real.pi) =
          Real.sqrt (2 * Real.pi * (n : ℝ)) := by
      congr 1
      ring
    simp only [Pi.inv_apply]
    rw [hsqrt_eq]
    rw [div_pow]
    rw [Real.exp_one_pow]
    field_simp [hnR, hsqrt_ne', hexp_ne]

end ExpStirling
