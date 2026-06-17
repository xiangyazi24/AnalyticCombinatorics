import Mathlib
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch8.SaddlePoint.InvolutionHAdmissible
import AnalyticCombinatorics.Ch4.Analytic.Poles

/-!
# Fragmented permutations: finite-radius H-admissible saddle data

Fragmented permutations are the labelled class `SET(SEQ_{\ge 1}(Z))`, with EGF
`exp (z / (1 - z))`.  This file packages the finite-radius Hayman data for the
committed `HAdmissible` bridge.  The saddle regime is `r -> 1-`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace FragmentedPermHAdmissible

/-- The fragmented-permutation EGF, `exp (z/(1-z))`. -/
abbrev fragPermFun (z : ℂ) : ℂ :=
  Complex.exp (z / (1 - z))

/-- The rational exponent `h(z)=z/(1-z)`. -/
abbrev fragPermH (z : ℂ) : ℂ :=
  z / (1 - z)

/-- Denominator `|1-r exp(iθ)|^2`, in a form convenient for tail estimates. -/
def fragPermDenom (r θ : ℝ) : ℝ :=
  (1 - r) ^ 2 + 2 * r * (1 - Real.cos θ)

/-- The inner series `z + z^2 + ...`, represented as `X/(1-X)`. -/
def fragPermInnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) * PowerSeries.pole1

lemma fragPermInnerPS_constantCoeff :
    PowerSeries.constantCoeff fragPermInnerPS = 0 := by
  simp [fragPermInnerPS]

/-- The formal EGF carrier `exp (X/(1-X))`. -/
def fragPermCarrier : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst fragPermInnerPS

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev fragPermSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS fragPermCarrier

lemma pole1_toFMLS_eq_geometric :
    PowerSeries.toFMLS PowerSeries.pole1 = formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, PowerSeries.coeff_pole1, formalMultilinearSeries_geometric]

lemma fragPermInner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z / (1 - z))
      (PowerSeries.toFMLS fragPermInnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    InvolutionHAdmissible.hasFPowerSeriesAt_id_toFMLS_X
  have hpole : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (PowerSeries.toFMLS PowerSeries.pole1) (0 : ℂ) := by
    simpa [pole1_toFMLS_eq_geometric] using
      (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have hmul := InvolutionHAdmissible.hasFPowerSeriesAt_mul_toFMLS hX hpole
  simpa [fragPermInnerPS, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma fragPermFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt fragPermFun fragPermSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp
      (PowerSeries.toFMLS (PowerSeries.exp ℂ)) ((fun z : ℂ => z / (1 - z)) 0) := by
    simpa [expCarrier] using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z / (1 - z)) houter fragPermInner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt fragPermFun (PowerSeries.toFMLS fragPermCarrier) (0 : ℂ)
  rw [fragPermCarrier]
  rw [PowerSeries.toFMLS_subst_eq_comp fragPermInnerPS_constantCoeff]
  simpa [Function.comp_def, fragPermFun, fragPermSeries] using hcomp

/-- The radius filter `r -> 1-`. -/
def fragPermRadFilter : Filter ℝ :=
  𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)

/-- Continuous saddle mean, `a(r)=r/(1-r)^2`. -/
def fragPermSaddleAReal (r : ℝ) : ℝ :=
  r / (1 - r) ^ 2

/-- Continuous saddle variance scale, `b(r)=r(1+r)/(1-r)^3`. -/
def fragPermSaddleBReal (r : ℝ) : ℝ :=
  r * (1 + r) / (1 - r) ^ 3

/-- Hayman window.  The exponent lies in `(4/3, 3/2)`. -/
def fragPermSaddleDeltaReal (r : ℝ) : ℝ :=
  (1 - r) ^ (7 / 5 : ℝ)

/-- Tail ratio constant from the flat-envelope real-part estimate. -/
def fragPermTailRatioC : ℝ :=
  1 / (3 * Real.pi ^ 2)

/-- Exponential tail decay constant after substituting `b(r) δ(r)^2`. -/
def fragPermTailC : ℝ :=
  1 / (4 * Real.pi ^ 2)

/-- Flat-envelope tail bound. -/
def fragPermTailE (r : ℝ) : ℝ :=
  Real.exp (-fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)))

@[simp] lemma fragPermSaddleAReal_apply (r : ℝ) :
    fragPermSaddleAReal r = r / (1 - r) ^ 2 := rfl

@[simp] lemma fragPermSaddleBReal_apply (r : ℝ) :
    fragPermSaddleBReal r = r * (1 + r) / (1 - r) ^ 3 := rfl

@[simp] lemma fragPermSaddleDeltaReal_apply (r : ℝ) :
    fragPermSaddleDeltaReal r = (1 - r) ^ (7 / 5 : ℝ) := rfl

@[simp] lemma fragPermTailRatioC_apply :
    fragPermTailRatioC = 1 / (3 * Real.pi ^ 2) := rfl

@[simp] lemma fragPermTailC_apply :
    fragPermTailC = 1 / (4 * Real.pi ^ 2) := rfl

lemma fragPermRadFilter_neBot : fragPermRadFilter.NeBot := by
  unfold fragPermRadFilter
  infer_instance

lemma fragPerm_eventually_Ioo_zero_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_eventually_Ioo_half_one :
    ∀ᶠ r : ℝ in fragPermRadFilter, r ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by
  rw [fragPermRadFilter, eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (by norm_num : ((1 : ℝ) / 2) < 1)
      (by norm_num : (1 : ℝ) < 2)] with r hr hleft
  exact ⟨hr.1, hleft⟩

lemma fragPerm_r_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  exact hr.1

lemma fragPerm_differentiableOn_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      DifferentiableOn ℂ fragPermFun (Metric.closedBall (0 : ℂ) r) := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr z hz
  have hnorm_le : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzne : (1 : ℂ) - z ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have hnorm_one : ‖z‖ = 1 := by simp [hz_eq]
    have : (1 : ℝ) ≤ r := by simpa [hnorm_one] using hnorm_le
    linarith [hr.2]
  unfold fragPermFun
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z) z := differentiableAt_id
  have hden : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hquot : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) z :=
    hnum.div hden hzne
  exact (Complex.differentiable_exp.differentiableAt.comp z hquot).differentiableWithinAt

lemma fragPerm_f_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < (fragPermFun (r : ℂ)).re := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermFun
  have harg : (r : ℂ) / (1 - (r : ℂ)) = ((r / (1 - r) : ℝ) : ℂ) := by
    norm_num
  rw [harg]
  rw [← Complex.ofReal_exp]
  exact Real.exp_pos _

lemma fragPerm_b_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermSaddleBReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermSaddleBReal
  have hrpos : 0 < r := hr.1
  have hden : 0 < (1 - r) ^ 3 := by
    have hbase : 0 < 1 - r := by linarith [hr.2]
    positivity
  have hnum : 0 < r * (1 + r) := by positivity
  exact div_pos hnum hden

lemma fragPerm_delta_pos_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 < fragPermSaddleDeltaReal r := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermSaddleDeltaReal
  exact Real.rpow_pos_of_pos (by linarith [hr.2] : 0 < 1 - r) _

lemma fragPerm_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermSaddleDeltaReal r ≤ Real.pi := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  have hδ_le_one : fragPermSaddleDeltaReal r ≤ 1 := by
    unfold fragPermSaddleDeltaReal
    exact Real.rpow_le_one hbase_nonneg hbase_le_one (by norm_num : (0 : ℝ) ≤ 7 / 5)
  have hpi : (1 : ℝ) ≤ Real.pi := by
    nlinarith [Real.one_le_pi_div_two]
  exact hδ_le_one.trans hpi

lemma fragPerm_delta_le_one_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, fragPermSaddleDeltaReal r ≤ 1 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hbase_nonneg : 0 ≤ 1 - r := by linarith [hr.2]
  have hbase_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  unfold fragPermSaddleDeltaReal
  exact Real.rpow_le_one hbase_nonneg hbase_le_one
    (by norm_num : (0 : ℝ) ≤ 7 / 5)

lemma fragPerm_one_sub_tendsto_nhdsGT_zero :
    Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) := by
  unfold fragPermRadFilter
  have hr : Tendsto (fun r : ℝ => r) (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [id] using
      (tendsto_id.mono_right
        (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ))))
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hnhds : Tendsto (fun r : ℝ => 1 - r)
      (𝓝[Set.Iio (1 : ℝ)] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (hc.sub hr)
  have hpos : ∀ᶠ r : ℝ in 𝓝[Set.Iio (1 : ℝ)] (1 : ℝ),
      1 - r ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hrlt
    exact sub_pos.mpr (by simpa using hrlt)
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun r : ℝ => 1 - r) hnhds hpos

lemma fragPerm_one_sub_rpow_neg_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 10 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 10 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPerm_sqrt_b_lower_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ)) ≤
      Real.sqrt (fragPermSaddleBReal r) := by
  let u : ℝ := 1 - r
  have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
  have hu_nonneg : 0 ≤ u := hu_pos.le
  have hden_pos : 0 < u ^ 3 := by positivity
  have hnum_ge : (1 / 2 : ℝ) ≤ r * (1 + r) := by nlinarith [hr.1]
  have hb_lower : (1 / 2 : ℝ) / u ^ 3 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    dsimp [u] at hden_pos ⊢
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hx_sq : ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2 ≤
      fragPermSaddleBReal r := by
    calc
      ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) ^ 2
          = (1 / 4 : ℝ) * u ^ (-(3 : ℝ)) := by
            rw [mul_pow]
            norm_num
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
      _ ≤ (1 / 2 : ℝ) * u ^ (-(3 : ℝ)) := by
            have hpow_nonneg : 0 ≤ u ^ (-(3 : ℝ)) := Real.rpow_nonneg hu_nonneg _
            nlinarith
      _ = (1 / 2 : ℝ) / u ^ 3 := by
            rw [Real.rpow_neg hu_nonneg]
            have hu3 : u ^ (3 : ℝ) = u ^ 3 := by
              norm_num [Real.rpow_natCast]
            rw [hu3]
            ring
      _ ≤ fragPermSaddleBReal r := hb_lower
  have hsqrt := Real.le_sqrt_of_sq_le hx_sq
  simpa [u] using hsqrt

lemma fragPerm_delta_sqrt_b_lower_of_Ioo_half_one {r : ℝ}
    (hr : r ∈ Set.Ioo ((1 : ℝ) / 2) 1) :
    (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ)) ≤
      fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r) := by
  have hs := fragPerm_sqrt_b_lower_of_Ioo_half_one hr
  have hδ_nonneg : 0 ≤ (1 - r) ^ (7 / 5 : ℝ) :=
    Real.rpow_nonneg (by linarith [hr.2] : 0 ≤ 1 - r) _
  have hmul := mul_le_mul_of_nonneg_left hs hδ_nonneg
  calc
    (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))
        = (1 - r) ^ (7 / 5 : ℝ) *
            ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by
          have hu_pos : 0 < 1 - r := by linarith [hr.2]
          calc
            (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))
                = (1 / 2 : ℝ) *
                    ((1 - r) ^ (7 / 5 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by
                  rw [← Real.rpow_add hu_pos]
                  norm_num
            _ = (1 - r) ^ (7 / 5 : ℝ) *
                ((1 / 2 : ℝ) * (1 - r) ^ (-(3 / 2 : ℝ))) := by
                  ring
    _ ≤ fragPermSaddleDeltaReal r * Real.sqrt (fragPermSaddleBReal r) := by
          simpa [fragPermSaddleDeltaReal] using hmul

lemma fragPerm_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => fragPermSaddleDeltaReal r *
      Real.sqrt (fragPermSaddleBReal r)) fragPermRadFilter atTop := by
  have hbase : Tendsto (fun r : ℝ =>
      (1 / 2 : ℝ) * (1 - r) ^ (-(1 / 10 : ℝ))) fragPermRadFilter atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
      fragPerm_one_sub_rpow_neg_tendsto_atTop
  refine tendsto_atTop_mono' fragPermRadFilter ?_ hbase
  filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
  exact fragPerm_delta_sqrt_b_lower_of_Ioo_half_one hr

lemma fragPerm_delta_sq_le_one_sub_sq_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2 := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  have hu_le_one : 1 - r ≤ 1 := by linarith [hr.1]
  calc
    (fragPermSaddleDeltaReal r) ^ 2 = (1 - r) ^ (14 / 5 : ℝ) := by
      unfold fragPermSaddleDeltaReal
      rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 2]
      norm_num
    _ ≤ (1 - r) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one
        (by norm_num : (2 : ℝ) ≤ 14 / 5)
    _ = (1 - r) ^ 2 := by norm_num [Real.rpow_natCast]

lemma fragPermH_re_circle (r θ : ℝ) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re =
      r * (Real.cos θ - r) / fragPermDenom r θ := by
  unfold fragPermH fragPermDenom
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im, Complex.mul_im]
  simp [Complex.normSq_apply]
  have hcosre : (Complex.cos (θ : ℂ)).re = Real.cos θ := by
    exact (congrArg Complex.re (Complex.ofReal_cos θ)).symm
  have hsinre : (Complex.sin (θ : ℂ)).re = Real.sin θ := by
    exact (congrArg Complex.re (Complex.ofReal_sin θ)).symm
  rw [hcosre, hsinre]
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  ring_nf
  rw [hsin]
  ring_nf

lemma fragPermDenom_pos {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < fragPermDenom r θ := by
  unfold fragPermDenom
  have hu : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
  have hterm : 0 ≤ 2 * r * (1 - Real.cos θ) := by
    have hcos : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    positivity
  nlinarith

lemma fragPermH_real_re (r : ℝ) (hr1 : r < 1) :
    (fragPermH (r : ℂ)).re = r / (1 - r) := by
  unfold fragPermH
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  have hne : 1 - r ≠ 0 := by linarith
  field_simp [hne]

lemma fragPermH_re_drop_eq {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re =
      -fragPermSaddleBReal r *
        (((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ) := by
  rw [fragPermH_re_circle, fragPermH_real_re r hr1]
  have hD : fragPermDenom r θ ≠ 0 := (fragPermDenom_pos hr0 hr1).ne'
  have hu : 1 - r ≠ 0 := by linarith
  unfold fragPermSaddleBReal
  field_simp [hD, hu]
  unfold fragPermDenom
  ring_nf

lemma fragPerm_tail_ratio_lower {r θ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    fragPermTailRatioC * (fragPermSaddleDeltaReal r) ^ 2 ≤
      ((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ := by
  let u := 1 - r
  let x := 1 - Real.cos θ
  let δ2 := (fragPermSaddleDeltaReal r) ^ 2
  have hx_nonneg : 0 ≤ x := by dsimp [x]; linarith [Real.cos_le_one θ]
  have hD_pos : 0 < fragPermDenom r θ := fragPermDenom_pos hr0 hr1
  have hδ_nonneg : 0 ≤ fragPermSaddleDeltaReal r := by
    unfold fragPermSaddleDeltaReal
    exact Real.rpow_nonneg (by linarith : 0 ≤ 1 - r) _
  have hδ2_nonneg : 0 ≤ δ2 := sq_nonneg _
  have hk_pos : 0 < 2 / Real.pi ^ 2 := by positivity
  have hA_nonneg : 0 ≤ fragPermTailRatioC := by
    unfold fragPermTailRatioC
    positivity
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθπ
  have hx_lower_k : (2 / Real.pi ^ 2) * δ2 ≤ x := by
    have hθsq : δ2 ≤ θ ^ 2 := by
      calc
        δ2 ≤ |θ| ^ 2 := pow_le_pow_left₀ hδ_nonneg hθδ 2
        _ = θ ^ 2 := by rw [sq_abs]
    dsimp [x]
    calc
      (2 / Real.pi ^ 2) * δ2 ≤ (2 / Real.pi ^ 2) * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hθsq hk_pos.le
      _ ≤ 1 - Real.cos θ := by linarith
  have hA_le_k_half : fragPermTailRatioC ≤ (2 / Real.pi ^ 2) / 2 := by
    unfold fragPermTailRatioC
    field_simp [Real.pi_ne_zero]
    norm_num
  have hx_lower_A : 2 * fragPermTailRatioC * δ2 ≤ x := by
    calc
      2 * fragPermTailRatioC * δ2 ≤ (2 / Real.pi ^ 2) * δ2 := by
        have : 2 * fragPermTailRatioC ≤ 2 / Real.pi ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right this hδ2_nonneg
      _ ≤ x := hx_lower_k
  have hcoef_half :
      (1 / 2 : ℝ) * u ^ 2 ≤ u ^ 2 - 2 * fragPermTailRatioC * r * δ2 := by
    have h2A_r_delta :
        2 * fragPermTailRatioC * r * δ2 ≤ (1 / 2 : ℝ) * u ^ 2 := by
      have h2Aδ_nonneg : 0 ≤ 2 * fragPermTailRatioC * δ2 := by nlinarith
      calc
        2 * fragPermTailRatioC * r * δ2
            = (2 * fragPermTailRatioC * δ2) * r := by ring
        _ ≤ (2 * fragPermTailRatioC * δ2) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hr1]) h2Aδ_nonneg
        _ = 2 * fragPermTailRatioC * 1 * δ2 := by ring
        _ ≤ (1 / 2 : ℝ) * δ2 := by
          have hcoef : 2 * fragPermTailRatioC * 1 ≤ (1 / 2 : ℝ) := by
            unfold fragPermTailRatioC
            have hpi2_ge : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
            have hden_pos : 0 < 3 * Real.pi ^ 2 := by positivity
            field_simp [Real.pi_ne_zero]
            nlinarith
          exact mul_le_mul_of_nonneg_right hcoef hδ2_nonneg
        _ ≤ (1 / 2 : ℝ) * u ^ 2 := by
          exact mul_le_mul_of_nonneg_left (by simpa [u, δ2] using hδsq) (by norm_num)
    nlinarith
  have h2Aδ_nonneg : 0 ≤ 2 * fragPermTailRatioC * δ2 := by nlinarith
  have hmul := mul_le_mul hcoef_half hx_lower_A h2Aδ_nonneg
    (by nlinarith [sq_nonneg u])
  have hmain_num :
      fragPermTailRatioC * δ2 * fragPermDenom r θ ≤ (1 - r) ^ 2 * x := by
    unfold fragPermDenom
    dsimp [u, x, δ2] at hmul hcoef_half hx_lower_A ⊢
    nlinarith
  rw [le_div_iff₀ hD_pos]
  simpa [fragPermDenom, x, δ2, mul_assoc, mul_left_comm, mul_comm] using hmain_num

lemma fragPerm_re_drop_le_neg_tail_scale {r θ : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re
      ≤ -fragPermTailRatioC * fragPermSaddleBReal r *
          (fragPermSaddleDeltaReal r) ^ 2 := by
  have hratio := fragPerm_tail_ratio_lower hr0 hr1 hδsq hθδ hθπ
  have hb_nonneg : 0 ≤ fragPermSaddleBReal r := by
    unfold fragPermSaddleBReal
    have hu_nonneg : 0 ≤ 1 - r := by linarith
    have hden_nonneg : 0 ≤ (1 - r) ^ 3 := by positivity
    have hnum_nonneg : 0 ≤ r * (1 + r) := by nlinarith [hr0]
    exact div_nonneg hnum_nonneg hden_nonneg
  rw [fragPermH_re_drop_eq hr0 hr1]
  have hmul :
      fragPermTailRatioC * (fragPermSaddleDeltaReal r) ^ 2 *
          fragPermSaddleBReal r ≤
        (((1 - r) ^ 2 * (1 - Real.cos θ)) / fragPermDenom r θ) *
          fragPermSaddleBReal r :=
    mul_le_mul_of_nonneg_right hratio hb_nonneg
  nlinarith

lemma fragPerm_tail_scale_lower {r : ℝ}
    (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1) :
    fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)) ≤
      fragPermTailRatioC * fragPermSaddleBReal r *
        (fragPermSaddleDeltaReal r) ^ 2 := by
  have hrate_nonneg : 0 ≤ (1 - r) ^ (-(1 / 5 : ℝ)) :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 - r) _
  have hratio_nonneg : 0 ≤ fragPermTailRatioC := by
    unfold fragPermTailRatioC
    positivity
  have hscale :
      fragPermSaddleBReal r * (fragPermSaddleDeltaReal r) ^ 2 =
        r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ)) := by
    have hu_pos : 0 < 1 - r := by linarith
    have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
    unfold fragPermSaddleBReal fragPermSaddleDeltaReal
    rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 2]
    norm_num
    have hpow3 : (1 - r) ^ 3 = (1 - r) ^ (3 : ℝ) :=
      (Real.rpow_natCast (1 - r) 3).symm
    rw [hpow3]
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
    calc
      r * (1 + r) * (1 - r) ^ (-3 : ℝ) *
          (1 - r) ^ (14 / 5 : ℝ)
          = r * (1 + r) *
              ((1 - r) ^ (-3 : ℝ) * (1 - r) ^ (14 / 5 : ℝ)) := by ring
      _ = r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ)) := by
        rw [← Real.rpow_add hu_pos]
        norm_num
  calc
    fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ))
        ≤ ((fragPermTailRatioC) * (3 / 4 : ℝ)) *
            (1 - r) ^ (-(1 / 5 : ℝ)) := by
          have hconst : fragPermTailC ≤ fragPermTailRatioC * (3 / 4 : ℝ) := by
            unfold fragPermTailC fragPermTailRatioC
            field_simp [Real.pi_ne_zero]
            norm_num
          exact mul_le_mul_of_nonneg_right hconst hrate_nonneg
    _ ≤ (fragPermTailRatioC * (r * (1 + r))) *
          (1 - r) ^ (-(1 / 5 : ℝ)) := by
        have hprod : (3 / 4 : ℝ) ≤ r * (1 + r) := by nlinarith [hrhalf]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod hratio_nonneg) hrate_nonneg
    _ = fragPermTailRatioC *
          (r * (1 + r) * (1 - r) ^ (-(1 / 5 : ℝ))) := by ring
    _ = fragPermTailRatioC *
          (fragPermSaddleBReal r * (fragPermSaddleDeltaReal r) ^ 2) := by
            rw [hscale]
    _ = fragPermTailRatioC * fragPermSaddleBReal r *
          (fragPermSaddleDeltaReal r) ^ 2 := by ring

lemma fragPerm_re_drop_le_neg_tail_rate {r θ : ℝ}
    (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1)
    (hδsq : (fragPermSaddleDeltaReal r) ^ 2 ≤ (1 - r) ^ 2)
    (hθδ : fragPermSaddleDeltaReal r ≤ |θ|) (hθπ : |θ| ≤ Real.pi) :
    (fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
        (fragPermH (r : ℂ)).re
      ≤ -fragPermTailC * (1 - r) ^ (-(1 / 5 : ℝ)) := by
  have hr0 : 0 ≤ r := by linarith [hrhalf]
  have hscale := fragPerm_re_drop_le_neg_tail_scale hr0 hr1 hδsq hθδ hθπ
  have hlower := fragPerm_tail_scale_lower hrhalf hr1
  nlinarith

lemma fragPerm_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt fragPermFun r n θ‖ =
      Real.exp
        ((fragPermH ((r : ℂ) * Complex.exp (θ * Complex.I))).re -
          (fragPermH (r : ℂ)).re) := by
  unfold saddleGAt fragPermFun fragPermH
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
          (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))) /
        Complex.exp ((r : ℂ) / (1 - (r : ℂ))) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        =
      Real.exp
          ((((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
            (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))).re) /
        Real.exp (((r : ℂ) / (1 - (r : ℂ))).re) := by
          rw [norm_mul, hphase, mul_one, norm_div, Complex.norm_exp, Complex.norm_exp]
    _ =
      Real.exp
        ((((r : ℂ) * Complex.exp (↑θ * Complex.I)) /
            (1 - (r : ℂ) * Complex.exp (↑θ * Complex.I))).re -
          ((r : ℂ) / (1 - (r : ℂ))).re) := by
          rw [← Real.exp_sub]

lemma fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop :
    Tendsto (fun r : ℝ => (1 - r) ^ (-(1 / 5 : ℝ))) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hpow : Tendsto (fun r : ℝ => ((1 - r)⁻¹) ^ (1 / 5 : ℝ))
      fragPermRadFilter atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hinv
  refine Tendsto.congr' ?_ hpow
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hnonneg : 0 ≤ 1 - r := by linarith [hr.2]
  rw [Real.inv_rpow hnonneg]
  rw [← Real.rpow_neg hnonneg]

lemma fragPermTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, 0 ≤ fragPermTailE r :=
  Eventually.of_forall fun _ => by
    unfold fragPermTailE
    positivity

lemma fragPermTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
      fragPermTailE r) fragPermRadFilter (𝓝 0) := by
  let c : ℝ := fragPermTailC
  have hc : 0 < c := by
    dsimp [c, fragPermTailC]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (15 / 2 : ℝ) * Real.exp (-c * y))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (15 / 2 : ℝ) c hc
  have hy := fragPerm_one_sub_rpow_neg_one_fifth_tendsto_atTop
  have hcomp :
      Tendsto
        (fun r : ℝ => ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) *
          Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ)))))
        fragPermRadFilter (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto
        (fun r : ℝ => Real.sqrt (4 * Real.pi) *
          (((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) *
            Real.exp (-c * ((1 - r) ^ (-(1 / 5 : ℝ))))))
        fragPermRadFilter (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    let u : ℝ := 1 - r
    have hu_pos : 0 < u := by dsimp [u]; linarith [hr.2]
    have hu_nonneg : 0 ≤ u := hu_pos.le
    have hnum_le : r * (1 + r) ≤ 2 := by nlinarith [hr.1, hr.2]
    have hB_le : fragPermSaddleBReal r ≤ 2 / u ^ 3 := by
      unfold fragPermSaddleBReal
      dsimp [u]
      have hden_pos : 0 < (1 - r) ^ 3 := by positivity
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    have hmul : 2 * Real.pi * fragPermSaddleBReal r ≤ 4 * Real.pi / u ^ 3 := by
      calc
        2 * Real.pi * fragPermSaddleBReal r
            ≤ 2 * Real.pi * (2 / u ^ 3) :=
              mul_le_mul_of_nonneg_left hB_le (by positivity)
        _ = 4 * Real.pi / u ^ 3 := by ring
    have hsqrt :
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
      calc
        Real.sqrt (2 * Real.pi * fragPermSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi / u ^ 3) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [div_eq_mul_inv]
          rw [Real.sqrt_mul h4pi]
          have hsqrt_inv_u3 : Real.sqrt ((u ^ 3)⁻¹) = u ^ (-(3 / 2 : ℝ)) := by
            have hinv_u3 : (u ^ 3)⁻¹ = u ^ (-3 : ℝ) := by
              rw [show u ^ 3 = u ^ (3 : ℝ) by exact (Real.rpow_natCast u 3).symm]
              rw [← Real.rpow_neg hu_nonneg (3 : ℝ)]
            rw [hinv_u3]
            rw [Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hu_nonneg]
            norm_num
          congr 1
    have hy_pow :
        ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) =
          u ^ (-(3 / 2 : ℝ)) := by
      have h :
          ((1 - r) ^ (-(1 / 5 : ℝ))) ^ (15 / 2 : ℝ) =
            (1 - r) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1 - r)]
        norm_num
      simpa [u] using h
    unfold fragPermTailE
    dsimp [c, fragPermTailC]
    rw [hy_pow]
    calc
      Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) *
          Real.exp (-(1 / (4 * Real.pi ^ 2)) *
            (1 - r) ^ (-(1 / 5 : ℝ)))
          ≤ (Real.sqrt (4 * Real.pi) * u ^ (-(3 / 2 : ℝ))) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ))) :=
            mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
      _ = Real.sqrt (4 * Real.pi) *
            (u ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(1 / (4 * Real.pi ^ 2)) *
                (1 - r) ^ (-(1 / 5 : ℝ)))) := by ring

lemma fragPerm_tail_bound_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
      fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt fragPermFun r n θ‖ ≤ fragPermTailE r := by
  filter_upwards [fragPerm_eventually_Ioo_half_one,
    fragPerm_delta_sq_le_one_sub_sq_eventually] with r hr hδsq n θ hθδ hθπ
  rw [fragPerm_saddleGAt_norm]
  unfold fragPermTailE
  exact Real.exp_le_exp.mpr
    (fragPerm_re_drop_le_neg_tail_rate hr.1.le hr.2 hδsq hθδ hθπ)

lemma fragPerm_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r) := by
  exact ⟨fragPermTailE, fragPermTailE_nonneg_eventually, fragPermTailE_decay,
    fragPerm_tail_bound_eventually⟩

lemma fragPerm_differentiableOn_closedBall_of_radius_lt_one {R : ℝ≥0}
    (hR : (R : ℝ≥0∞) < (1 : ℝ≥0∞)) :
    DifferentiableOn ℂ fragPermFun (Metric.closedBall (0 : ℂ) R) := by
  intro z hz
  have hRlt : (R : ℝ) < 1 := by
    exact ENNReal.coe_lt_one_iff.mp hR
  have hnorm_le : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzne : (1 : ℂ) - z ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have hnorm_one : ‖z‖ = 1 := by simp [hz_eq]
    have : (1 : ℝ) ≤ R := by simpa [hnorm_one] using hnorm_le
    linarith
  unfold fragPermFun
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z) z := differentiableAt_id
  have hden : DifferentiableAt ℂ (fun z : ℂ => (1 : ℂ) - z) z :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hquot : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) z :=
    hnum.div hden hzne
  exact (Complex.differentiable_exp.differentiableAt.comp z hquot).differentiableWithinAt

lemma fragPermSeries_one_le_radius :
    (1 : ℝ≥0∞) ≤ fragPermSeries.radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun R hRlt => ?_
  rcases eq_or_lt_of_le (zero_le R) with rfl | hRpos
  · exact zero_le _
  rcases fragPermFun_hasFPowerSeriesAt_zero with ⟨r0, hbase⟩
  have hdiff := fragPerm_differentiableOn_closedBall_of_radius_lt_one hRlt
  have hcauchy := hdiff.hasFPowerSeriesOnBall hRpos
  exact (hbase.exchange_radius hcauchy).r_le

lemma fragPerm_hasFPowerSeriesOnBall_one :
    HasFPowerSeriesOnBall fragPermFun fragPermSeries (0 : ℂ) (1 : ℝ≥0∞) := by
  refine ⟨fragPermSeries_one_le_radius, by norm_num, ?_⟩
  intro y hy
  rw [mem_eball_zero_iff] at hy
  obtain ⟨R, hyR, hRone⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  rcases eq_or_lt_of_le (zero_le R) with rfl | hRpos
  · simp at hyR
  rcases fragPermFun_hasFPowerSeriesAt_zero with ⟨r0, hbase⟩
  have hdiff := fragPerm_differentiableOn_closedBall_of_radius_lt_one hRone
  have hcauchy := hdiff.hasFPowerSeriesOnBall hRpos
  exact (hbase.exchange_radius hcauchy).hasSum (mem_eball_zero_iff.mpr hyR)

lemma fragPermFun_norm_tendsto_atTop :
    Tendsto (fun r : ℝ => ‖fragPermFun (r : ℂ)‖) fragPermRadFilter atTop := by
  have hinv : Tendsto (fun r : ℝ => (1 - r)⁻¹) fragPermRadFilter atTop :=
    tendsto_inv_nhdsGT_zero.comp fragPerm_one_sub_tendsto_nhdsGT_zero
  have hhalf_inv :
      Tendsto (fun r : ℝ => (1 / 2 : ℝ) * (1 - r)⁻¹) fragPermRadFilter atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hinv
  have hquot : Tendsto (fun r : ℝ => r / (1 - r)) fragPermRadFilter atTop := by
    refine tendsto_atTop_mono' fragPermRadFilter ?_ hhalf_inv
    filter_upwards [fragPerm_eventually_Ioo_half_one] with r hr
    have hinv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith [hr.2] : 0 ≤ 1 - r)
    calc
      (1 / 2 : ℝ) * (1 - r)⁻¹ ≤ r * (1 - r)⁻¹ :=
        mul_le_mul_of_nonneg_right hr.1.le hinv_nonneg
      _ = r / (1 - r) := by rw [div_eq_mul_inv]
  refine Tendsto.congr' ?_ (Real.tendsto_exp_atTop.comp hquot)
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  unfold fragPermFun
  have harg : (r : ℂ) / (1 - (r : ℂ)) = ((r / (1 - r) : ℝ) : ℂ) := by
    norm_num
  rw [Complex.norm_exp]
  exact congrArg Real.exp (congrArg Complex.re harg).symm

lemma fragPermSeries_radius_le_one :
    fragPermSeries.radius ≤ (1 : ℝ≥0∞) := by
  by_contra hnot
  have hgt : (1 : ℝ≥0∞) < fragPermSeries.radius := lt_of_not_ge hnot
  have hpos : 0 < fragPermSeries.radius :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) fragPermSeries_one_le_radius
  have hpball : HasFPowerSeriesOnBall fragPermSeries.sum fragPermSeries (0 : ℂ)
      fragPermSeries.radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall fragPermSeries hpos
  have hmem_one : (1 : ℂ) ∈ Metric.eball (0 : ℂ) fragPermSeries.radius := by
    simpa [mem_eball_zero_iff] using hgt
  have hcont :
      ContinuousAt fragPermSeries.sum (1 : ℂ) :=
    (hpball.analyticAt_of_mem hmem_one).continuousAt
  have hreal_to_one : Tendsto (fun r : ℝ => r) fragPermRadFilter (𝓝 (1 : ℝ)) := by
    unfold fragPermRadFilter
    exact tendsto_id.mono_right (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio (1 : ℝ)))
  have hcomplex_to_one : Tendsto (fun r : ℝ => (r : ℂ)) fragPermRadFilter (𝓝 (1 : ℂ)) := by
    exact Filter.tendsto_ofReal_iff.mpr hreal_to_one
  have hfinite :
      Tendsto (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) fragPermRadFilter
        (𝓝 ‖fragPermSeries.sum (1 : ℂ)‖) := by
    have hnorm_cont : ContinuousAt (fun z : ℂ => ‖fragPermSeries.sum z‖) (1 : ℂ) :=
      hcont.norm
    exact hnorm_cont.tendsto.comp hcomplex_to_one
  have heq :
      (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) =ᶠ[fragPermRadFilter]
        fun r : ℝ => ‖fragPermFun (r : ℂ)‖ := by
    filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
    have hy : (r : ℂ) ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) := by
      rw [mem_eball_zero_iff]
      rw [← ENNReal.coe_one]
      exact ENNReal.coe_lt_coe.2 (by
        apply NNReal.coe_lt_coe.mp
        simpa [NNReal.coe_one, coe_nnnorm, abs_of_nonneg hr.1.le] using hr.2)
    have hsum := fragPerm_hasFPowerSeriesOnBall_one.sum hy
    rw [← hsum]
    simp
  have hatTop :
      Tendsto (fun r : ℝ => ‖fragPermSeries.sum (r : ℂ)‖) fragPermRadFilter atTop :=
    Tendsto.congr' heq.symm fragPermFun_norm_tendsto_atTop
  haveI : fragPermRadFilter.NeBot := fragPermRadFilter_neBot
  exact (not_tendsto_atTop_of_tendsto_nhds hfinite) hatTop

lemma fragPermSeries_radius_eq_one_proved :
    fragPermSeries.radius = (1 : ℝ≥0∞) :=
  le_antisymm fragPermSeries_radius_le_one fragPermSeries_one_le_radius

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def fragPermLocalExponent (r θ : ℝ) : ℂ :=
  fragPermH ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) -
    fragPermH (r : ℂ) -
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I +
        ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ)

lemma fragPerm_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ =
      Complex.exp (fragPermLocalExponent r θ) := by
  unfold saddleLocalRatio fragPermFun fragPermLocalExponent
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  ring

lemma fragPerm_exp_i_sub_one_norm_le_two_abs {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_le (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

lemma fragPerm_exp_i_sub_one_sub_id_norm_le_sq {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ |θ| ^ 2 := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

lemma fragPermLocalExponent_decomp {r θ : ℝ} (hr1 : r < 1)
    (hy : (1 : ℂ) -
        (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) / (1 - (r : ℂ)) ≠ 0) :
    let u : ℂ := 1 - (r : ℂ)
    let w : ℂ := (θ : ℂ) * Complex.I
    let q : ℂ := Complex.exp w - 1
    let y : ℂ := (r : ℂ) * q / u
    fragPermLocalExponent r θ =
      ((r : ℂ) / u ^ 2) * ExpStirling.expLocalRemainder θ +
        (((r : ℂ) ^ 2 / u ^ 3) * (q ^ 2 - w ^ 2)) +
          (((r : ℂ) ^ 3 / u ^ 4) * q ^ 3 * (1 - y)⁻¹) := by
  dsimp
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  have hu_ne : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [u] at hre
    linarith
  have hmain_den : (1 : ℂ) - (r : ℂ) * Complex.exp w ≠ 0 := by
    intro hzero
    apply hy
    have heq :
        (1 : ℂ) -
            (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) / (1 - (r : ℂ)) =
          ((1 : ℂ) - (r : ℂ) * Complex.exp w) / (1 - (r : ℂ)) := by
      change (1 : ℂ) - (r : ℂ) * (Complex.exp w - 1) / (1 - (r : ℂ)) =
        ((1 : ℂ) - (r : ℂ) * Complex.exp w) / (1 - (r : ℂ))
      field_simp [hu_ne]
      have haux : (1 : ℂ) + (r : ℂ) * (1 - (r : ℂ))⁻¹ =
          (1 - (r : ℂ))⁻¹ := by
        have hurne : (1 - r : ℝ) ≠ 0 := by linarith
        have hreal : (1 : ℝ) + r * (1 - r)⁻¹ = (1 - r)⁻¹ := by
          field_simp [hurne]
          ring
        exact_mod_cast hreal
      linear_combination haux
    rw [heq, hzero]
    simp
  have huq_ne : u - (r : ℂ) * q ≠ 0 := by
    have hden_eq : (1 : ℂ) - (r : ℂ) * Complex.exp w = u - (r : ℂ) * q := by
      dsimp [u, q]
      ring
    rwa [hden_eq] at hmain_den
  have hdiff :
      fragPermH ((r : ℂ) * Complex.exp w) - fragPermH (r : ℂ) =
        (r : ℂ) * q / (u * (u - (r : ℂ) * q)) := by
    have hrat {a q u : ℂ} (hu : u = 1 - a) (huq : u - a * q ≠ 0) (hu0 : u ≠ 0) :
        a * (1 + q) / (1 - a * (1 + q)) - a / (1 - a) =
          a * q / (u * (u - a * q)) := by
      subst u
      have h1 : (1 : ℂ) - a ≠ 0 := hu0
      have h2 : (1 : ℂ) - a * (1 + q) ≠ 0 := by
        simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using huq
      field_simp [h1, h2]
      ring
    have hexp : Complex.exp w = 1 + q := by
      dsimp [q]
      ring
    unfold fragPermH
    rw [hexp]
    exact hrat (a := (r : ℂ)) (q := q) (u := u) rfl huq_ne hu_ne
  have hgeom :
      (r : ℂ) * q / (u * (u - (r : ℂ) * q)) =
        ((r : ℂ) / u ^ 2) * q +
          (((r : ℂ) ^ 2 / u ^ 3) * q ^ 2) +
            (((r : ℂ) ^ 3 / u ^ 4) * q ^ 3 *
              (1 - (r : ℂ) * q / u)⁻¹) := by
    field_simp [hu_ne, huq_ne, hy]
    ring
  have hq :
      q = w - ((θ ^ 2 / 2 : ℝ) : ℂ) + ExpStirling.expLocalRemainder θ := by
    dsimp [q, w]
    rw [ExpStirling.expLocalRemainder_eq]
    ring
  have hlin :
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I =
        ((r : ℂ) / u ^ 2) * w := by
    unfold fragPermSaddleAReal
    dsimp [u, w]
    have hurne : (1 - r : ℝ) ≠ 0 := by linarith
    field_simp [hurne]
    norm_num [Complex.ext_iff]
  have hquad :
      ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ) =
        ((r : ℂ) / u ^ 2) * (((θ ^ 2 / 2 : ℝ) : ℂ)) -
          (((r : ℂ) ^ 2 / u ^ 3) * (w ^ 2)) := by
    unfold fragPermSaddleBReal
    dsimp [u, w]
    have hurne : (1 - r : ℝ) ≠ 0 := by linarith
    have hw2 : ((θ : ℂ) * Complex.I) ^ 2 = -((θ ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq]
      norm_num
    rw [hw2]
    have hreal : r * (1 + r) / (1 - r) ^ 3 * θ ^ 2 / 2 =
        r / (1 - r) ^ 2 * (θ ^ 2 / 2) - (r ^ 2 / (1 - r) ^ 3) * (-(θ ^ 2)) := by
      field_simp [hurne]
      ring
    exact_mod_cast hreal
  unfold fragPermLocalExponent
  rw [hdiff, hgeom]
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let C : ℂ := (r : ℂ) ^ 3 / u ^ 4 * q ^ 3 * (1 - (r : ℂ) * q / u)⁻¹
  let T : ℂ := ((θ ^ 2 / 2 : ℝ) : ℂ)
  change A * q + B * q ^ 2 + C -
      ((fragPermSaddleAReal r * θ : ℝ) : ℂ) * Complex.I +
        ((fragPermSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ) =
    A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C
  rw [hlin, hquad]
  change A * q + B * q ^ 2 + C - A * w + (A * T - B * w ^ 2) =
    A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C
  rw [hq]
  ring

def fragPermLocalConstant : ℝ :=
  100 * Real.exp 1

lemma fragPermLocalConstant_pos : 0 < fragPermLocalConstant := by
  unfold fragPermLocalConstant
  positivity

lemma fragPerm_delta_le_one_sub_quarter_eventually :
    ∀ᶠ r : ℝ in fragPermRadFilter,
      fragPermSaddleDeltaReal r ≤ (1 - r) / 4 := by
  have hnhds : Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  have hpow :
      Tendsto (fun r : ℝ => (1 - r) ^ (2 / 5 : ℝ)) fragPermRadFilter (𝓝 0) := by
    simpa using hnhds.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 5))
  have hsmall :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        (1 - r) ^ (2 / 5 : ℝ) ≤ (1 / 4 : ℝ) :=
    hpow.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [fragPerm_eventually_Ioo_zero_one, hsmall] with r hr hsmallr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  calc
    fragPermSaddleDeltaReal r = (1 - r) ^ (1 : ℝ) * (1 - r) ^ (2 / 5 : ℝ) := by
      unfold fragPermSaddleDeltaReal
      rw [← Real.rpow_add hu_pos]
      norm_num
    _ ≤ (1 - r) * (1 / 4 : ℝ) :=
      by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hsmallr hu_nonneg
    _ = (1 - r) / 4 := by ring

def fragPermLocalControl (r : ℝ) : ℝ :=
  (1 - r) ^ (1 / 5 : ℝ)

lemma fragPermLocalControl_tendsto_zero :
    Tendsto fragPermLocalControl fragPermRadFilter (𝓝 0) := by
  have hnhds : Tendsto (fun r : ℝ => 1 - r) fragPermRadFilter (𝓝 (0 : ℝ)) :=
    fragPerm_one_sub_tendsto_nhdsGT_zero.mono_right
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  change Tendsto (fun r : ℝ => (1 - r) ^ (1 / 5 : ℝ)) fragPermRadFilter (𝓝 0)
  have h := hnhds.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 5))
  simpa using h

lemma fragPerm_local_scale_eq_control_eventually :
    (fun r : ℝ => (fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4)
      =ᶠ[fragPermRadFilter] fragPermLocalControl := by
  filter_upwards [fragPerm_eventually_Ioo_zero_one] with r hr
  have hu_pos : 0 < 1 - r := by linarith [hr.2]
  have hu_nonneg : 0 ≤ 1 - r := hu_pos.le
  unfold fragPermSaddleDeltaReal fragPermLocalControl
  rw [← Real.rpow_mul_natCast hu_nonneg (7 / 5 : ℝ) 3]
  norm_num
  have hpow4 : (1 - r) ^ 4 = (1 - r) ^ (4 : ℝ) :=
    (Real.rpow_natCast (1 - r) 4).symm
  rw [hpow4]
  rw [div_eq_mul_inv, ← Real.rpow_neg hu_nonneg (4 : ℝ), ← Real.rpow_add hu_pos]
  norm_num

lemma fragPermLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ =>
      fragPermLocalConstant * ((fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4))
      fragPermRadFilter (𝓝 0) := by
  have hscale :
    Tendsto (fun r : ℝ => (fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4)
        fragPermRadFilter (𝓝 0) :=
    Tendsto.congr' fragPerm_local_scale_eq_control_eventually.symm
      fragPermLocalControl_tendsto_zero
  simpa using hscale.const_mul fragPermLocalConstant

set_option maxHeartbeats 800000 in
lemma fragPerm_local_exponent_norm_le
    {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hδ_le_one : fragPermSaddleDeltaReal r ≤ 1)
    (hδ_le_u_quarter : fragPermSaddleDeltaReal r ≤ (1 - r) / 4)
    (hθ : |θ| ≤ fragPermSaddleDeltaReal r) :
    ‖fragPermLocalExponent r θ‖ ≤
      fragPermLocalConstant * ((fragPermSaddleDeltaReal r) ^ 3 / (1 - r) ^ 4) := by
  let δ : ℝ := fragPermSaddleDeltaReal r
  let uR : ℝ := 1 - r
  let u : ℂ := 1 - (r : ℂ)
  let w : ℂ := (θ : ℂ) * Complex.I
  let q : ℂ := Complex.exp w - 1
  let y : ℂ := (r : ℂ) * q / u
  have hu_pos : 0 < uR := by dsimp [uR]; linarith [hr1]
  have hu_nonneg : 0 ≤ uR := hu_pos.le
  have hu_le_one : uR ≤ 1 := by dsimp [uR]; linarith [hr0]
  have hu_ne : u ≠ 0 := by
    dsimp [u, uR] at *
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hr_norm : ‖(r : ℂ)‖ = r :=
    (RCLike.norm_ofReal (K := ℂ) r).trans (abs_of_nonneg hr0)
  have hu_norm : ‖u‖ = uR := by
    dsimp [u, uR]
    have hcoerce : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hcoerce]
    exact (RCLike.norm_ofReal (K := ℂ) (1 - r)).trans (abs_of_pos hu_pos)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, fragPermSaddleDeltaReal]
    exact Real.rpow_nonneg hu_nonneg _
  have hθ_one : |θ| ≤ 1 := hθ.trans hδ_le_one
  have hθ_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have hθ2δ2 : |θ| ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ hθ_nonneg (by simpa [δ] using hθ) 2
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ hθ_nonneg (by simpa [δ] using hθ) 3
  have hq_norm : ‖q‖ ≤ 2 * |θ| := by
    simpa [q, w] using fragPerm_exp_i_sub_one_norm_le_two_abs hθ_one
  have hq_norm_delta : ‖q‖ ≤ 2 * δ := by
    exact hq_norm.trans (mul_le_mul_of_nonneg_left (by simpa [δ] using hθ)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hy_norm : ‖y‖ ≤ (1 / 2 : ℝ) := by
    have hnorm_eq : ‖y‖ = r * ‖q‖ / uR := by
      dsimp [y, u, uR]
      rw [norm_div, norm_mul]
      rw [hr_norm, hu_norm]
    calc
      ‖y‖ = r * ‖q‖ / uR := hnorm_eq
      _ ≤ r * (2 * δ) / uR := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq_norm_delta hr0) hu_nonneg
      _ ≤ 1 * (2 * δ) / uR := by
        have hr_le_one : r ≤ 1 := hr1.le
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hr_le_one (by positivity : 0 ≤ 2 * δ)) hu_nonneg
      _ ≤ 1 / 2 := by
        have hδu : 2 * δ ≤ uR / 2 := by linarith [hδ_le_u_quarter]
        rw [one_mul]
        have hu_neR : uR ≠ 0 := hu_pos.ne'
        rw [div_le_iff₀ hu_pos]
        nlinarith
  have hy_ne : (1 : ℂ) - y ≠ 0 := by
    intro hzero
    have hy_eq : y = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [hy_eq] using hy_norm
    norm_num at this
  have hdecomp := fragPermLocalExponent_decomp (r := r) (θ := θ) hr1 hy_ne
  dsimp [u, w, q, y] at hdecomp
  rw [hdecomp]
  let A : ℂ := (r : ℂ) / u ^ 2
  let B : ℂ := (r : ℂ) ^ 2 / u ^ 3
  let C : ℂ := (r : ℂ) ^ 3 / u ^ 4 * q ^ 3 * (1 - y)⁻¹
  have hη : ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 1 * |θ| ^ 3 :=
    ExpStirling.expLocalRemainder_norm_le_exp_one θ hθ_one
  have hA_norm : ‖A‖ = r / uR ^ 2 := by
    dsimp [A, u, uR]
    rw [norm_div, norm_pow]
    rw [hr_norm, hu_norm]
  have hB_norm : ‖B‖ = r ^ 2 / uR ^ 3 := by
    dsimp [B, u, uR]
    rw [norm_div, norm_pow, norm_pow]
    rw [hr_norm, hu_norm]
  have hCcoef_norm : ‖((r : ℂ) ^ 3 / u ^ 4)‖ = r ^ 3 / uR ^ 4 := by
    dsimp [u, uR]
    rw [norm_div, norm_pow, norm_pow]
    rw [hr_norm, hu_norm]
  have hterm1 :
      ‖A * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 1 * δ ^ 3 / uR ^ 4 := by
    rw [norm_mul, hA_norm]
    calc
      r / uR ^ 2 * ‖ExpStirling.expLocalRemainder θ‖
          ≤ r / uR ^ 2 * (Real.exp 1 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hη (by positivity)
      _ ≤ r / uR ^ 2 * (Real.exp 1 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 1).le) (by positivity)
      _ ≤ Real.exp 1 * δ ^ 3 / uR ^ 4 := by
        have hr_le_one : r ≤ 1 := hr1.le
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        have hu2_le_one : uR ^ 2 ≤ 1 := by nlinarith [hu_nonneg, hu_le_one]
        have hru2_le_one : r * uR ^ 2 ≤ 1 := by nlinarith [hr0, hr_le_one, hu2_le_one]
        field_simp [hu_pos.ne']
        nlinarith [hru2_le_one, hδ3_nonneg, Real.exp_pos 1]
  have hq_sub_w : ‖q - w‖ ≤ δ ^ 2 := by
    have hbase := fragPerm_exp_i_sub_one_sub_id_norm_le_sq hθ_one
    calc
      ‖q - w‖ = ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ := by
        dsimp [q, w]
      _ ≤ |θ| ^ 2 := hbase
      _ ≤ δ ^ 2 := hθ2δ2
  have hq_plus_w : ‖q + w‖ ≤ 3 * δ := by
    calc
      ‖q + w‖ ≤ ‖q‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 * δ + δ := by
        have hw_norm : ‖w‖ = |θ| := by dsimp [w]; simp
        rw [hw_norm]
        exact add_le_add hq_norm_delta (by simpa [δ] using hθ)
      _ = 3 * δ := by ring
  have hq_sq_sub : ‖q ^ 2 - w ^ 2‖ ≤ 3 * δ ^ 3 := by
    have hfac : q ^ 2 - w ^ 2 = (q - w) * (q + w) := by ring
    rw [hfac, norm_mul]
    calc
      ‖q - w‖ * ‖q + w‖ ≤ δ ^ 2 * (3 * δ) :=
        mul_le_mul hq_sub_w hq_plus_w (norm_nonneg _) (by positivity)
      _ = 3 * δ ^ 3 := by ring
  have hterm2 :
      ‖B * (q ^ 2 - w ^ 2)‖ ≤ 3 * δ ^ 3 / uR ^ 4 := by
    rw [norm_mul, hB_norm]
    calc
      r ^ 2 / uR ^ 3 * ‖q ^ 2 - w ^ 2‖
          ≤ r ^ 2 / uR ^ 3 * (3 * δ ^ 3) :=
        mul_le_mul_of_nonneg_left hq_sq_sub (by positivity)
      _ ≤ 3 * δ ^ 3 / uR ^ 4 := by
        have hr2_le_one : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1.le]
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        have hru_le_one : r ^ 2 * uR ≤ 1 := by nlinarith [hr2_le_one, hu_nonneg, hu_le_one]
        field_simp [hu_pos.ne']
        nlinarith [hru_le_one, hδ3_nonneg]
  have hinv_norm : ‖(1 - y)⁻¹‖ ≤ 2 := by
    have hdist : (1 / 2 : ℝ) ≤ ‖1 - y‖ := by
      calc
        (1 / 2 : ℝ) ≤ 1 - ‖y‖ := by linarith [hy_norm]
        _ ≤ ‖(1 : ℂ) - y‖ := by
          have h := norm_sub_norm_le (1 : ℂ) y
          have hone : ‖(1 : ℂ)‖ = (1 : ℝ) := by norm_num
          rw [hone] at h
          linarith
    rw [norm_inv]
    have hnorm_pos : 0 < ‖(1 : ℂ) - y‖ := norm_pos_iff.mpr hy_ne
    rw [inv_le_comm₀ hnorm_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hdist]
  have hq3 : ‖q ^ 3‖ ≤ (2 * δ) ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hq_norm_delta 3
  have hterm3 :
      ‖C‖ ≤ 16 * δ ^ 3 / uR ^ 4 := by
    dsimp [C]
    rw [norm_mul, norm_mul, hCcoef_norm]
    calc
      r ^ 3 / uR ^ 4 * ‖q ^ 3‖ * ‖(1 - y)⁻¹‖
          ≤ r ^ 3 / uR ^ 4 * ((2 * δ) ^ 3) * 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hq3 (by positivity)) hinv_norm
          (norm_nonneg _) (by positivity)
      _ ≤ 16 * δ ^ 3 / uR ^ 4 := by
        have hr3_le_one : r ^ 3 ≤ 1 := by nlinarith [hr0, hr1.le]
        have hδ3_nonneg : 0 ≤ δ ^ 3 := by positivity
        field_simp [hu_pos.ne']
        nlinarith [hr3_le_one, hδ3_nonneg]
  have hsum :
      ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖ ≤
        (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4 := by
    calc
      ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖
          ≤ ‖A * ExpStirling.expLocalRemainder θ‖ +
              ‖B * (q ^ 2 - w ^ 2)‖ + ‖C‖ := by
        calc
          ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2) + C‖
              ≤ ‖A * ExpStirling.expLocalRemainder θ + B * (q ^ 2 - w ^ 2)‖ + ‖C‖ :=
            norm_add_le _ _
          _ ≤ (‖A * ExpStirling.expLocalRemainder θ‖ +
                  ‖B * (q ^ 2 - w ^ 2)‖) + ‖C‖ :=
            by
              have h := norm_add_le (A * ExpStirling.expLocalRemainder θ)
                (B * (q ^ 2 - w ^ 2))
              nlinarith
          _ = ‖A * ExpStirling.expLocalRemainder θ‖ +
              ‖B * (q ^ 2 - w ^ 2)‖ + ‖C‖ := by ring
      _ ≤ Real.exp 1 * δ ^ 3 / uR ^ 4 + 3 * δ ^ 3 / uR ^ 4 +
            16 * δ ^ 3 / uR ^ 4 := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4 := by ring
  refine hsum.trans ?_
  have hnonneg : 0 ≤ δ ^ 3 / uR ^ 4 := by positivity
  have hconst : Real.exp 1 + 3 + 16 ≤ 100 * Real.exp 1 := by
    have hone_le : (1 : ℝ) ≤ Real.exp 1 := by
      exact Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    nlinarith
  calc
    (Real.exp 1 + 3 + 16) * δ ^ 3 / uR ^ 4
        = (Real.exp 1 + 3 + 16) * (δ ^ 3 / uR ^ 4) := by ring
    _ ≤ fragPermLocalConstant * (δ ^ 3 / uR ^ 4) := by
      unfold fragPermLocalConstant
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    _ = fragPermLocalConstant *
        (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) := by
      simp [δ, uR]

lemma fragPerm_local_uniform_proved :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) ≤ ε / 2 :=
    fragPermLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in fragPermRadFilter,
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) ≤ 1 :=
    fragPermLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [fragPerm_eventually_Ioo_zero_one, fragPerm_delta_le_one_eventually,
    fragPerm_delta_le_one_sub_quarter_eventually, hsmall, hone] with
      r hr hδ_one hδ_u hsmallr honer θ hθ
  rw [fragPerm_saddleLocalRatio_eq]
  have hz :
      ‖fragPermLocalExponent r θ‖ ≤
        fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4) :=
    fragPerm_local_exponent_norm_le hr.1.le hr.2 hδ_one hδ_u hθ
  have hz_one : ‖fragPermLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (fragPermLocalExponent r θ) - 1‖
        ≤ 2 * ‖fragPermLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 *
        (fragPermLocalConstant *
          (fragPermSaddleDeltaReal r ^ 3 / (1 - r) ^ 4)) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

/-- Radius and local uniform estimates for `exp (z/(1-z))`. -/
lemma fragPerm_radius_and_local_uniform_gap :
    fragPermSeries.radius = (1 : ℝ≥0∞) ∧
    (∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε) := by
  exact ⟨fragPermSeries_radius_eq_one_proved, fragPerm_local_uniform_proved⟩

lemma fragPermSeries_radius_eq_one :
    fragPermSeries.radius = (1 : ℝ≥0∞) :=
  fragPerm_radius_and_local_uniform_gap.1

lemma fragPerm_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε :=
  fragPerm_radius_and_local_uniform_gap.2

/-- The finite-radius Hayman local and tail estimates for `exp (z/(1-z))`. -/
lemma fragPerm_hayman_uniform_estimates :
    (∀ ε > 0, ∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ θ : ℝ,
      |θ| ≤ fragPermSaddleDeltaReal r →
        ‖saddleLocalRatio fragPermFun fragPermSaddleAReal fragPermSaddleBReal r θ - 1‖ ≤ ε) ∧
    (∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in fragPermRadFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * fragPermSaddleBReal r) * E r)
        fragPermRadFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in fragPermRadFilter, ∀ n : ℕ, ∀ θ : ℝ,
        fragPermSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt fragPermFun r n θ‖ ≤ E r)) := by
  exact ⟨fragPerm_local_uniform, fragPerm_tail_uniform⟩

/-- Explicit saddle radius solving `r/(1-r)^2=n`. -/
def fragPermSaddleRadius (n : ℕ) : ℝ :=
  1 - 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1)

lemma fragPermSaddleRadius_lt_one (n : ℕ) :
    fragPermSaddleRadius n < 1 := by
  unfold fragPermSaddleRadius
  have hden_pos : 0 < Real.sqrt (4 * (n : ℝ) + 1) + 1 := by positivity
  have hfrac_pos : 0 < 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1) := by positivity
  linarith

lemma fragPermSaddleRadius_nonneg (n : ℕ) :
    0 ≤ fragPermSaddleRadius n := by
  unfold fragPermSaddleRadius
  have hs_ge_one : 1 ≤ Real.sqrt (4 * (n : ℝ) + 1) := by
    have hs : Real.sqrt (1 : ℝ) ≤ Real.sqrt (4 * (n : ℝ) + 1) := by
      exact Real.sqrt_le_sqrt (by
        have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        nlinarith : (1 : ℝ) ≤ 4 * (n : ℝ) + 1)
    convert hs using 1
    simp
  have hden_pos : 0 < Real.sqrt (4 * (n : ℝ) + 1) + 1 := by positivity
  have hle : 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1) ≤ 1 := by
    rw [div_le_iff₀ hden_pos]
    linarith
  linarith

lemma fragPermSaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < fragPermSaddleRadius n := by
  unfold fragPermSaddleRadius
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs_gt_one : 1 < Real.sqrt (4 * (n : ℝ) + 1) := by
    have hs : Real.sqrt (1 : ℝ) < Real.sqrt (4 * (n : ℝ) + 1) := by
      exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (by nlinarith [hnR] : (1 : ℝ) < 4 * (n : ℝ) + 1)
    simpa using hs
  have hden_pos : 0 < Real.sqrt (4 * (n : ℝ) + 1) + 1 := by positivity
  have hlt : 2 / (Real.sqrt (4 * (n : ℝ) + 1) + 1) < 1 := by
    rw [div_lt_iff₀ hden_pos]
    linarith
  linarith

lemma fragPermSaddleAReal_radius (n : ℕ) :
    fragPermSaddleAReal (fragPermSaddleRadius n) = (n : ℝ) := by
  unfold fragPermSaddleAReal fragPermSaddleRadius
  let s : ℝ := Real.sqrt (4 * (n : ℝ) + 1)
  have hs_nonneg_arg : 0 ≤ 4 * (n : ℝ) + 1 := by positivity
  have hs_sq : s ^ 2 = 4 * (n : ℝ) + 1 := by
    dsimp [s]
    exact Real.sq_sqrt hs_nonneg_arg
  have hs_pos : 0 < s + 1 := by
    dsimp [s]
    positivity
  have hne : s + 1 ≠ 0 := hs_pos.ne'
  field_simp [hne]
  nlinarith

lemma fragPermSaddleRadius_tendsto_radFilter :
    Tendsto fragPermSaddleRadius atTop fragPermRadFilter := by
  unfold fragPermRadFilter
  rw [tendsto_nhdsWithin_iff]
  constructor
  · unfold fragPermSaddleRadius
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hmul : Tendsto (fun n : ℕ => (4 : ℝ) * (n : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hn
    have hlin : Tendsto (fun n : ℕ => (4 : ℝ) * (n : ℝ) + 1) atTop atTop :=
      hmul.atTop_add tendsto_const_nhds
    have hden : Tendsto
        (fun n : ℕ => Real.sqrt (4 * (n : ℝ) + 1) + 1) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp hlin).atTop_add tendsto_const_nhds
    have hfrac : Tendsto
        (fun n : ℕ => (2 : ℝ) / (Real.sqrt (4 * (n : ℝ) + 1) + 1))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have hsub : Tendsto
        (fun n : ℕ => (1 : ℝ) -
          (2 : ℝ) / (Real.sqrt (4 * (n : ℝ) + 1) + 1))
        atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hfrac
    simpa using hsub
  · exact Eventually.of_forall fun n => fragPermSaddleRadius_lt_one n

def fragPermHAdmissible : HAdmissible fragPermFun fragPermSeries where
  ρ := (1 : ℝ≥0∞)
  radFilter := fragPermRadFilter
  a := fragPermSaddleAReal
  b := fragPermSaddleBReal
  δ := fragPermSaddleDeltaReal
  hp := fragPermFun_hasFPowerSeriesAt_zero
  radius_eq := fragPermSeries_radius_eq_one
  radius_pos := by norm_num
  rad_neBot := fragPermRadFilter_neBot
  r_pos := fragPerm_r_pos_eventually
  differentiableOn := fragPerm_differentiableOn_eventually
  f_pos := fragPerm_f_pos_eventually
  b_pos := fragPerm_b_pos_eventually
  δ_pos := fragPerm_delta_pos_eventually
  δ_le_pi := fragPerm_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := fragPerm_delta_sqrt_b_tendsto_atTop
  local_uniform := fragPerm_hayman_uniform_estimates.1
  tail_uniform := fragPerm_hayman_uniform_estimates.2

def fragPermHAdmissibleSaddleSequence : SaddleSequence fragPermHAdmissible where
  r := fragPermSaddleRadius
  tendsTo := by
    simpa [fragPermHAdmissible] using fragPermSaddleRadius_tendsto_radFilter
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change fragPermSaddleAReal (fragPermSaddleRadius n) = (n : ℝ)
      exact fragPermSaddleAReal_radius n

theorem fragPerm_coeff_isEquivalent_saddle_from_HAdmissible :
    (fun n : ℕ => fragPermSeries.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale fragPermFun fragPermSaddleRadius
        (fun n => fragPermSaddleBReal (fragPermSaddleRadius n)) n) := by
  have h := coeff_isEquivalent_saddle fragPermHAdmissible fragPermHAdmissibleSaddleSequence
  simpa [HAdmissible.B, fragPermHAdmissibleSaddleSequence, fragPermHAdmissible] using h

end FragmentedPermHAdmissible
