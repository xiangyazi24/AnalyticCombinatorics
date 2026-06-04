import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeq

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

namespace SupercriticalSeqGenuine

/-- Shift `C` so that the candidate singularity is at the origin. -/
def shiftedC (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  Cfun (ρ + w)

/-- The divided difference `(C(ρ+w)-C(ρ))/w`, with the derivative value at `w=0`. -/
def cdiv (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  dslope (shiftedC Cfun ρ) 0 w

/-- The divided difference of `cdiv`; this is the analytic numerator left after the pole is
subtracted. -/
def cdivSlope (Cfun : ℂ → ℂ) (ρ : ℂ) (w : ℂ) : ℂ :=
  dslope (cdiv Cfun ρ) 0 w

/-- The removable remainder after subtracting `(1/C'(ρ))/(ρ-z)` from `1/(1-C(z))`. -/
def remainderFun (Cfun : ℂ → ℂ) (ρ Cderiv : ℂ) (z : ℂ) : ℂ :=
  cdivSlope Cfun ρ (z - ρ) / (Cderiv * cdiv Cfun ρ (z - ρ))

lemma shiftedC_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (shiftedC Cfun ρ) p 0 := by
  rcases hC with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hp' : HasFPowerSeriesAt (fun z : ℂ => Cfun (z + ρ)) p (0 : ℂ) := by
    simpa using hp.comp_sub (-ρ)
  exact hp'.congr (Eventually.of_forall fun z => by
    simp [shiftedC, add_comm])

lemma cdiv_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (cdiv Cfun ρ) p 0 := by
  rcases shiftedC_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cdiv] using hp.has_fpower_series_dslope_fslope⟩

lemma cdiv_analyticAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    AnalyticAt ℂ (cdiv Cfun ρ) 0 := by
  rcases cdiv_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p, hp⟩

lemma shiftedC_hasDerivAt_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    HasDerivAt (shiftedC Cfun ρ) Cderiv 0 := by
  have h' : HasDerivAt Cfun Cderiv (ρ + 0) := by
    simpa using hderiv
  have hshift := h'.comp_const_add ρ (0 : ℂ)
  simpa [shiftedC] using hshift

lemma cdiv_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    cdiv Cfun ρ 0 = Cderiv := by
  rw [cdiv, dslope_same]
  exact (shiftedC_hasDerivAt_zero (Cfun := Cfun) (ρ := ρ) hderiv).deriv

lemma cdiv_of_ne
    {Cfun : ℂ → ℂ} {ρ w : ℂ} (hw : w ≠ 0) :
    cdiv Cfun ρ w = w⁻¹ * (Cfun (ρ + w) - Cfun ρ) := by
  rw [cdiv, dslope_of_ne (shiftedC Cfun ρ) hw]
  simp [shiftedC, slope_def_module, smul_eq_mul]

lemma cdiv_shift_eq
    {Cfun : ℂ → ℂ} {ρ Cρ w : ℂ} (hCρ : Cfun ρ = Cρ) :
    Cfun (ρ + w) = Cρ + w * cdiv Cfun ρ w := by
  have h := sub_smul_dslope (shiftedC Cfun ρ) (0 : ℂ) w
  change (w - 0) • cdiv Cfun ρ w = shiftedC Cfun ρ w - shiftedC Cfun ρ 0 at h
  have h' : w * cdiv Cfun ρ w = Cfun (ρ + w) - Cρ := by
    simpa [shiftedC, hCρ, smul_eq_mul] using h
  calc
    Cfun (ρ + w) = Cρ + (Cfun (ρ + w) - Cρ) := by ring
    _ = Cρ + w * cdiv Cfun ρ w := by rw [← h']

lemma cdiv_analyticAt_of_ne
    {Cfun : ℂ → ℂ} {ρ w : ℂ} (hw : w ≠ 0)
    (hCw : AnalyticAt ℂ Cfun (ρ + w)) :
    AnalyticAt ℂ (cdiv Cfun ρ) w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (Cfun (ρ + u) - Cfun ρ)) w := by
    have hshift : AnalyticAt ℂ (fun u : ℂ => ρ + u) w :=
      analyticAt_const.add analyticAt_id
    have hCshift : AnalyticAt ℂ (fun u : ℂ => Cfun (ρ + u)) w :=
      AnalyticAt.comp' (𝕜 := ℂ) (g := Cfun) (f := fun u : ℂ => ρ + u)
        (x := w) hCw hshift
    exact (analyticAt_id.inv hw).mul
      (hCshift.sub (analyticAt_const (𝕜 := ℂ) (v := Cfun ρ) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne (shiftedC Cfun ρ) hw).mono fun u hu => by
    simpa [cdiv, shiftedC, slope_def_module, smul_eq_mul] using hu.symm

lemma cdiv_analyticAt_of_shift
    {Cfun : ℂ → ℂ} {ρ w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w)) :
    AnalyticAt ℂ (cdiv Cfun ρ) w := by
  by_cases hw : w = 0
  · simpa [hw] using cdiv_analyticAt_zero (Cfun := Cfun) (ρ := ρ) hCρ
  · exact cdiv_analyticAt_of_ne (Cfun := Cfun) (ρ := ρ) hw hCw

lemma cdivSlope_hasFPowerSeriesAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (cdivSlope Cfun ρ) p 0 := by
  rcases cdiv_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cdivSlope] using hp.has_fpower_series_dslope_fslope⟩

lemma cdivSlope_analyticAt_zero
    {Cfun : ℂ → ℂ} {ρ : ℂ} (hC : AnalyticAt ℂ Cfun ρ) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) 0 := by
  rcases cdivSlope_hasFPowerSeriesAt_zero (Cfun := Cfun) (ρ := ρ) hC with ⟨p, hp⟩
  exact ⟨p, hp⟩

lemma cdivSlope_of_ne
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hw : w ≠ 0) :
    cdivSlope Cfun ρ w = w⁻¹ * (cdiv Cfun ρ w - Cderiv) := by
  rw [cdivSlope, dslope_of_ne (cdiv Cfun ρ) hw]
  simp [slope_def_module, cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv, smul_eq_mul]

lemma cdiv_eq_deriv_add
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    cdiv Cfun ρ w = Cderiv + w * cdivSlope Cfun ρ w := by
  have h := sub_smul_dslope (cdiv Cfun ρ) (0 : ℂ) w
  change (w - 0) • cdivSlope Cfun ρ w =
    cdiv Cfun ρ w - cdiv Cfun ρ 0 at h
  rw [cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv] at h
  have h' : w * cdivSlope Cfun ρ w = cdiv Cfun ρ w - Cderiv := by
    simpa [smul_eq_mul] using h
  calc
    cdiv Cfun ρ w = Cderiv + (cdiv Cfun ρ w - Cderiv) := by ring
    _ = Cderiv + w * cdivSlope Cfun ρ w := by rw [← h']

lemma cdivSlope_analyticAt_of_ne
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w))
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hw : w ≠ 0) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (cdiv Cfun ρ u - Cderiv)) w := by
    exact (analyticAt_id.inv hw).mul
      ((cdiv_analyticAt_of_shift (Cfun := Cfun) (ρ := ρ) hCρ hCw).sub
        (analyticAt_const (𝕜 := ℂ) (v := Cderiv) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne (cdiv Cfun ρ) hw).mono fun u hu => by
    simpa [cdivSlope, slope_def_module,
      cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv, smul_eq_mul] using hu.symm

lemma cdivSlope_analyticAt_of_shift
    {Cfun : ℂ → ℂ} {ρ Cderiv w : ℂ}
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCw : AnalyticAt ℂ Cfun (ρ + w))
    (hderiv : HasDerivAt Cfun Cderiv ρ) :
    AnalyticAt ℂ (cdivSlope Cfun ρ) w := by
  by_cases hw : w = 0
  · simpa [hw] using cdivSlope_analyticAt_zero (Cfun := Cfun) (ρ := ρ) hCρ
  · exact cdivSlope_analyticAt_of_ne
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) hCρ hCw hderiv hw

lemma cdiv_ne_zero_of_ne
    {Cfun : ℂ → ℂ} {ρ z : ℂ}
    (hCρ : Cfun ρ = 1) (hden : 1 - Cfun z ≠ 0) :
    cdiv Cfun ρ (z - ρ) ≠ 0 := by
  intro hzero
  have hshift := cdiv_shift_eq (Cfun := Cfun) (ρ := ρ) (Cρ := 1)
    (w := z - ρ) hCρ
  have hzsplit : ρ + (z - ρ) = z := by ring
  rw [hzsplit, hzero, mul_zero, add_zero] at hshift
  apply hden
  rw [hshift]
  ring

lemma cdiv_ne_zero_at
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : z ≠ ρ → 1 - Cfun z ≠ 0) :
    cdiv Cfun ρ (z - ρ) ≠ 0 := by
  by_cases hz : z = ρ
  · simpa [hz] using cdiv_zero (Cfun := Cfun) (ρ := ρ) hderiv ▸ hCderiv_ne
  · exact cdiv_ne_zero_of_ne (Cfun := Cfun) (ρ := ρ) hCρ (hden hz)

lemma analyticAt_remainderFun
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ_value : Cfun ρ = 1)
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCz : AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : z ≠ ρ → 1 - Cfun z ≠ 0) :
    AnalyticAt ℂ (remainderFun Cfun ρ Cderiv) z := by
  have hshift : AnalyticAt ℂ (fun y : ℂ => y - ρ) z :=
    analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := ρ) (x := z))
  have hCw : AnalyticAt ℂ Cfun (ρ + (z - ρ)) := by
    convert hCz using 1
    ring
  have hnum0 : AnalyticAt ℂ (cdivSlope Cfun ρ) (z - ρ) :=
    cdivSlope_analyticAt_of_shift
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) hCρ hCw hderiv
  have hden0 : AnalyticAt ℂ (cdiv Cfun ρ) (z - ρ) :=
    cdiv_analyticAt_of_shift (Cfun := Cfun) (ρ := ρ) hCρ hCw
  have hnum : AnalyticAt ℂ (fun y : ℂ => cdivSlope Cfun ρ (y - ρ)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cdivSlope Cfun ρ)
      (f := fun y : ℂ => y - ρ) (x := z) hnum0 hshift
  have hden_cdiv : AnalyticAt ℂ (fun y : ℂ => cdiv Cfun ρ (y - ρ)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cdiv Cfun ρ)
      (f := fun y : ℂ => y - ρ) (x := z) hden0 hshift
  have hconst : AnalyticAt ℂ (fun _ : ℂ => Cderiv) z :=
    analyticAt_const (𝕜 := ℂ) (v := Cderiv) (x := z)
  have hden_an : AnalyticAt ℂ
      (fun y : ℂ => Cderiv * cdiv Cfun ρ (y - ρ)) z :=
    hconst.mul hden_cdiv
  have hden_ne : Cderiv * cdiv Cfun ρ (z - ρ) ≠ 0 :=
    mul_ne_zero hCderiv_ne
      (cdiv_ne_zero_at (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv)
        hCρ_value hderiv hCderiv_ne hden)
  change AnalyticAt ℂ
    (fun y : ℂ =>
      cdivSlope Cfun ρ (y - ρ) / (Cderiv * cdiv Cfun ρ (y - ρ))) z
  exact hnum.div hden_an hden_ne

theorem remainderFun_differentiableOn_closedBall
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hCρ_value : Cfun ρ = 1)
    (hCρ : AnalyticAt ℂ Cfun ρ)
    (hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) S, AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0) :
    DifferentiableOn ℂ (remainderFun Cfun ρ Cderiv) (Metric.closedBall (0 : ℂ) S) := by
  intro z hz
  exact (analyticAt_remainderFun
    (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (z := z)
    hCρ_value hCρ (hCan z hz) hderiv hCderiv_ne
    (fun hzρ => hden z hz hzρ)).differentiableAt.differentiableWithinAt

lemma remainderFun_eq_inv_sub_principal
    {Cfun : ℂ → ℂ} {ρ Cderiv z : ℂ}
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hz : z ≠ ρ) (hden : 1 - Cfun z ≠ 0) :
    remainderFun Cfun ρ Cderiv z =
      (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹ := by
  let w : ℂ := z - ρ
  let Sdiv : ℂ := cdiv Cfun ρ w
  let Tdiv : ℂ := cdivSlope Cfun ρ w
  let A : ℂ := Cderiv
  have hw : w ≠ 0 := by
    dsimp [w]
    exact sub_ne_zero.mpr hz
  have hS : Sdiv ≠ 0 := by
    dsimp [Sdiv, w]
    exact cdiv_ne_zero_of_ne (Cfun := Cfun) (ρ := ρ) hCρ hden
  have hA : A ≠ 0 := by simpa [A] using hCderiv_ne
  have hzsplit : ρ + w = z := by
    dsimp [w]
    ring
  have hCz : Cfun z = 1 + w * Sdiv := by
    rw [← hzsplit]
    simpa [Sdiv] using cdiv_shift_eq (Cfun := Cfun) (ρ := ρ) (Cρ := 1)
      (w := w) hCρ
  have hSrel : Sdiv = A + w * Tdiv := by
    simpa [Sdiv, Tdiv, A, w] using
      cdiv_eq_deriv_add (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (w := z - ρ)
        hderiv
  have hrz : ρ - z = -w := by
    dsimp [w]
    ring
  rw [remainderFun]
  change Tdiv / (A * Sdiv) =
    (1 - Cfun z)⁻¹ - A⁻¹ * (ρ - z)⁻¹
  rw [hCz, hrz]
  field_simp [hw, hS, hA]
  rw [hSrel]
  ring

theorem inv_sub_principal_eventuallyEq_remainderFun_at_zero
    {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρS : ‖ρ‖ < S)
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0) :
    (fun z : ℂ => (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹)
      =ᶠ[𝓝 (0 : ℂ)] remainderFun Cfun ρ Cderiv := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hzball
  have hz_norm : ‖z‖ < ‖ρ‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) S := by
    have hzS : ‖z‖ ≤ S := (hz_norm.trans hρS).le
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzS
  have hz_ne : z ≠ ρ := by
    intro h
    have hnorm : ‖z‖ = ‖ρ‖ := by rw [h]
    linarith
  exact (remainderFun_eq_inv_sub_principal
    (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (z := z)
    hCρ hderiv hCderiv_ne hz_ne (hden z hz_closed hz_ne)).symm

/-- Formal simple-pole principal part with analytic function `c/(ρ-z)`. -/
def principalSeries (ρ c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (c * ρ⁻¹) *
    PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic function represented at the origin by `principalSeries ρ c`. -/
def principalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  c * (ρ - z)⁻¹

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

theorem principalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (principalFun ρ c) (PowerSeries.toFMLS (principalSeries ρ c)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hz
  have hz_norm : ‖z‖ < ‖ρ‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hρ_ne : ρ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hρ)
  have hzr : ‖z * ρ⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv]
    have hpos : 0 < ‖ρ‖⁻¹ := inv_pos.mpr hρ
    calc
      ‖z‖ * ‖ρ‖⁻¹ < ‖ρ‖ * ‖ρ‖⁻¹ :=
        mul_lt_mul_of_pos_right hz_norm hpos
      _ = 1 := by
        field_simp [ne_of_gt hρ]
  have hlin_ne : 1 - z * ρ⁻¹ ≠ 0 := by
    intro h
    have hzreq : z * ρ⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖z * ρ⁻¹‖ = 1 := by
      rw [hzreq, norm_one]
    linarith
  have hrz_ne : ρ - z ≠ 0 := by
    intro h
    have hzrho : ρ = z := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖ρ‖ := by
      rw [← hzrho]
    linarith
  have hsum :
      HasSum (fun n : ℕ => (c * ρ⁻¹) * (z * ρ⁻¹) ^ n)
        ((c * ρ⁻¹) * (1 - z * ρ⁻¹)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hzr).mul_left (c * ρ⁻¹)
  convert hsum using 1
  · ext n
    rw [PowerSeries.coeff_toFMLS]
    change z ^ n * PowerSeries.coeff (R := ℂ) n (principalSeries ρ c) =
      (c * ρ⁻¹) * (z * ρ⁻¹) ^ n
    rw [principalSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
    rw [mul_pow]
    ring
  · simp [principalFun]
    field_simp [hρ_ne, hlin_ne, hrz_ne]

theorem remainderFun_hasFPowerSeriesAt_zero
    (F : PowerSeries ℂ) {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρS : ‖ρ‖ < S)
    (hCρ : Cfun ρ = 1)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0)
    (hF : HasFPowerSeriesAt (fun z : ℂ => (1 - Cfun z)⁻¹) (PowerSeries.toFMLS F) 0) :
    HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv)
      (PowerSeries.toFMLS (F - principalSeries ρ Cderiv⁻¹)) 0 := by
  have hprincipal :
      HasFPowerSeriesAt (principalFun ρ Cderiv⁻¹)
        (PowerSeries.toFMLS (principalSeries ρ Cderiv⁻¹)) 0 :=
    principalFun_hasFPowerSeriesAt_zero (ρ := ρ) (c := Cderiv⁻¹) hρ
  have hsub := hF.sub hprincipal
  have hsub' : HasFPowerSeriesAt
      (fun z : ℂ => (1 - Cfun z)⁻¹ - Cderiv⁻¹ * (ρ - z)⁻¹)
      (PowerSeries.toFMLS (F - principalSeries ρ Cderiv⁻¹)) 0 := by
    simpa [toFMLS_sub, principalFun] using hsub
  exact hsub'.congr
    (inv_sub_principal_eventuallyEq_remainderFun_at_zero
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
      hρ hρS hCρ hderiv hCderiv_ne hden)

/-- If a `PowerSeries` represents a function that is differentiable on a larger closed disk of
radius `S`, then its convergence radius is strictly larger than every real `R < S`. -/
theorem powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
    (G : PowerSeries ℂ) {gfun : ℂ → ℂ} {R S : ℝ}
    (hS : 0 < S) (hRS : R < S)
    (hp : HasFPowerSeriesAt gfun (PowerSeries.toFMLS G) 0)
    (hd : DifferentiableOn ℂ gfun (Metric.closedBall (0 : ℂ) S)) :
    ENNReal.ofReal R < (PowerSeries.toFMLS G).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS G
  have hcoeffO :
      (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => S⁻¹ ^ n) :=
    coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
      (g := gfun) (p := p) (R := S) hS hp hd
  have hcancel :
      (fun n : ℕ => (S⁻¹ ^ n) * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hpow : S⁻¹ ^ n * S ^ n = 1 := by
      rw [← mul_pow]
      field_simp [ne_of_gt hS]
      simp
    rw [hpow]
    norm_num
  have hcoeffMul :
      (fun n : ℕ => ‖p.coeff n‖ * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact (hcoeffO.mul (isBigO_refl (fun n : ℕ => S ^ n) atTop)).trans hcancel
  have hnorm_eq :
      (fun n : ℕ => ‖p n‖ * S ^ n) =ᶠ[atTop]
        (fun n : ℕ => ‖p.coeff n‖ * S ^ n) := by
    exact Eventually.of_forall fun n => by
      have hpn : ‖p n‖ = ‖p.coeff n‖ := by
        simp [p, PowerSeries.toFMLS]
      change ‖p n‖ * S ^ n = ‖p.coeff n‖ * S ^ n
      rw [hpn]
  have hterm :
      (fun n : ℕ => ‖p n‖ * S ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hnorm_eq.trans_isBigO hcoeffMul
  have hle : ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_isBigO (r := Real.toNNReal S) (by
      simpa [p, Real.coe_toNNReal _ hS.le] using hterm)
  have hRltS : ENNReal.ofReal R < ((Real.toNNReal S : ℝ≥0) : ℝ≥0∞) := by
    simpa [ENNReal.ofNNReal_toNNReal] using
      (ENNReal.ofReal_lt_ofReal_iff hS).mpr hRS
  exact hRltS.trans_le hle

/-- Genuine supercritical-sequence decomposition: the principal-part-plus-remainder form follows
from the analytic supercritical data and the fact that `F` represents `1/(1-C)` at the origin.

The auxiliary radius `S` is the formalized "analytic on a neighborhood of the closed disk of
radius `R`" margin: differentiability on the larger closed disk gives
`ENNReal.ofReal R < radius`. -/
theorem supercriticalSeq_decomposition_from_supercritical_data
    (F : PowerSeries ℂ) {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {R S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hRS : R < S)
    (hCρ : Cfun ρ = 1)
    (hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) S, AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0)
    (hF : HasFPowerSeriesAt (fun z : ℂ => (1 - Cfun z)⁻¹) (PowerSeries.toFMLS F) 0) :
    ∃ g : PowerSeries ℂ,
      HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv) (PowerSeries.toFMLS g) 0 ∧
      ENNReal.ofReal R < (PowerSeries.toFMLS g).radius ∧
      F =
        PowerSeries.C (Cderiv⁻¹ * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g := by
  let g : PowerSeries ℂ := F - principalSeries ρ Cderiv⁻¹
  have hρS : ‖ρ‖ < S := hρR.trans hRS
  have hρ_closed : ρ ∈ Metric.closedBall (0 : ℂ) S := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hρS.le
  have hCρ_an : AnalyticAt ℂ Cfun ρ := hCan ρ hρ_closed
  have hg_has :
      HasFPowerSeriesAt (remainderFun Cfun ρ Cderiv) (PowerSeries.toFMLS g) 0 := by
    simpa [g] using
      remainderFun_hasFPowerSeriesAt_zero
        (F := F) (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
        hρ hρS hCρ hderiv hCderiv_ne hden hF
  have hg_diff :
      DifferentiableOn ℂ (remainderFun Cfun ρ Cderiv) (Metric.closedBall (0 : ℂ) S) :=
    remainderFun_differentiableOn_closedBall
      (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (S := S)
      hCρ hCρ_an hCan hderiv hCderiv_ne hden
  have hS : 0 < S := hρ.trans hρS
  have hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius :=
    powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
      (G := g) (gfun := remainderFun Cfun ρ Cderiv) (R := R) (S := S)
      hS hRS hg_has hg_diff
  have hfg_principal : F = principalSeries ρ Cderiv⁻¹ + g := by
    simp [g]
  refine ⟨g, hg_has, hgR, ?_⟩
  simpa [principalSeries] using hfg_principal

/-- Genuine F&S V.2 supercritical-sequence transfer. The principal decomposition is derived
internally from the supercritical data; it is not an input hypothesis. -/
theorem supercriticalSeq_isEquivalent_from_supercritical_data
    (F : PowerSeries ℂ) {Cfun : ℂ → ℂ} {ρ Cderiv : ℂ} {R S : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hRS : R < S)
    (hCρ : Cfun ρ = 1)
    (hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) S, AnalyticAt ℂ Cfun z)
    (hderiv : HasDerivAt Cfun Cderiv ρ) (hCderiv_ne : Cderiv ≠ 0)
    (hden : ∀ z ∈ Metric.closedBall (0 : ℂ) S, z ≠ ρ → 1 - Cfun z ≠ 0)
    (hF : HasFPowerSeriesAt (fun z : ℂ => (1 - Cfun z)⁻¹) (PowerSeries.toFMLS F) 0) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n F) ~[atTop]
      (fun n : ℕ => (1 / (ρ * Cderiv)) * ρ⁻¹ ^ n) := by
  rcases supercriticalSeq_decomposition_from_supercritical_data
      (F := F) (Cfun := Cfun) (ρ := ρ) (Cderiv := Cderiv) (R := R) (S := S)
      hρ hρR hRS hCρ hCan hderiv hCderiv_ne hden hF with
    ⟨g, _hg_has, hgR, hfg⟩
  exact supercriticalSeq_isEquivalent
    F g (ρ := ρ) (Cderiv := Cderiv) (R := R)
    hρ hρR hCderiv_ne hgR hfg

end SupercriticalSeqGenuine

end Meromorphic
end Ch5
end AnalyticCombinatorics
