import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch2.EGF.Applications
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Surjections

open AnalyticCombinatorics.Ch1

def rho : ℂ := ((Real.log 2 : ℝ) : ℂ)

def surjEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ CombClass.posInt.lseq.egf

def principal : PowerSeries ℂ :=
  PowerSeries.C ((1 / 2 : ℂ) * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

def remainder : PowerSeries ℂ :=
  surjEGFℂ - principal

namespace PowerSeries

/-- The power series whose coefficients are the scalar coefficients of a formal multilinear
series. -/
def ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => p.coeff n

@[simp] theorem coeff_ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (ofFMLS p) = p.coeff n := by
  simp [ofFMLS]

theorem toFMLS_ofFMLS (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    PowerSeries.toFMLS (ofFMLS p) = p := by
  ext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq (PowerSeries.toFMLS (ofFMLS p)) n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq p n]
  simp

end PowerSeries

lemma rho_re : rho.re = Real.log 2 := by
  exact Complex.ofReal_re (Real.log 2)

lemma rho_im : rho.im = 0 := by
  exact Complex.ofReal_im (Real.log 2)

lemma real_log_two_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)

lemma rho_ne_zero : rho ≠ 0 := by
  rw [rho]
  exact_mod_cast (ne_of_gt real_log_two_pos)

lemma rho_norm : ‖rho‖ = Real.log 2 := by
  rw [rho]
  rw [Complex.norm_of_nonneg real_log_two_pos.le]

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact real_log_two_pos

lemma rho_norm_lt_one : ‖rho‖ < 1 := by
  rw [rho_norm]
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h
  exact h

lemma half_ne_zero : (1 / 2 : ℂ) ≠ 0 := by
  norm_num

lemma principal_constant_ne_zero : (1 / 2 : ℂ) ≠ 0 := half_ne_zero

theorem surjEGFℂ_mul_denominator :
    surjEGFℂ * (1 - (PowerSeries.exp ℂ - 1)) = 1 := by
  have h := congrArg PowerSeries.mapℂ CombClass.egf_surjections
  simpa [surjEGFℂ, PowerSeries.mapℂ] using h

theorem surjEGFℂ_eq_inv_denominator :
    surjEGFℂ = (1 - (PowerSeries.exp ℂ - 1))⁻¹ := by
  have h0 : PowerSeries.constantCoeff (1 - (PowerSeries.exp ℂ - 1) : PowerSeries ℂ) ≠ 0 := by
    simp
  exact (PowerSeries.eq_inv_iff_mul_eq_one h0).2 surjEGFℂ_mul_denominator

theorem surjEGFℂ_eq_principal_add_remainder :
    surjEGFℂ = principal + remainder := by
  simp [remainder]

theorem coeff_principal_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n principal)
      ~[atTop] (fun n : ℕ => (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1)) := by
  simpa [principal] using
    (single_simplePole_principal_isEquivalent (ρ := rho) (c := (1 / 2 : ℂ)))

lemma coeff_principal (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n principal = (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1) := by
  rw [principal, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

theorem coeff_surjEGFℂ_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (1 : ℝ) < (PowerSeries.toFMLS remainder).radius) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ)
      ~[atTop] (fun n : ℕ => (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1)) := by
  exact dominant_simplePole_isEquivalent
    surjEGFℂ remainder (ρ := rho) (c := (1 / 2 : ℂ)) (R := 1)
    rho_norm_pos rho_norm_lt_one half_ne_zero hrem surjEGFℂ_eq_principal_add_remainder

lemma expMinusOne_constantCoeff :
    PowerSeries.constantCoeff (PowerSeries.exp ℂ - 1 : PowerSeries ℂ) = 0 := by
  simp

theorem surjEGFℂ_eq_geometric_subst :
    surjEGFℂ =
      (PowerSeries.invUnitsSub (1 : ℂˣ)).subst (PowerSeries.exp ℂ - 1) := by
  let H : PowerSeries ℂ := PowerSeries.exp ℂ - 1
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    simp [H]
  have hsubst : (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H * (1 - H) = 1 := by
    have hHas : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
    have hsubHX :
        (PowerSeries.C ((1 : ℂˣ) : ℂ) - PowerSeries.X).subst H = 1 - H := by
      rw [PowerSeries.subst_sub hHas, PowerSeries.subst_C, PowerSeries.subst_X hHas]
      simp
    rw [← hsubHX, ← PowerSeries.subst_mul hHas, PowerSeries.invUnitsSub_mul_sub]
    change (PowerSeries.C (1 : ℂ)).subst H = 1
    rw [PowerSeries.subst_C]
    simp
  rw [surjEGFℂ_eq_inv_denominator]
  have h0 : PowerSeries.constantCoeff (1 - H : PowerSeries ℂ) ≠ 0 := by
    simp [H]
  exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).2 hsubst).symm

lemma toFMLS_invUnitsSub_one :
    PowerSeries.toFMLS (PowerSeries.invUnitsSub (1 : ℂˣ)) =
      formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, formalMultilinearSeries_geometric_eq_ofScalars,
    FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_one :
    PowerSeries.toFMLS (1 : PowerSeries ℂ) =
      constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries]
  | succ n =>
      simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars,
        constFormalMultilinearSeries]

lemma toFMLS_powerSeries_exp :
    PowerSeries.toFMLS (PowerSeries.exp ℂ) = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_expMinusOne :
    PowerSeries.toFMLS (PowerSeries.exp ℂ - 1) =
      NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
  rw [toFMLS_sub, toFMLS_powerSeries_exp, toFMLS_one]

def expSubOne (z : ℂ) : ℂ :=
  Complex.exp z - 1

def expDiv (z : ℂ) : ℂ :=
  dslope expSubOne 0 z

def expDivSlope (z : ℂ) : ℂ :=
  dslope expDiv 0 z

def analyticRemainderFun (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (expDivSlope (z - rho) / expDiv (z - rho))

def surjAnalyticFun (z : ℂ) : ℂ :=
  (2 - Complex.exp z)⁻¹

def principalAnalyticFun (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (rho - z)⁻¹

lemma complex_exp_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (NormedSpace.expSeries ℂ ℂ) (0 : ℂ) := by
  simpa [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℂ) (𝔸 := ℂ))

lemma complex_exp_analyticAt (z : ℂ) : AnalyticAt ℂ Complex.exp z := by
  simpa [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.exp_analytic (𝕂 := ℂ) (𝔸 := ℂ) z)

lemma expSubOne_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expSubOne
      (NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)) (0 : ℂ) := by
  simpa [expSubOne, Pi.sub_apply] using
    complex_exp_hasFPowerSeriesAt_zero.sub
      (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
        (c := (1 : ℂ)) (e := (0 : ℂ)))

theorem surjAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt surjAnalyticFun (PowerSeries.toFMLS surjEGFℂ) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (0 : ℂ) :=
    (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have houter' : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (expSubOne 0) := by
    simpa [expSubOne] using houter
  have hcomp := houter'.comp expSubOne_hasFPowerSeriesAt_zero
  rw [surjEGFℂ_eq_geometric_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp expMinusOne_constantCoeff]
  rw [toFMLS_invUnitsSub_one, toFMLS_expMinusOne]
  refine hcomp.congr ?_
  filter_upwards with z
  simp [surjAnalyticFun, expSubOne]
  ring_nf

theorem principalAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt principalAnalyticFun (PowerSeries.toFMLS principal) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rho_norm_pos] with z hz
  have hz_norm : ‖z‖ < ‖rho‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hzr : ‖z * rho⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv]
    have hpos : 0 < ‖rho‖⁻¹ := inv_pos.mpr rho_norm_pos
    calc
      ‖z‖ * ‖rho‖⁻¹ < ‖rho‖ * ‖rho‖⁻¹ :=
        mul_lt_mul_of_pos_right hz_norm hpos
      _ = 1 := by
        field_simp [ne_of_gt rho_norm_pos]
  have hlin_ne : 1 - z * rho⁻¹ ≠ 0 := by
    intro h
    have hzreq : z * rho⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖z * rho⁻¹‖ = 1 := by
      rw [hzreq, norm_one]
    linarith
  have hrz_ne : rho - z ≠ 0 := by
    intro h
    have hzrho : rho = z := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖rho‖ := by
      rw [← hzrho]
    linarith
  have hsum :
      HasSum (fun n : ℕ => ((1 / 2 : ℂ) * rho⁻¹) * (z * rho⁻¹) ^ n)
        (((1 / 2 : ℂ) * rho⁻¹) * (1 - z * rho⁻¹)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hzr).mul_left ((1 / 2 : ℂ) * rho⁻¹)
  convert hsum using 1
  · ext n
    rw [PowerSeries.coeff_toFMLS, coeff_principal]
    simp [smul_eq_mul]
    rw [pow_succ, mul_pow]
    ring
  · simp [principalAnalyticFun]
    field_simp [rho_ne_zero, hlin_ne, hrz_ne]

lemma expDiv_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expDiv
      (NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)).fslope
      (0 : ℂ) := by
  simpa [expDiv] using expSubOne_hasFPowerSeriesAt_zero.has_fpower_series_dslope_fslope

lemma expDiv_analyticAt_zero : AnalyticAt ℂ expDiv (0 : ℂ) :=
  expDiv_hasFPowerSeriesAt_zero.analyticAt

lemma expDiv_of_ne {z : ℂ} (hz : z ≠ 0) :
    expDiv z = z⁻¹ * (Complex.exp z - 1) := by
  rw [expDiv, dslope_of_ne expSubOne hz]
  simp [expSubOne, slope_def_module, smul_eq_mul]

lemma expDiv_zero : expDiv 0 = 1 := by
  rw [expDiv, dslope_same]
  change deriv expSubOne (0 : ℂ) = 1
  rw [show expSubOne = fun z : ℂ => Complex.exp z - 1 by rfl]
  rw [deriv_sub_const]
  rw [Complex.deriv_exp]
  simp

lemma expDiv_analyticAt_of_ne {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ expDiv z := by
  have hmodel : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * (Complex.exp w - 1)) z :=
    (analyticAt_id.inv hz).mul
      ((complex_exp_analyticAt z).sub
        (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne expSubOne hz).mono fun w hw => by
    simpa [expDiv, expSubOne, slope_def_module, smul_eq_mul] using hw.symm

lemma expDiv_analyticAt (z : ℂ) : AnalyticAt ℂ expDiv z := by
  by_cases hz : z = 0
  · simpa [hz] using expDiv_analyticAt_zero
  · exact expDiv_analyticAt_of_ne hz

lemma expDivSlope_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt expDivSlope
      ((NormedSpace.expSeries ℂ ℂ - constFormalMultilinearSeries ℂ ℂ (1 : ℂ)).fslope.fslope)
      (0 : ℂ) := by
  simpa [expDivSlope] using expDiv_hasFPowerSeriesAt_zero.has_fpower_series_dslope_fslope

lemma expDivSlope_analyticAt_zero : AnalyticAt ℂ expDivSlope (0 : ℂ) :=
  expDivSlope_hasFPowerSeriesAt_zero.analyticAt

lemma expDivSlope_of_ne {z : ℂ} (hz : z ≠ 0) :
    expDivSlope z = z⁻¹ * (expDiv z - 1) := by
  rw [expDivSlope, dslope_of_ne expDiv hz]
  simp [slope_def_module, expDiv_zero, smul_eq_mul]

lemma expDivSlope_analyticAt_of_ne {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ expDivSlope z := by
  have hmodel : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * (expDiv w - 1)) z :=
    (analyticAt_id.inv hz).mul
      ((expDiv_analyticAt z).sub
        (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne expDiv hz).mono fun w hw => by
    simpa [expDivSlope, slope_def_module, expDiv_zero, smul_eq_mul] using hw.symm

lemma expDivSlope_analyticAt (z : ℂ) : AnalyticAt ℂ expDivSlope z := by
  by_cases hz : z = 0
  · simpa [hz] using expDivSlope_analyticAt_zero
  · exact expDivSlope_analyticAt_of_ne hz

lemma exp_rho : Complex.exp rho = 2 := by
  rw [rho, ← Complex.ofReal_exp]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

lemma eq_rho_of_exp_eq_two_of_norm_le_two {z : ℂ}
    (hz_norm : ‖z‖ ≤ 2) (hz_exp : Complex.exp z = 2) :
    z = rho := by
  have hz_exp_rho : Complex.exp z = Complex.exp rho := by
    simpa [exp_rho] using hz_exp
  rcases (Complex.exp_eq_exp_iff_exists_int).mp hz_exp_rho with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · simpa [hk0] using hk
  · exfalso
    have hz_im : z.im = (k : ℝ) * (2 * Real.pi) := by
      calc
        z.im = (rho + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [hk]
        _ = rho.im + ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [Complex.add_im]
        _ = 0 + ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
          rw [rho_im]
        _ = (k : ℝ) * (2 * Real.pi) := by
          simp [Complex.mul_im]
    have him_le_norm : |(k : ℝ) * (2 * Real.pi)| ≤ ‖z‖ := by
      rw [← hz_im]
      exact Complex.abs_im_le_norm z
    have hkabs_int : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
      exact_mod_cast hkabs_int
    have htwopi_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
    have htwopi_le : 2 * Real.pi ≤ |(k : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_nonneg htwopi_nonneg]
      nlinarith [hkabs, Real.two_pi_pos]
    have htwo_lt_twopi : (2 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    linarith

lemma expDiv_ne_zero_on_closedBall_two {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
    expDiv (z - rho) ≠ 0 := by
  intro hzero
  by_cases hw : z - rho = 0
  · have hval : expDiv (z - rho) = 1 := by simpa [hw] using expDiv_zero
    rw [hval] at hzero
    exact one_ne_zero hzero
  · have hexpw : Complex.exp (z - rho) = 1 := by
      have hdiv := hzero
      rw [expDiv_of_ne hw] at hdiv
      have hsub : Complex.exp (z - rho) - 1 = 0 :=
        (mul_eq_zero.mp hdiv).resolve_left (inv_ne_zero hw)
      exact sub_eq_zero.mp hsub
    have hz_exp : Complex.exp z = 2 := by
      have hzsplit : z = rho + (z - rho) := by abel
      rw [hzsplit, Complex.exp_add, exp_rho, hexpw]
      norm_num
    have hz_norm : ‖z‖ ≤ 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hzrho := eq_rho_of_exp_eq_two_of_norm_le_two hz_norm hz_exp
    exact hw (by simp [hzrho])

lemma analyticRemainderFun_analyticAt_on_closedBall_two {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 2) :
    AnalyticAt ℂ analyticRemainderFun z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w - rho) z :=
    analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))
  have hnum : AnalyticAt ℂ (fun w : ℂ => expDivSlope (w - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := expDivSlope) (f := fun w : ℂ => w - rho)
      (x := z) (expDivSlope_analyticAt (z - rho)) hshift
  have hden : AnalyticAt ℂ (fun w : ℂ => expDiv (w - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := expDiv) (f := fun w : ℂ => w - rho)
      (x := z) (expDiv_analyticAt (z - rho)) hshift
  have hquot : AnalyticAt ℂ
      (fun w : ℂ => expDivSlope (w - rho) / expDiv (w - rho)) z :=
    hnum.div hden (expDiv_ne_zero_on_closedBall_two hz)
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) z :=
    analyticAt_const (𝕜 := ℂ) (v := (1 / 2 : ℂ)) (x := z)
  change AnalyticAt ℂ
    (fun w : ℂ => (1 / 2 : ℂ) * (expDivSlope (w - rho) / expDiv (w - rho))) z
  simpa only [Pi.mul_apply] using hconst.mul hquot

theorem analyticRemainderFun_differentiableOn_closedBall_two :
    DifferentiableOn ℂ analyticRemainderFun (Metric.closedBall (0 : ℂ) 2) := by
  intro z hz
  exact (analyticRemainderFun_analyticAt_on_closedBall_two hz).differentiableAt.differentiableWithinAt

lemma analyticRemainderFun_eq_surj_sub_principal {z : ℂ}
    (hz : z - rho ≠ 0) (hdiv : expDiv (z - rho) ≠ 0) :
    analyticRemainderFun z = surjAnalyticFun z - principalAnalyticFun z := by
  have h_exp_sub_ne : Complex.exp (z - rho) - 1 ≠ 0 := by
    intro h
    apply hdiv
    rw [expDiv_of_ne hz, h]
    simp
  have h_one_sub_exp_ne : 1 - Complex.exp (z - rho) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using neg_ne_zero.mpr h_exp_sub_ne
  have h_surj_den_ne : 2 - 2 * Complex.exp (z - rho) ≠ 0 := by
    intro h
    have hfactor : (2 : ℂ) * (1 - Complex.exp (z - rho)) = 0 := by
      simpa [mul_sub] using h
    rcases mul_eq_zero.mp hfactor with htwo | hone
    · exact (by norm_num : (2 : ℂ) ≠ 0) htwo
    · exact h_one_sub_exp_ne hone
  have h_rho_sub_ne : rho - z ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm] using neg_ne_zero.mpr hz
  have h_exp : Complex.exp z = 2 * Complex.exp (z - rho) := by
    have hzsplit : z = rho + (z - rho) := by abel
    calc
      Complex.exp z = Complex.exp (rho + (z - rho)) := congrArg Complex.exp hzsplit
      _ = Complex.exp rho * Complex.exp (z - rho) := by rw [Complex.exp_add]
      _ = 2 * Complex.exp (z - rho) := by rw [exp_rho]
  rw [analyticRemainderFun, surjAnalyticFun, principalAnalyticFun]
  rw [expDivSlope_of_ne hz, expDiv_of_ne hz, h_exp]
  field_simp [hz, hdiv, h_exp_sub_ne, h_one_sub_exp_ne, h_surj_den_ne, h_rho_sub_ne]
  ring

theorem analyticRemainderFun_eventually_eq_surj_sub_principal :
    (fun z : ℂ => surjAnalyticFun z - principalAnalyticFun z)
      =ᶠ[𝓝 (0 : ℂ)] analyticRemainderFun := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rho_norm_pos] with z hz
  have hz_norm : ‖z‖ < ‖rho‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_closed_two : z ∈ Metric.closedBall (0 : ℂ) 2 := by
    have hz_two : ‖z‖ ≤ 2 := by
      have hlt_one : ‖z‖ < 1 := hz_norm.trans rho_norm_lt_one
      linarith
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_two
  have hz_ne : z - rho ≠ 0 := by
    intro h
    have hzrho : z = rho := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖rho‖ := by rw [hzrho]
    linarith
  exact (analyticRemainderFun_eq_surj_sub_principal hz_ne
    (expDiv_ne_zero_on_closedBall_two hz_closed_two)).symm

lemma toFMLS_remainder :
    PowerSeries.toFMLS remainder =
      PowerSeries.toFMLS surjEGFℂ - PowerSeries.toFMLS principal := by
  rw [remainder, toFMLS_sub]

theorem analyticRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt analyticRemainderFun (PowerSeries.toFMLS remainder) (0 : ℂ) := by
  have hsub := surjAnalyticFun_hasFPowerSeriesAt_zero.sub
    principalAnalyticFun_hasFPowerSeriesAt_zero
  have hsub' : HasFPowerSeriesAt
      (fun z : ℂ => surjAnalyticFun z - principalAnalyticFun z)
      (PowerSeries.toFMLS remainder) (0 : ℂ) := by
    simpa [toFMLS_remainder] using hsub
  exact hsub'.congr analyticRemainderFun_eventually_eq_surj_sub_principal

theorem remainder_radius_gt_one :
    ENNReal.ofReal (1 : ℝ) < (PowerSeries.toFMLS remainder).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS remainder
  have hcoeffO :
      (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) :=
    coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
      (g := analyticRemainderFun) (p := p) (R := 2)
      (by norm_num) analyticRemainderFun_hasFPowerSeriesAt_zero
      analyticRemainderFun_differentiableOn_closedBall_two
  have hcancel :
      (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hpow : ((2 : ℝ)⁻¹ ^ n) * (2 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hpow]
    norm_num
  have hcoeffMul :
      (fun n : ℕ => ‖p.coeff n‖ * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact (hcoeffO.mul (isBigO_refl (fun n : ℕ => (2 : ℝ) ^ n) atTop)).trans hcancel
  have hnorm_eq :
      (fun n : ℕ => ‖p n‖ * (2 : ℝ) ^ n) =ᶠ[atTop]
        (fun n : ℕ => ‖p.coeff n‖ * (2 : ℝ) ^ n) := by
    exact Eventually.of_forall fun n => by
      have hpn : ‖p n‖ = ‖p.coeff n‖ := by
        simp [p, PowerSeries.toFMLS]
      change ‖p n‖ * (2 : ℝ) ^ n = ‖p.coeff n‖ * (2 : ℝ) ^ n
      rw [hpn]
  have hterm :
      (fun n : ℕ => ‖p n‖ * (2 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hnorm_eq.trans_isBigO hcoeffMul
  have hle : ((2 : ℝ≥0) : ℝ≥0∞) ≤ p.radius :=
    p.le_radius_of_isBigO (r := (2 : ℝ≥0)) hterm
  have hone_two : ENNReal.ofReal (1 : ℝ) < ((2 : ℝ≥0) : ℝ≥0∞) := by
    norm_num
  exact hone_two.trans_le hle

theorem coeff_surjEGFℂ_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ)
      ~[atTop] (fun n : ℕ => (1 : ℂ) / (2 * rho ^ (n + 1))) := by
  have hmain := coeff_surjEGFℂ_isEquivalent_of_remainder_radius remainder_radius_gt_one
  refine hmain.trans_eventuallyEq (Eventually.of_forall fun n => ?_)
  calc
    (1 / 2 : ℂ) * rho⁻¹ ^ (n + 1) =
        (1 / 2 : ℂ) * (rho ^ (n + 1))⁻¹ := by
      rw [inv_pow]
    _ = (1 : ℂ) / (2 * rho ^ (n + 1)) := by
      change (1 : ℂ) * 2⁻¹ * (rho ^ (n + 1))⁻¹ =
        (1 : ℂ) * (2 * rho ^ (n + 1))⁻¹
      rw [mul_inv_rev]
      ring

def surjectionsCount (n : ℕ) : ℕ :=
  CombClass.posInt.lseq.counts n

theorem surjectionsCount_div_factorial_isEquivalent :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((surjectionsCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop]
    (fun n : ℕ => (1 : ℂ) / (2 * (((Real.log 2 : ℝ) : ℂ) ^ (n + 1)))) := by
  have hbridge :
      (fun n : ℕ =>
        algebraMap ℚ ℂ ((surjectionsCount n : ℚ) / (n.factorial : ℚ)))
        =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n surjEGFℂ) := by
    exact Eventually.of_forall fun n => by
      change algebraMap ℚ ℂ
          ((CombClass.posInt.lseq.counts n : ℚ) / (n.factorial : ℚ)) =
        PowerSeries.coeff (R := ℂ) n surjEGFℂ
      rw [surjEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
  exact hbridge.trans_isEquivalent (by simpa [rho] using coeff_surjEGFℂ_isEquivalent)

end Surjections
end Meromorphic
end Ch5
end AnalyticCombinatorics
