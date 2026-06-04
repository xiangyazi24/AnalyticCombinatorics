import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch2.EGF.LabelledCyc
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Alignments

open AnalyticCombinatorics.Ch1

/-- The genuine labelled class of alignments: `SEQ(CYC(Z))`. -/
def alignmentClass : CombClass :=
  CombClass.atom.lcyc.lseq

/-- The alignment numbers `o_n`. This is a genuine labelled combinatorial definition. -/
def alignmentCount (n : ℕ) : ℕ :=
  alignmentClass.counts n

/-- The real dominant singularity `rho = 1 - 1 / e`. -/
def rhoReal : ℝ :=
  1 - (Real.exp 1)⁻¹

/-- The dominant singularity as a complex number. -/
def rho : ℂ :=
  (rhoReal : ℂ)

/-- The simple-pole numerator `c = 1 / L'(rho) = 1 / e`, for
`1 / (1 - L(z)) ~ c / (rho - z)`. -/
def poleNumerator : ℂ :=
  (((Real.exp 1)⁻¹ : ℝ) : ℂ)

/-- The coefficient-asymptotic constant in the normalization
`[z^n] O(z) ~ C * rho^{-n}`. -/
def alignmentConstant : ℂ :=
  ((((Real.exp 1 - 1)⁻¹ : ℝ)) : ℂ)

/-- The formal power series for `log (1 / (1 - z))`, with zero constant term. -/
def cycleEGFℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n : ℕ => ((n : ℂ)⁻¹)

/-- The same formal logarithm over `ℚ`, used to identify the genuine `CYC(Z)` EGF. -/
def cycleEGFℚ : PowerSeries ℚ :=
  PowerSeries.mk fun n : ℕ => ((n : ℚ)⁻¹)

/-- The complex EGF of the genuine alignment class. -/
def alignmentEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ alignmentClass.egf

/-- The dominant simple-pole principal part. -/
def principal : PowerSeries ℂ :=
  PowerSeries.C (poleNumerator * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic remainder after removing the dominant pole. -/
def remainder : PowerSeries ℂ :=
  alignmentEGFℂ - principal

/-- Analytic representative of the labelled-cycle EGF `log (1 / (1 - z))`
on the principal branch. -/
def cycleAnalyticFun (z : ℂ) : ℂ :=
  -Complex.log (1 - z)

/-- Analytic representative of the alignment EGF away from the zeros of
`1 - cycleAnalyticFun`. -/
def alignmentAnalyticFun (z : ℂ) : ℂ :=
  (1 - cycleAnalyticFun z)⁻¹

/-- Analytic representative of the dominant principal part. -/
def principalAnalyticFun (z : ℂ) : ℂ :=
  poleNumerator * (rho - z)⁻¹

/-- The shifted cycle EGF `w ↦ L(rho + w)`. -/
def shiftedCycleAnalyticFun (w : ℂ) : ℂ :=
  cycleAnalyticFun (rho + w)

/-- The divided difference `(L(rho+w)-L(rho))/w`, extended at `w=0` by the derivative. -/
def cycleDiv (w : ℂ) : ℂ :=
  dslope shiftedCycleAnalyticFun 0 w

/-- The divided difference `(cycleDiv w - cycleDiv 0)/w`, again extended at `0`. -/
def cycleDivSlope (w : ℂ) : ℂ :=
  dslope cycleDiv 0 w

/-- The removable analytic continuation of `alignmentAnalyticFun - principalAnalyticFun`
across `z = rho`. -/
def analyticRemainderFun (z : ℂ) : ℂ :=
  cycleDivSlope (z - rho) / (((Real.exp 1 : ℝ) : ℂ) * cycleDiv (z - rho))

lemma coeff_cycleEGFℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n cycleEGFℂ = ((n : ℂ)⁻¹) := by
  simp [cycleEGFℂ]

lemma coeff_cycleEGFℚ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n cycleEGFℚ = ((n : ℚ)⁻¹) := by
  simp [cycleEGFℚ]

lemma cycleEGFℂ_constantCoeff :
    PowerSeries.constantCoeff cycleEGFℂ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_cycleEGFℂ]
  simp

lemma cycleEGFℚ_constantCoeff :
    PowerSeries.constantCoeff cycleEGFℚ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_cycleEGFℚ]
  simp

lemma cycleAnalyticFun_zero : cycleAnalyticFun 0 = 0 := by
  simp [cycleAnalyticFun]

theorem cycleAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt cycleAnalyticFun (PowerSeries.toFMLS cycleEGFℂ) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  simpa [cycleAnalyticFun, coeff_cycleEGFℂ, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    Complex.hasSum_taylorSeries_neg_log hz_norm

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

lemma real_exp_one_pos : 0 < Real.exp 1 :=
  Real.exp_pos 1

lemma real_one_lt_exp_one : 1 < Real.exp 1 := by
  exact Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)

lemma rhoReal_pos : 0 < rhoReal := by
  rw [rhoReal]
  have hlt : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ real_one_lt_exp_one
  linarith

lemma rhoReal_lt_three_fourths : rhoReal < (3 / 4 : ℝ) := by
  rw [rhoReal]
  have hlt : (1 / 4 : ℝ) < (Real.exp 1)⁻¹ := by
    simpa [one_div] using
      one_div_lt_one_div_of_lt real_exp_one_pos
        (lt_trans Real.exp_one_lt_three (by norm_num : (3 : ℝ) < 4))
  linarith

lemma rho_norm : ‖rho‖ = rhoReal := by
  rw [rho]
  exact Complex.norm_of_nonneg rhoReal_pos.le

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact rhoReal_pos

lemma rho_norm_lt_three_fourths : ‖rho‖ < (3 / 4 : ℝ) := by
  rw [rho_norm]
  exact rhoReal_lt_three_fourths

lemma rho_ne_zero : rho ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)

lemma poleNumerator_ne_zero : poleNumerator ≠ 0 := by
  rw [poleNumerator]
  exact_mod_cast inv_ne_zero (ne_of_gt real_exp_one_pos)

lemma alignmentConstant_eq_poleNumerator_div_rho :
    alignmentConstant = poleNumerator * rho⁻¹ := by
  rw [alignmentConstant, poleNumerator, rho, rhoReal]
  norm_num [Complex.ofReal_inv]
  field_simp [ne_of_gt real_exp_one_pos, ne_of_gt rhoReal_pos]

lemma rho_norm_lt_one : ‖rho‖ < 1 := by
  exact rho_norm_lt_three_fourths.trans (by norm_num : (3 / 4 : ℝ) < 1)

lemma rho_norm_lt_four_fifths : ‖rho‖ < (4 / 5 : ℝ) :=
  rho_norm_lt_three_fourths.trans (by norm_num : (3 / 4 : ℝ) < 4 / 5)

lemma expOneℂ_ne_zero : (((Real.exp 1 : ℝ) : ℂ) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt real_exp_one_pos

lemma poleNumerator_eq_expOneℂ_inv :
    poleNumerator = ((((Real.exp 1 : ℝ) : ℂ) : ℂ)⁻¹) := by
  rw [poleNumerator]
  norm_num [Complex.ofReal_inv]

lemma one_sub_mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [sub_eq_add_neg]
  exact Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz)

lemma one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hz)

lemma cycleAnalyticFun_hasDerivAt_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt cycleAnalyticFun (1 - z)⁻¹ z := by
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z :=
    (hasDerivAt_id z).const_sub 1
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (1 - w))
      ((-1 : ℂ) / (1 - z)) z :=
    hsub.clog (one_sub_mem_slitPlane_of_norm_lt_one hz)
  have hneg := hlog.neg
  convert hneg using 1
  · field_simp [one_sub_ne_zero_of_norm_lt_one hz]

lemma cycleAnalyticFun_differentiableOn_ball_one :
    DifferentiableOn ℂ cycleAnalyticFun (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  exact (cycleAnalyticFun_hasDerivAt_of_norm_lt_one hz_norm).differentiableAt.differentiableWithinAt

lemma cycleAnalyticFun_analyticAt_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ cycleAnalyticFun z :=
  cycleAnalyticFun_differentiableOn_ball_one.analyticAt
    (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hz))

lemma one_sub_rho : 1 - rho = poleNumerator := by
  rw [rho, rhoReal, poleNumerator]
  norm_num [Complex.ofReal_inv]

lemma inv_one_sub_rho : (1 - rho)⁻¹ = (((Real.exp 1) : ℝ) : ℂ) := by
  rw [one_sub_rho, poleNumerator]
  norm_num [Complex.ofReal_inv]

lemma cycleAnalyticFun_rho : cycleAnalyticFun rho = 1 := by
  rw [cycleAnalyticFun, one_sub_rho, poleNumerator]
  rw [← Complex.ofReal_log (inv_nonneg.mpr real_exp_one_pos.le)]
  rw [Real.log_inv, Real.log_exp]
  norm_num

lemma shiftedCycleAnalyticFun_hasDerivAt_zero :
    HasDerivAt shiftedCycleAnalyticFun (((Real.exp 1 : ℝ) : ℂ)) (0 : ℂ) := by
  have h := cycleAnalyticFun_hasDerivAt_of_norm_lt_one rho_norm_lt_one
  have h' : HasDerivAt cycleAnalyticFun (1 - rho)⁻¹ (rho + 0) := by
    simpa using h
  have hshift := h'.comp_const_add rho (0 : ℂ)
  simpa [shiftedCycleAnalyticFun, inv_one_sub_rho] using hshift

lemma cycleDiv_zero : cycleDiv 0 = (((Real.exp 1 : ℝ) : ℂ) : ℂ) := by
  rw [cycleDiv, dslope_same]
  exact shiftedCycleAnalyticFun_hasDerivAt_zero.deriv

lemma shiftedCycleAnalyticFun_analyticAt_zero :
    AnalyticAt ℂ shiftedCycleAnalyticFun (0 : ℂ) := by
  rcases cycleAnalyticFun_analyticAt_of_norm_lt_one rho_norm_lt_one with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hp' : HasFPowerSeriesAt (fun z : ℂ => cycleAnalyticFun (z + rho)) p (0 : ℂ) := by
    simpa using hp.comp_sub (-rho)
  exact hp'.congr (Eventually.of_forall fun z => by
    simp [shiftedCycleAnalyticFun, add_comm])

lemma cycleDiv_hasFPowerSeriesAt_zero :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt cycleDiv p (0 : ℂ) := by
  rcases shiftedCycleAnalyticFun_analyticAt_zero with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cycleDiv] using hp.has_fpower_series_dslope_fslope⟩

lemma cycleDiv_analyticAt_zero : AnalyticAt ℂ cycleDiv (0 : ℂ) :=
  cycleDiv_hasFPowerSeriesAt_zero

lemma cycleDiv_of_ne {w : ℂ} (hw : w ≠ 0) :
    cycleDiv w = w⁻¹ * (cycleAnalyticFun (rho + w) - 1) := by
  rw [cycleDiv, dslope_of_ne shiftedCycleAnalyticFun hw]
  simp [shiftedCycleAnalyticFun, cycleAnalyticFun_rho, slope_def_module, smul_eq_mul]

lemma cycleDiv_analyticAt_of_ne {w : ℂ} (hw : w ≠ 0)
    (hw_norm : ‖rho + w‖ < 1) :
    AnalyticAt ℂ cycleDiv w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (cycleAnalyticFun (rho + u) - 1)) w := by
    have hshift : AnalyticAt ℂ (fun u : ℂ => rho + u) w :=
      analyticAt_const.add analyticAt_id
    have hcycle : AnalyticAt ℂ (fun u : ℂ => cycleAnalyticFun (rho + u)) w :=
      AnalyticAt.comp' (𝕜 := ℂ) (g := cycleAnalyticFun) (f := fun u : ℂ => rho + u)
        (x := w) (cycleAnalyticFun_analyticAt_of_norm_lt_one hw_norm) hshift
    exact (analyticAt_id.inv hw).mul
      (hcycle.sub (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne shiftedCycleAnalyticFun hw).mono fun u hu => by
    simpa [cycleDiv, shiftedCycleAnalyticFun, cycleAnalyticFun_rho, slope_def_module,
      smul_eq_mul] using hu.symm

lemma cycleDiv_analyticAt_of_shift_norm_lt_one {w : ℂ} (hw_norm : ‖rho + w‖ < 1) :
    AnalyticAt ℂ cycleDiv w := by
  by_cases hw : w = 0
  · simpa [hw] using cycleDiv_analyticAt_zero
  · exact cycleDiv_analyticAt_of_ne hw hw_norm

lemma cycleDivSlope_hasFPowerSeriesAt_zero :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt cycleDivSlope p (0 : ℂ) := by
  rcases cycleDiv_hasFPowerSeriesAt_zero with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa [cycleDivSlope] using hp.has_fpower_series_dslope_fslope⟩

lemma cycleDivSlope_analyticAt_zero : AnalyticAt ℂ cycleDivSlope (0 : ℂ) :=
  cycleDivSlope_hasFPowerSeriesAt_zero

lemma cycleDivSlope_of_ne {w : ℂ} (hw : w ≠ 0) :
    cycleDivSlope w = w⁻¹ * (cycleDiv w - (((Real.exp 1 : ℝ) : ℂ))) := by
  rw [cycleDivSlope, dslope_of_ne cycleDiv hw]
  simp [cycleDiv_zero, slope_def_module, smul_eq_mul]

lemma cycleDivSlope_analyticAt_of_ne {w : ℂ} (hw : w ≠ 0)
    (hw_norm : ‖rho + w‖ < 1) :
    AnalyticAt ℂ cycleDivSlope w := by
  have hmodel : AnalyticAt ℂ
      (fun u : ℂ => u⁻¹ * (cycleDiv u - (((Real.exp 1 : ℝ) : ℂ)))) w := by
    exact (analyticAt_id.inv hw).mul
      ((cycleDiv_analyticAt_of_shift_norm_lt_one hw_norm).sub
        (analyticAt_const (𝕜 := ℂ) (v := (((Real.exp 1 : ℝ) : ℂ)) ) (x := w)))
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne cycleDiv hw).mono fun u hu => by
    simpa [cycleDivSlope, cycleDiv_zero, slope_def_module, smul_eq_mul] using hu.symm

lemma cycleDivSlope_analyticAt_of_shift_norm_lt_one {w : ℂ}
    (hw_norm : ‖rho + w‖ < 1) :
    AnalyticAt ℂ cycleDivSlope w := by
  by_cases hw : w = 0
  · simpa [hw] using cycleDivSlope_analyticAt_zero
  · exact cycleDivSlope_analyticAt_of_ne hw hw_norm

lemma exp_cycleAnalyticFun_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.exp (cycleAnalyticFun z) = (1 - z)⁻¹ := by
  rw [cycleAnalyticFun, Complex.exp_neg]
  rw [Complex.exp_log (one_sub_ne_zero_of_norm_lt_one hz)]

lemma cycleDiv_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    cycleDiv (z - rho) ≠ 0 := by
  intro hzero
  by_cases hw : z - rho = 0
  · have hval : cycleDiv (z - rho) = (((Real.exp 1 : ℝ) : ℂ) : ℂ) := by
      simpa [hw] using cycleDiv_zero
    rw [hval] at hzero
    exact expOneℂ_ne_zero hzero
  · have hdiv := cycleDiv_of_ne (w := z - rho) hw
    have hdiv' : (z - rho)⁻¹ * (cycleAnalyticFun z - 1) = 0 := by
      have hdiv0 := hdiv
      rw [hzero] at hdiv0
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiv0.symm
    have hLminus : cycleAnalyticFun z - 1 = 0 :=
      (mul_eq_zero.mp hdiv').resolve_left (inv_ne_zero hw)
    have hL : cycleAnalyticFun z = 1 := sub_eq_zero.mp hLminus
    have hinv : (1 - z)⁻¹ = (((Real.exp 1 : ℝ) : ℂ) : ℂ) := by
      calc
        (1 - z)⁻¹ = Complex.exp (cycleAnalyticFun z) := by
          rw [exp_cycleAnalyticFun_of_norm_lt_one hz]
        _ = Complex.exp (1 : ℂ) := by rw [hL]
        _ = (((Real.exp 1 : ℝ) : ℂ) : ℂ) := by
          exact (Complex.ofReal_exp 1).symm
    have hbase := congrArg Inv.inv hinv
    rw [inv_inv] at hbase
    have hbase' : 1 - z = poleNumerator := by
      simpa [poleNumerator_eq_expOneℂ_inv] using hbase
    have hzrho : z = rho := by
      calc
        z = 1 - (1 - z) := by ring
        _ = 1 - poleNumerator := by rw [hbase']
        _ = rho := by
          rw [← one_sub_rho]
          ring
    exact hw (by simp [hzrho])

lemma analyticRemainderFun_eq_alignment_sub_principal {z : ℂ}
    (hw : z - rho ≠ 0) (hdiv : cycleDiv (z - rho) ≠ 0) :
    analyticRemainderFun z = alignmentAnalyticFun z - principalAnalyticFun z := by
  let w : ℂ := z - rho
  let S : ℂ := cycleDiv (z - rho)
  let E : ℂ := (((Real.exp 1 : ℝ) : ℂ) : ℂ)
  have hw' : w ≠ 0 := by simpa [w] using hw
  have hS : S ≠ 0 := by simpa [S] using hdiv
  have hE : E ≠ 0 := by
    exact expOneℂ_ne_zero
  have hcycleDiv :
      cycleDiv (z - rho) = (z - rho)⁻¹ * (cycleAnalyticFun z - 1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      cycleDiv_of_ne (w := z - rho) hw
  have hcycle :
      cycleAnalyticFun z = 1 + w * S := by
    change cycleAnalyticFun z = 1 + (z - rho) * cycleDiv (z - rho)
    rw [hcycleDiv]
    field_simp [hw]
    ring
  rw [analyticRemainderFun, alignmentAnalyticFun, principalAnalyticFun,
    cycleDivSlope_of_ne hw, hcycle, poleNumerator_eq_expOneℂ_inv]
  have hrz : rho - z = -w := by
    dsimp [w]
    ring
  rw [hrz]
  dsimp [w, S, E]
  field_simp [hw, hdiv, expOneℂ_ne_zero]
  ring

lemma analyticRemainderFun_analyticAt_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ analyticRemainderFun z := by
  have hshift : AnalyticAt ℂ (fun y : ℂ => y - rho) z :=
    analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))
  have hw_norm : ‖rho + (z - rho)‖ < 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
  have hnum : AnalyticAt ℂ (fun y : ℂ => cycleDivSlope (y - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cycleDivSlope) (f := fun y : ℂ => y - rho)
      (x := z) (cycleDivSlope_analyticAt_of_shift_norm_lt_one hw_norm) hshift
  have hden0 : AnalyticAt ℂ (fun y : ℂ => cycleDiv (y - rho)) z :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := cycleDiv) (f := fun y : ℂ => y - rho)
      (x := z) (cycleDiv_analyticAt_of_shift_norm_lt_one hw_norm) hshift
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (((Real.exp 1 : ℝ) : ℂ) : ℂ)) z :=
    analyticAt_const (𝕜 := ℂ) (v := (((Real.exp 1 : ℝ) : ℂ) : ℂ)) (x := z)
  have hden : AnalyticAt ℂ
      (fun y : ℂ => (((Real.exp 1 : ℝ) : ℂ) : ℂ) * cycleDiv (y - rho)) z :=
    hconst.mul hden0
  have hden_ne :
      (((Real.exp 1 : ℝ) : ℂ) : ℂ) * cycleDiv (z - rho) ≠ 0 :=
    mul_ne_zero expOneℂ_ne_zero (cycleDiv_ne_zero_of_norm_lt_one hz)
  change AnalyticAt ℂ
    (fun y : ℂ => cycleDivSlope (y - rho) /
      ((((Real.exp 1 : ℝ) : ℂ) : ℂ) * cycleDiv (y - rho))) z
  exact hnum.div hden hden_ne

theorem analyticRemainderFun_differentiableOn_closedBall_four_fifths :
    DifferentiableOn ℂ analyticRemainderFun (Metric.closedBall (0 : ℂ) (4 / 5 : ℝ)) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by
    have hz_le : ‖z‖ ≤ (4 / 5 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact hz_le.trans_lt (by norm_num : (4 / 5 : ℝ) < 1)
  exact (analyticRemainderFun_analyticAt_of_norm_lt_one hz_norm).differentiableAt.differentiableWithinAt

theorem analyticRemainderFun_eventually_eq_alignment_sub_principal :
    (fun z : ℂ => alignmentAnalyticFun z - principalAnalyticFun z)
      =ᶠ[𝓝 (0 : ℂ)] analyticRemainderFun := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) rho_norm_pos] with z hz
  have hz_norm : ‖z‖ < ‖rho‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_lt_one : ‖z‖ < 1 := hz_norm.trans rho_norm_lt_one
  have hw : z - rho ≠ 0 := by
    intro h
    have hzrho : z = rho := sub_eq_zero.mp h
    have hnorm : ‖z‖ = ‖rho‖ := by rw [hzrho]
    linarith
  exact (analyticRemainderFun_eq_alignment_sub_principal hw
    (cycleDiv_ne_zero_of_norm_lt_one hz_lt_one)).symm

lemma atom_counts_zero : CombClass.atom.counts 0 = 0 := by
  simp [CombClass.counts_atom]

theorem egf_atom : CombClass.atom.egf = (PowerSeries.X : PowerSeries ℚ) := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_atom]
  by_cases h1 : n = 1
  · subst n
    simp
  · have hcoeffX : PowerSeries.coeff (R := ℚ) n PowerSeries.X = 0 := by
      rw [PowerSeries.coeff_X]
      simp [h1]
    rw [if_neg h1, hcoeffX]
    simp

lemma cycleClass_counts_zero : CombClass.atom.lcyc.counts 0 = 0 := by
  simp [CombClass.counts, CombClass.lcyc]

lemma atom_lseq_egf_eq_geometric :
    CombClass.atom.lseq.egf = PowerSeries.invUnitsSub (1 : ℚˣ) := by
  have hmul := CombClass.egf_lseq CombClass.atom atom_counts_zero
  rw [egf_atom] at hmul
  have h0 : PowerSeries.constantCoeff (1 - (PowerSeries.X : PowerSeries ℚ)) ≠ 0 := by
    simp
  have hseq : CombClass.atom.lseq.egf = (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one h0).2 hmul
  have hgeom :
      PowerSeries.invUnitsSub (1 : ℚˣ) = (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one h0).2 (by
    simpa only [Units.val_one] using
      (PowerSeries.invUnitsSub_mul_sub (u := (1 : ℚˣ))))
  exact hseq.trans hgeom.symm

lemma derivative_cycleEGFℚ :
    d⁄dX ℚ cycleEGFℚ = PowerSeries.invUnitsSub (1 : ℚˣ) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_cycleEGFℚ, PowerSeries.coeff_invUnitsSub]
  simp [Nat.cast_add, Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

theorem atom_lcyc_egf_eq_cycleEGFℚ :
    CombClass.atom.lcyc.egf = cycleEGFℚ := by
  have hF' :
      d⁄dX ℚ cycleEGFℚ =
        d⁄dX ℚ CombClass.atom.egf * CombClass.atom.lseq.egf := by
    rw [derivative_cycleEGFℚ, egf_atom, PowerSeries.derivative_X, one_mul,
      atom_lseq_egf_eq_geometric]
  have hF0 : PowerSeries.constantCoeff cycleEGFℚ = 0 :=
    cycleEGFℚ_constantCoeff
  exact (CombClass.egf_lcyc_unique CombClass.atom atom_counts_zero hF' hF0).symm

theorem map_cycleEGFℚ :
    PowerSeries.mapℂ cycleEGFℚ = cycleEGFℂ := by
  ext n
  rw [PowerSeries.coeff_mapℂ, coeff_cycleEGFℚ, coeff_cycleEGFℂ]
  norm_num

theorem alignmentEGFℂ_mul_denominator :
    alignmentEGFℂ * (1 - cycleEGFℂ) = 1 := by
  have h := congrArg PowerSeries.mapℂ
    (CombClass.egf_lseq CombClass.atom.lcyc cycleClass_counts_zero)
  rw [atom_lcyc_egf_eq_cycleEGFℚ] at h
  simp only [map_mul, map_sub, map_one, map_cycleEGFℚ] at h
  simpa [alignmentClass, alignmentEGFℂ] using h

theorem alignmentEGFℂ_eq_inv_denominator :
    alignmentEGFℂ = (1 - cycleEGFℂ)⁻¹ := by
  have h0 : PowerSeries.constantCoeff (1 - cycleEGFℂ : PowerSeries ℂ) ≠ 0 := by
    rw [map_sub, PowerSeries.constantCoeff_one, cycleEGFℂ_constantCoeff]
    norm_num
  exact (PowerSeries.eq_inv_iff_mul_eq_one h0).2 alignmentEGFℂ_mul_denominator

theorem alignmentEGFℂ_eq_geometric_subst :
    alignmentEGFℂ =
      (PowerSeries.invUnitsSub (1 : ℂˣ)).subst cycleEGFℂ := by
  let H : PowerSeries ℂ := cycleEGFℂ
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    simpa [H] using cycleEGFℂ_constantCoeff
  have hHas : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
  have hsubst : (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H * (1 - H) = 1 := by
    have hsubHX :
        (PowerSeries.C ((1 : ℂˣ) : ℂ) - PowerSeries.X).subst H = 1 - H := by
      rw [PowerSeries.subst_sub hHas, PowerSeries.subst_C, PowerSeries.subst_X hHas]
      simp
    rw [← hsubHX, ← PowerSeries.subst_mul hHas, PowerSeries.invUnitsSub_mul_sub]
    change (PowerSeries.C (1 : ℂ)).subst H = 1
    rw [PowerSeries.subst_C]
    simp
  rw [alignmentEGFℂ_eq_inv_denominator]
  have h0 : PowerSeries.constantCoeff (1 - H : PowerSeries ℂ) ≠ 0 := by
    simp [H, cycleEGFℂ_constantCoeff]
  exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).2 hsubst).symm

theorem alignmentAnalyticFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt alignmentAnalyticFun (PowerSeries.toFMLS alignmentEGFℂ) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (0 : ℂ) :=
    (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have houter' : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (cycleAnalyticFun 0) := by
    simpa [cycleAnalyticFun_zero] using houter
  have hcomp := houter'.comp cycleAnalyticFun_hasFPowerSeriesAt_zero
  rw [alignmentEGFℂ_eq_geometric_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp cycleEGFℂ_constantCoeff]
  rw [toFMLS_invUnitsSub_one]
  refine hcomp.congr ?_
  filter_upwards with z
  simp [alignmentAnalyticFun]

lemma coeff_principal (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n principal =
      poleNumerator * rho⁻¹ ^ (n + 1) := by
  rw [principal, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

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
      HasSum (fun n : ℕ => (poleNumerator * rho⁻¹) * (z * rho⁻¹) ^ n)
        ((poleNumerator * rho⁻¹) * (1 - z * rho⁻¹)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hzr).mul_left (poleNumerator * rho⁻¹)
  convert hsum using 1
  · ext n
    rw [PowerSeries.coeff_toFMLS, coeff_principal]
    simp [smul_eq_mul]
    rw [pow_succ, mul_pow]
    ring
  · simp [principalAnalyticFun]
    field_simp [rho_ne_zero, hlin_ne, hrz_ne]

lemma toFMLS_remainder :
    PowerSeries.toFMLS remainder =
      PowerSeries.toFMLS alignmentEGFℂ - PowerSeries.toFMLS principal := by
  rw [remainder, toFMLS_sub]

theorem analyticSubRemainder_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => alignmentAnalyticFun z - principalAnalyticFun z)
      (PowerSeries.toFMLS remainder) (0 : ℂ) := by
  have hsub := alignmentAnalyticFun_hasFPowerSeriesAt_zero.sub
    principalAnalyticFun_hasFPowerSeriesAt_zero
  simpa [toFMLS_remainder] using hsub

theorem analyticRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt analyticRemainderFun (PowerSeries.toFMLS remainder) (0 : ℂ) :=
  analyticSubRemainder_hasFPowerSeriesAt_zero.congr
    analyticRemainderFun_eventually_eq_alignment_sub_principal

theorem remainder_radius_gt_three_fourths :
    ENNReal.ofReal (3 / 4 : ℝ) < (PowerSeries.toFMLS remainder).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS remainder
  have hcoeffO :
      (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => (4 / 5 : ℝ)⁻¹ ^ n) :=
    coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
      (g := analyticRemainderFun) (p := p) (R := (4 / 5 : ℝ))
      (by norm_num) analyticRemainderFun_hasFPowerSeriesAt_zero
      analyticRemainderFun_differentiableOn_closedBall_four_fifths
  have hcancel :
      (fun n : ℕ => ((4 / 5 : ℝ)⁻¹ ^ n) * (4 / 5 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have hpow : ((4 / 5 : ℝ)⁻¹ ^ n) * (4 / 5 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hpow]
    norm_num
  have hcoeffMul :
      (fun n : ℕ => ‖p.coeff n‖ * (4 / 5 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact (hcoeffO.mul (isBigO_refl (fun n : ℕ => (4 / 5 : ℝ) ^ n) atTop)).trans
      hcancel
  have hnorm_eq :
      (fun n : ℕ => ‖p n‖ * (4 / 5 : ℝ) ^ n) =ᶠ[atTop]
        (fun n : ℕ => ‖p.coeff n‖ * (4 / 5 : ℝ) ^ n) := by
    exact Eventually.of_forall fun n => by
      have hpn : ‖p n‖ = ‖p.coeff n‖ := by
        simp [p, PowerSeries.toFMLS]
      change ‖p n‖ * (4 / 5 : ℝ) ^ n = ‖p.coeff n‖ * (4 / 5 : ℝ) ^ n
      rw [hpn]
  have hterm :
      (fun n : ℕ => ‖p n‖ * (4 / 5 : ℝ) ^ n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    hnorm_eq.trans_isBigO hcoeffMul
  have hle : (((4 / 5 : ℝ≥0) : ℝ≥0∞)) ≤ p.radius :=
    p.le_radius_of_isBigO (r := (4 / 5 : ℝ≥0)) hterm
  have hstrict : ENNReal.ofReal (3 / 4 : ℝ) < (((4 / 5 : ℝ≥0) : ℝ≥0∞)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4 / 5)).2
      (by norm_num : (3 / 4 : ℝ) < 4 / 5)
  exact hstrict.trans_le hle

lemma alignmentEGFℂ_eq_principal_add_remainder :
    alignmentEGFℂ = principal + remainder := by
  simp [remainder]

theorem coeff_alignmentEGFℂ_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (3 / 4 : ℝ) < (PowerSeries.toFMLS remainder).radius) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n alignmentEGFℂ)
      ~[atTop] (fun n : ℕ => poleNumerator * rho⁻¹ ^ (n + 1)) := by
  exact dominant_simplePole_isEquivalent
    alignmentEGFℂ remainder (ρ := rho) (c := poleNumerator) (R := (3 / 4 : ℝ))
    rho_norm_pos rho_norm_lt_three_fourths poleNumerator_ne_zero hrem
    alignmentEGFℂ_eq_principal_add_remainder

theorem coeff_alignmentEGFℂ_isEquivalent_of_remainder_radius_C
    (hrem : ENNReal.ofReal (3 / 4 : ℝ) < (PowerSeries.toFMLS remainder).radius) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n alignmentEGFℂ)
      ~[atTop] (fun n : ℕ => alignmentConstant * rho⁻¹ ^ n) := by
  have hmain := coeff_alignmentEGFℂ_isEquivalent_of_remainder_radius hrem
  refine hmain.trans_eventuallyEq (Eventually.of_forall fun n => ?_)
  rw [alignmentConstant_eq_poleNumerator_div_rho]
  change poleNumerator * rho⁻¹ ^ (n + 1) = poleNumerator * rho⁻¹ * rho⁻¹ ^ n
  rw [pow_succ]
  ring

theorem alignmentCount_div_factorial_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (3 / 4 : ℝ) < (PowerSeries.toFMLS remainder).radius) :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((alignmentCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop] (fun n : ℕ => alignmentConstant * rho⁻¹ ^ n) := by
  have hbridge :
      (fun n : ℕ =>
        algebraMap ℚ ℂ ((alignmentCount n : ℚ) / (n.factorial : ℚ)))
        =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n alignmentEGFℂ) := by
    exact Eventually.of_forall fun n => by
      simp [alignmentCount, alignmentEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
  exact hbridge.trans_isEquivalent
    (coeff_alignmentEGFℂ_isEquivalent_of_remainder_radius_C hrem)

theorem coeff_alignmentEGFℂ_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n alignmentEGFℂ)
      ~[atTop] (fun n : ℕ => alignmentConstant * rho⁻¹ ^ n) :=
  coeff_alignmentEGFℂ_isEquivalent_of_remainder_radius_C remainder_radius_gt_three_fourths

theorem alignmentCount_div_factorial_isEquivalent :
    (fun n : ℕ =>
      algebraMap ℚ ℂ ((alignmentCount n : ℚ) / (n.factorial : ℚ)))
      ~[atTop] (fun n : ℕ => alignmentConstant * rho⁻¹ ^ n) :=
  alignmentCount_div_factorial_isEquivalent_of_remainder_radius remainder_radius_gt_three_fourths

end Alignments
end Meromorphic
end Ch5
end AnalyticCombinatorics
