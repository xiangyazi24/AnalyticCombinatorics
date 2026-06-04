import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch5.Meromorphic.Alignments
import AnalyticCombinatorics.Ch5.Meromorphic.SupercriticalSeqGenuine
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Tangent

namespace PowerSeries

/-- The power series whose coefficients are the scalar coefficients of a formal multilinear
series.  This local bridge is used to package the Taylor series obtained from `AnalyticAt`. -/
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

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

lemma toFMLS_sub (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f - g) = PowerSeries.toFMLS f - PowerSeries.toFMLS g := by
  ext n
  simp [PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]

/-- The positive dominant pole radius `π / 2`. -/
def rhoReal : ℝ :=
  Real.pi / 2

/-- The positive dominant pole of `tan`. -/
def rho : ℂ :=
  (rhoReal : ℂ)

/-- A single simple-pole principal part `c / (ρ - z)`. -/
def simplePolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C (c * ρ⁻¹) *
    PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The symmetric two-pole principal part `c / (ρ - z) + c / (-ρ - z)`. -/
def twoPolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  simplePolePrincipal ρ c + simplePolePrincipal (-ρ) c

lemma coeff_simplePolePrincipal (ρ c : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (simplePolePrincipal ρ c) =
      c * ρ⁻¹ ^ (n + 1) := by
  rw [simplePolePrincipal, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

lemma coeff_twoPolePrincipal (ρ c : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (twoPolePrincipal ρ c) =
      c * ρ⁻¹ ^ (n + 1) + c * (-ρ)⁻¹ ^ (n + 1) := by
  simp [twoPolePrincipal, coeff_simplePolePrincipal]

lemma neg_inv_pow_even (ρ : ℂ) (k : ℕ) :
    (-ρ)⁻¹ ^ (2 * k + 2) = ρ⁻¹ ^ (2 * k + 2) := by
  rw [inv_neg, neg_pow]
  have hEven : Even (2 * k + 2) := by
    refine ⟨k + 1, ?_⟩
    ring
  rw [Even.neg_pow hEven]
  simp

lemma coeff_twoPolePrincipal_odd (ρ c : ℂ) (k : ℕ) :
    PowerSeries.coeff (R := ℂ) (2 * k + 1) (twoPolePrincipal ρ c) =
      2 * c * ρ⁻¹ ^ (2 * k + 2) := by
  rw [coeff_twoPolePrincipal, neg_inv_pow_even]
  ring

private lemma tendsto_two_mul_add_one_atTop :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  exact Filter.tendsto_atTop_mono
    (f := fun k : ℕ => k) (g := fun k : ℕ => 2 * k + 1)
    (fun k : ℕ => by
      calc
        k ≤ 2 * k := Nat.le_mul_of_pos_left k (by norm_num : 0 < 2)
        _ ≤ 2 * k + 1 := Nat.le_succ _)
    (tendsto_id : Tendsto (fun k : ℕ => k) atTop atTop)

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_twoPole_odd
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun k : ℕ => R⁻¹ ^ (2 * k + 1) : ℕ → ℝ) =o[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hpowLittleOdd :
      (fun k : ℕ => R⁻¹ ^ (2 * k + 1) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k + 1) : ℕ → ℝ) :=
    hpowLittle.comp_tendsto tendsto_two_mul_add_one_atTop
  have hmainO :
      (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k + 1) : ℕ → ℝ) =O[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) := by
    have hcnorm : ‖2 * c‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact mul_ne_zero (by norm_num) hc
    have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
    have hρinv : ‖ρ‖⁻¹ ≠ 0 := inv_ne_zero hρnorm
    refine isBigO_of_le' (l := atTop) (c := (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro k
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ (2 * k + 1) :=
      pow_nonneg hbase_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    have hnorm_main :
        ‖2 * c * ρ⁻¹ ^ (2 * k + 2)‖ =
          ‖2 * c‖ * ‖ρ‖⁻¹ ^ (2 * k + 2) := by
      rw [norm_mul, norm_pow, norm_inv]
    calc
      ‖ρ‖⁻¹ ^ (2 * k + 1) =
          (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            (‖2 * c‖ * (‖ρ‖⁻¹ ^ (2 * k + 2))) := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ]
        field_simp [hcnorm, hρnorm, hρinv]
        have hunit : ‖ρ‖ ^ 2 * (1 / ‖ρ‖) ^ 2 = 1 := by
          field_simp [hρnorm]
        rw [show 2 * k + 1 + 1 = 2 + 2 * k by ring, pow_add]
        rw [← mul_assoc, hunit]
        simp
      _ = (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            ‖2 * c * ρ⁻¹ ^ (2 * k + 2)‖ := by rw [hnorm_main]
  exact hpowLittleOdd.trans_isBigO hmainO

/-- Two symmetric dominant simple poles transfer, restricted to odd indices.  This is the
two-pole analogue needed for tangent numbers: the even-index cancellation is avoided by indexing
`n = 2k + 1`. -/
theorem twoDominantSimplePole_isEquivalent_odd
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = twoPolePrincipal ρ c + g) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) f) ~[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) := by
  let S : PowerSeries ℂ := twoPolePrincipal ρ c
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR (by simpa [S] using hfg)
  have hremOOdd :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) f -
        PowerSeries.coeff (R := ℂ) (2 * k + 1) S) =O[atTop]
        (fun k : ℕ => R⁻¹ ^ (2 * k + 1)) :=
    hremO.comp_tendsto tendsto_two_mul_add_one_atTop
  have hgeom :
      (fun k : ℕ => R⁻¹ ^ (2 * k + 1) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) :=
    inv_radius_pow_isLittleO_twoPole_odd hρ hρR hc
  have hremLittle :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) f -
        PowerSeries.coeff (R := ℂ) (2 * k + 1) S) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) :=
    hremOOdd.trans_isLittleO hgeom
  have hS :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) S) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) := by
    apply Filter.EventuallyEq.isEquivalent
    exact Eventually.of_forall fun k => by
      simpa [S] using coeff_twoPolePrincipal_odd (ρ := ρ) (c := c) k
  have hsum :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) S +
        (PowerSeries.coeff (R := ℂ) (2 * k + 1) f -
          PowerSeries.coeff (R := ℂ) (2 * k + 1) S)) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 2)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun k => by ring)

lemma rhoReal_pos : 0 < rhoReal := by
  rw [rhoReal]
  exact half_pos Real.pi_pos

lemma rho_norm : ‖rho‖ = rhoReal := by
  rw [rho]
  exact Complex.norm_of_nonneg rhoReal_pos.le

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact rhoReal_pos

lemma rho_norm_lt_two : ‖rho‖ < (2 : ℝ) := by
  rw [rho_norm, rhoReal]
  nlinarith [Real.pi_lt_four]

lemma one_ne_zero_complex : (1 : ℂ) ≠ 0 := one_ne_zero

theorem tan_analyticAt_zero : AnalyticAt ℂ Complex.tan (0 : ℂ) := by
  have hcos : Complex.cos (0 : ℂ) ≠ 0 := by simp
  exact ((Complex.contDiffAt_tan (x := (0 : ℂ)) (n := (⊤ : WithTop ℕ∞))).2 hcos).analyticAt

/-- The Taylor power series of `Complex.tan` at the origin. -/
def tangentEGFℂ : PowerSeries ℂ :=
  PowerSeries.ofFMLS (Classical.choose tan_analyticAt_zero)

theorem tangentEGFℂ_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.tan (PowerSeries.toFMLS tangentEGFℂ) (0 : ℂ) := by
  rw [tangentEGFℂ, PowerSeries.toFMLS_ofFMLS]
  exact Classical.choose_spec tan_analyticAt_zero

/-- Tangent numbers, represented by their exponential generating function coefficients.
Thus `tangentNumber n / n! = [z^n] tan z` by definition. -/
def tangentNumber (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff (R := ℂ) n tangentEGFℂ

lemma tangentNumber_div_factorial (n : ℕ) :
    tangentNumber n / (n.factorial : ℂ) =
      PowerSeries.coeff (R := ℂ) n tangentEGFℂ := by
  rw [tangentNumber]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- The formal remainder after subtracting the two dominant tangent principal parts. -/
def tangentRemainder : PowerSeries ℂ :=
  tangentEGFℂ - twoPolePrincipal rho (1 : ℂ)

lemma tangentEGFℂ_eq_twoPolePrincipal_add_remainder :
    tangentEGFℂ = twoPolePrincipal rho (1 : ℂ) + tangentRemainder := by
  simp [tangentRemainder]

/-- Analytic function represented by a single simple-pole principal part near the origin. -/
def simplePolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  c * (ρ - z)⁻¹

/-- Analytic function represented by the symmetric two-pole principal part near the origin. -/
def twoPolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  simplePolePrincipalFun ρ c z + simplePolePrincipalFun (-ρ) c z

theorem simplePolePrincipalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (simplePolePrincipalFun ρ c)
      (PowerSeries.toFMLS (simplePolePrincipal ρ c)) (0 : ℂ) := by
  simpa [simplePolePrincipalFun, simplePolePrincipal,
    SupercriticalSeqGenuine.principalFun, SupercriticalSeqGenuine.principalSeries] using
    (SupercriticalSeqGenuine.principalFun_hasFPowerSeriesAt_zero
      (ρ := ρ) (c := c) hρ)

theorem twoPolePrincipalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (twoPolePrincipalFun ρ c)
      (PowerSeries.toFMLS (twoPolePrincipal ρ c)) (0 : ℂ) := by
  have hpos :
      HasFPowerSeriesAt (simplePolePrincipalFun ρ c)
        (PowerSeries.toFMLS (simplePolePrincipal ρ c)) (0 : ℂ) :=
    simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := ρ) (c := c) hρ
  have hneg :
      HasFPowerSeriesAt (simplePolePrincipalFun (-ρ) c)
        (PowerSeries.toFMLS (simplePolePrincipal (-ρ) c)) (0 : ℂ) :=
    simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := -ρ) (c := c) (by
      simpa using hρ)
  simpa [twoPolePrincipalFun, twoPolePrincipal, toFMLS_add] using hpos.add hneg

/-- The raw two-pole-subtracted tangent function.  Its values at the two poles are the
field-default values, so `tangentRemainderFun` below replaces them by the removable limits. -/
def tanRemRaw (z : ℂ) : ℂ :=
  Complex.tan z + (z - rho)⁻¹ + (z + rho)⁻¹

/-- `sin z / z`, with the removable value at zero. -/
def sinDiv (z : ℂ) : ℂ :=
  dslope Complex.sin 0 z

lemma sinDiv_zero : sinDiv 0 = 1 := by
  rw [sinDiv, dslope_same, Complex.deriv_sin]
  simp

lemma sinDiv_of_ne {z : ℂ} (hz : z ≠ 0) :
    sinDiv z = z⁻¹ * Complex.sin z := by
  rw [sinDiv, dslope_of_ne Complex.sin hz]
  simp [slope_def_module, smul_eq_mul]

private lemma analyticAt_dslope_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0 : ℂ)) :
    AnalyticAt ℂ (dslope f 0) (0 : ℂ) := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa using hp.has_fpower_series_dslope_fslope⟩

lemma sinDiv_analyticAt_zero : AnalyticAt ℂ sinDiv (0 : ℂ) := by
  have hsin : AnalyticAt ℂ Complex.sin (0 : ℂ) :=
    (Complex.contDiff_sin (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt
  simpa [sinDiv] using analyticAt_dslope_zero hsin

lemma sinDiv_analyticAt_of_ne {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ sinDiv z := by
  have hmodel : AnalyticAt ℂ (fun w : ℂ => w⁻¹ * Complex.sin w) z :=
    (analyticAt_id.inv hz).mul
      ((Complex.contDiff_sin (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt)
  refine hmodel.congr ?_
  exact (dslope_eventuallyEq_slope_of_ne Complex.sin hz).mono fun w hw => by
    simpa [sinDiv, slope_def_module, smul_eq_mul] using hw.symm

lemma sinDiv_analyticAt (z : ℂ) : AnalyticAt ℂ sinDiv z := by
  by_cases hz : z = 0
  · simpa [hz] using sinDiv_analyticAt_zero
  · exact sinDiv_analyticAt_of_ne hz

/-- The removable core `cot w - 1 / w`, defined analytically at `w = 0`. -/
def tanPoleCore (w : ℂ) : ℂ :=
  dslope (fun u : ℂ => Complex.cos u - sinDiv u) 0 w / sinDiv w

lemma tanPoleCore_analyticAt_zero : AnalyticAt ℂ tanPoleCore (0 : ℂ) := by
  have hcos : AnalyticAt ℂ Complex.cos (0 : ℂ) :=
    (Complex.contDiff_cos (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt
  have hnum :
      AnalyticAt ℂ (dslope (fun u : ℂ => Complex.cos u - sinDiv u) 0) (0 : ℂ) :=
    analyticAt_dslope_zero (hcos.sub sinDiv_analyticAt_zero)
  have hden : AnalyticAt ℂ sinDiv (0 : ℂ) := sinDiv_analyticAt_zero
  have hden_ne : sinDiv 0 ≠ 0 := by
    rw [sinDiv_zero]
    norm_num
  simpa [tanPoleCore] using hnum.div hden hden_ne

lemma tanPoleCore_eq_tan_inv_sub_inv {w : ℂ}
    (hw : w ≠ 0) (hdiv : sinDiv w ≠ 0) :
    tanPoleCore w = (Complex.tan w)⁻¹ - w⁻¹ := by
  have hsin_ne : Complex.sin w ≠ 0 := by
    intro hsin
    apply hdiv
    rw [sinDiv_of_ne hw, hsin]
    simp
  have hzero : Complex.cos 0 - sinDiv 0 = 0 := by
    rw [sinDiv_zero]
    simp
  rw [tanPoleCore, dslope_of_ne (fun u : ℂ => Complex.cos u - sinDiv u) hw,
    slope_def_module, hzero, sub_zero, sinDiv_of_ne hw, Complex.tan_eq_sin_div_cos]
  rw [inv_div]
  field_simp [hw, hsin_ne]
  simp [smul_eq_mul]
  field_simp [hw]

def tanRemLocalPos (z : ℂ) : ℂ :=
  tanPoleCore (rho - z) + (z + rho)⁻¹

def tanRemLocalNeg (z : ℂ) : ℂ :=
  -tanPoleCore (z + rho) + (z - rho)⁻¹

/-- The two-pole-subtracted tangent function with the removable values installed at `±ρ`. -/
def tangentRemainderFun (z : ℂ) : ℂ :=
  if z = rho then tanRemLocalPos z
  else if z = -rho then tanRemLocalNeg z
  else tanRemRaw z

lemma tanRemRaw_eq_tan_sub_twoPolePrincipalFun (z : ℂ) :
    tanRemRaw z = Complex.tan z - twoPolePrincipalFun rho (1 : ℂ) z := by
  have hpos_inv : (rho - z)⁻¹ = - (z - rho)⁻¹ := by
    have h : rho - z = -(z - rho) := by ring
    rw [h, inv_neg]
  have hneg_inv : (-rho - z)⁻¹ = - (z + rho)⁻¹ := by
    have h : -rho - z = -(z + rho) := by ring
    rw [h, inv_neg]
  simp [tanRemRaw, twoPolePrincipalFun, simplePolePrincipalFun, hpos_inv, hneg_inv]
  ring

theorem tanRemRaw_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt tanRemRaw (PowerSeries.toFMLS tangentRemainder) (0 : ℂ) := by
  have hprincipal :
      HasFPowerSeriesAt (twoPolePrincipalFun rho (1 : ℂ))
        (PowerSeries.toFMLS (twoPolePrincipal rho (1 : ℂ))) (0 : ℂ) :=
    twoPolePrincipalFun_hasFPowerSeriesAt_zero (ρ := rho) (c := (1 : ℂ)) rho_norm_pos
  have hsub := tangentEGFℂ_hasFPowerSeriesAt_zero.sub hprincipal
  have hsub' :
      HasFPowerSeriesAt (fun z : ℂ => Complex.tan z - twoPolePrincipalFun rho (1 : ℂ) z)
        (PowerSeries.toFMLS tangentRemainder) (0 : ℂ) := by
    simpa [tangentRemainder, toFMLS_sub] using hsub
  exact hsub'.congr (Eventually.of_forall fun z => by
    exact (tanRemRaw_eq_tan_sub_twoPolePrincipalFun z).symm)

theorem tangentRemainderFun_eventually_eq_tanRemRaw_at_zero :
    tanRemRaw =ᶠ[𝓝 (0 : ℂ)] tangentRemainderFun := by
  have h0rho : (0 : ℂ) ≠ rho := by
    intro h
    have hnorm : ‖rho‖ = 0 := by
      rw [h.symm]
      simp
    exact ne_of_gt rho_norm_pos hnorm
  have h0negrho : (0 : ℂ) ≠ -rho := by
    intro h
    have hnorm : ‖rho‖ = 0 := by
      rw [← norm_neg rho, h.symm]
      simp
    exact ne_of_gt rho_norm_pos hnorm
  filter_upwards [isOpen_ne.mem_nhds h0rho, isOpen_ne.mem_nhds h0negrho] with z hzρ hznegρ
  simp [tangentRemainderFun, hzρ, hznegρ]

theorem tangentRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt tangentRemainderFun (PowerSeries.toFMLS tangentRemainder) (0 : ℂ) :=
  tanRemRaw_hasFPowerSeriesAt_zero.congr tangentRemainderFun_eventually_eq_tanRemRaw_at_zero

lemma tanRemRaw_eq_tanRemLocalPos {z : ℂ}
    (hz : z ≠ rho) (hdiv : sinDiv (rho - z) ≠ 0) :
    tanRemRaw z = tanRemLocalPos z := by
  have hw : rho - z ≠ 0 := by
    intro h
    exact hz (eq_of_sub_eq_zero h).symm
  have htan : Complex.tan z = (Complex.tan (rho - z))⁻¹ := by
    have hzsplit : z = rho - (rho - z) := by ring
    rw [hzsplit]
    simpa [rho, rhoReal] using Complex.tan_pi_div_two_sub (rho - z)
  have hzinv : (z - rho)⁻¹ = - (rho - z)⁻¹ := by
    have h : z - rho = -(rho - z) := by ring
    rw [h, inv_neg]
  rw [tanRemRaw, tanRemLocalPos, htan, hzinv,
    tanPoleCore_eq_tan_inv_sub_inv hw hdiv]
  ring

lemma tanRemRaw_eq_tanRemLocalNeg {z : ℂ}
    (hz : z ≠ -rho) (hdiv : sinDiv (z + rho) ≠ 0) :
    tanRemRaw z = tanRemLocalNeg z := by
  have hw : z + rho ≠ 0 := by
    intro h
    exact hz (eq_neg_of_add_eq_zero_left h)
  have htan : Complex.tan z = - (Complex.tan (z + rho))⁻¹ := by
    have hzsplit : z = -(rho - (z + rho)) := by ring
    rw [hzsplit, Complex.tan_neg]
    simpa [rho, rhoReal] using congrArg Neg.neg (Complex.tan_pi_div_two_sub (z + rho))
  rw [tanRemRaw, tanRemLocalNeg, htan,
    tanPoleCore_eq_tan_inv_sub_inv hw hdiv]
  ring

lemma tanRemLocalPos_analyticAt_rho :
    AnalyticAt ℂ tanRemLocalPos rho := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => rho - z) rho :=
    (analyticAt_const (𝕜 := ℂ) (v := rho) (x := rho)).sub analyticAt_id
  have hcore : AnalyticAt ℂ (fun z : ℂ => tanPoleCore (rho - z)) rho :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := tanPoleCore) (f := fun z : ℂ => rho - z)
      (x := rho) (by simpa using tanPoleCore_analyticAt_zero) hshift
  have hinv_ne : rho + rho ≠ 0 := by
    intro h
    have hmul : (2 : ℂ) * rho = 0 := by
      simpa [two_mul] using h
    have hzero : rho = 0 := by
      rcases mul_eq_zero.mp hmul with htwo | hrho
      · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
      · exact hrho
    exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
  have hinv : AnalyticAt ℂ (fun z : ℂ => (z + rho)⁻¹) rho :=
    (analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := rho))).inv hinv_ne
  simpa [tanRemLocalPos] using hcore.add hinv

lemma tanRemLocalNeg_analyticAt_neg_rho :
    AnalyticAt ℂ tanRemLocalNeg (-rho) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + rho) (-rho) :=
    analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho))
  have hcore : AnalyticAt ℂ (fun z : ℂ => tanPoleCore (z + rho)) (-rho) :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := tanPoleCore) (f := fun z : ℂ => z + rho)
      (x := -rho) (by simpa using tanPoleCore_analyticAt_zero) hshift
  have hneg_core : AnalyticAt ℂ (fun z : ℂ => -tanPoleCore (z + rho)) (-rho) :=
    hcore.neg
  have hinv_ne : -rho - rho ≠ 0 := by
    intro h
    have hmul : (2 : ℂ) * rho = 0 := by
      calc
        (2 : ℂ) * rho = -(-rho - rho) := by ring
        _ = 0 := by rw [h, neg_zero]
    have hzero : rho = 0 := by
      rcases mul_eq_zero.mp hmul with htwo | hrho
      · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
      · exact hrho
    exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
  have hinv : AnalyticAt ℂ (fun z : ℂ => (z - rho)⁻¹) (-rho) :=
    (analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho))).inv hinv_ne
  simpa [tanRemLocalNeg] using hneg_core.add hinv

lemma tangentRemainderFun_eventually_eq_localPos_at_rho :
    tangentRemainderFun =ᶠ[𝓝 rho] tanRemLocalPos := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 rho, sinDiv (rho - z) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => rho - z) rho :=
      ((continuous_const.sub continuous_id).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => sinDiv (rho - z)) rho :=
      by
        have hcomp :=
          sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
        simpa [Function.comp_def] using hcomp
    have hne : sinDiv (rho - rho) ≠ 0 := by
      simp [sinDiv_zero]
    exact hcont.eventually_ne hne
  have hne_neg : ∀ᶠ z in 𝓝 rho, z ≠ -rho := by
    have h : rho ≠ -rho := by
      intro hr
      have hmul : (2 : ℂ) * rho = 0 := by
        have hsub : rho - (-rho) = 0 := by
          rw [← hr, sub_self]
        simpa [two_mul, sub_eq_add_neg] using hsub
      have hzero : rho = 0 := by
        rcases mul_eq_zero.mp hmul with htwo | hrho
        · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
        · exact hrho
      exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
    exact isOpen_ne.mem_nhds h
  filter_upwards [hdiv_event, hne_neg] with z hdiv hne_neg
  by_cases hz : z = rho
  · simp [tangentRemainderFun, tanRemLocalPos, hz]
  · simp [tangentRemainderFun, hz, hne_neg, tanRemRaw_eq_tanRemLocalPos hz hdiv]

lemma tangentRemainderFun_eventually_eq_localNeg_at_neg_rho :
    tangentRemainderFun =ᶠ[𝓝 (-rho)] tanRemLocalNeg := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 (-rho), sinDiv (z + rho) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => z + rho) (-rho) :=
      ((continuous_id.add continuous_const).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => sinDiv (z + rho)) (-rho) :=
      by
        have hcomp :=
          sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
        simpa [Function.comp_def] using hcomp
    have hne : sinDiv ((-rho) + rho) ≠ 0 := by
      simp [sinDiv_zero]
    exact hcont.eventually_ne hne
  have hne_pos : ∀ᶠ z in 𝓝 (-rho), z ≠ rho := by
    have h : -rho ≠ rho := by
      intro hr
      have hmul : (2 : ℂ) * rho = 0 := by
        have hsub : rho - (-rho) = 0 := by
          rw [hr, sub_self]
        simpa [two_mul, sub_eq_add_neg] using hsub
      have hzero : rho = 0 := by
        rcases mul_eq_zero.mp hmul with htwo | hrho
        · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
        · exact hrho
      exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
    exact isOpen_ne.mem_nhds h
  filter_upwards [hdiv_event, hne_pos] with z hdiv hne_pos
  by_cases hz : z = -rho
  · have hne_pos' : -rho ≠ rho := by simpa [hz] using hne_pos
    simp [tangentRemainderFun, tanRemLocalNeg, hz, hne_pos']
  · simp [tangentRemainderFun, hne_pos, hz, tanRemRaw_eq_tanRemLocalNeg hz hdiv]

private lemma abs_int_cast_lt_three_of_norm_cos_zero_le_three
    {z : ℂ} (hz_norm : ‖z‖ ≤ 3) (hcos : Complex.cos z = 0) :
    ∃ k : ℤ, z = ((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2 ∧
      |(((2 * k + 1 : ℤ) : ℝ))| < 3 := by
  rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hk' : z = ((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2 := by
    simpa using hk
  refine ⟨k, hk', ?_⟩
  have hnorm_eq :
      ‖(((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2)‖ =
        |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 := by
    have hint :
        ‖(((2 * k + 1 : ℤ) : ℂ))‖ =
          |(((2 * k + 1 : ℤ) : ℝ))| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (((2 * k + 1 : ℤ) : ℝ)))
    have hpi : ‖(((Real.pi : ℝ) : ℂ))‖ = Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [norm_div, norm_mul, hint, hpi, htwo]
  have hle : |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 ≤ 3 := by
    have hle0 :
        ‖(((2 * k + 1 : ℤ) : ℂ) * ((Real.pi : ℝ) : ℂ) / 2)‖ ≤ 3 := by
      simpa [hk'] using hz_norm
    rw [hnorm_eq] at hle0
    exact hle0
  by_contra hnot
  have hge : 3 ≤ |(((2 * k + 1 : ℤ) : ℝ))| := le_of_not_gt hnot
  have hbig : 3 < |(((2 * k + 1 : ℤ) : ℝ))| * Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  linarith

lemma eq_pm_rho_of_cos_eq_zero_of_norm_le_three {z : ℂ}
    (hz_norm : ‖z‖ ≤ 3) (hcos : Complex.cos z = 0) :
    z = rho ∨ z = -rho := by
  rcases abs_int_cast_lt_three_of_norm_cos_zero_le_three hz_norm hcos with
    ⟨k, hkz, habs⟩
  have hlt : (2 * k + 1 : ℤ) < 3 := by
    have hreal : (((2 * k + 1 : ℤ) : ℝ)) < 3 :=
      (le_abs_self _).trans_lt habs
    exact_mod_cast hreal
  have hgt : -(3 : ℤ) < (2 * k + 1 : ℤ) := by
    have hreal : (-(3 : ℝ)) < (((2 * k + 1 : ℤ) : ℝ)) := by
      have hneg_le : -(((2 * k + 1 : ℤ) : ℝ)) ≤
          |(((2 * k + 1 : ℤ) : ℝ))| := neg_le_abs _
      linarith
    exact_mod_cast hreal
  have hkodd : (2 * k + 1 : ℤ) = -1 ∨ (2 * k + 1 : ℤ) = 1 := by
    omega
  rcases hkodd with hkodd | hkodd
  · right
    rw [hkz, hkodd]
    simp [rho, rhoReal]
    ring
  · left
    rw [hkz, hkodd]
    simp [rho, rhoReal]

lemma tanRemRaw_analyticAt_of_not_poles {z : ℂ}
    (hcos : Complex.cos z ≠ 0) (hpos : z ≠ rho) (hneg : z ≠ -rho) :
    AnalyticAt ℂ tanRemRaw z := by
  have htan : AnalyticAt ℂ Complex.tan z :=
    ((Complex.contDiffAt_tan (x := z) (n := (⊤ : WithTop ℕ∞))).2 hcos).analyticAt
  have hpos_den : z - rho ≠ 0 := sub_ne_zero.mpr hpos
  have hneg_den : z + rho ≠ 0 := by
    intro h
    exact hneg (eq_neg_of_add_eq_zero_left h)
  have hpos_inv : AnalyticAt ℂ (fun w : ℂ => (w - rho)⁻¹) z :=
    (analyticAt_id.sub (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))).inv hpos_den
  have hneg_inv : AnalyticAt ℂ (fun w : ℂ => (w + rho)⁻¹) z :=
    (analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))).inv hneg_den
  simpa [tanRemRaw] using (htan.add hpos_inv).add hneg_inv

theorem tangentRemainderFun_analyticAt_on_closedBall_three {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) (3 : ℝ)) :
    AnalyticAt ℂ tangentRemainderFun z := by
  by_cases hpos : z = rho
  · subst z
    exact tanRemLocalPos_analyticAt_rho.congr
      tangentRemainderFun_eventually_eq_localPos_at_rho.symm
  · by_cases hneg : z = -rho
    · subst z
      exact tanRemLocalNeg_analyticAt_neg_rho.congr
        tangentRemainderFun_eventually_eq_localNeg_at_neg_rho.symm
    · have hz_norm : ‖z‖ ≤ 3 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hcos : Complex.cos z ≠ 0 := by
        intro hzero
        rcases eq_pm_rho_of_cos_eq_zero_of_norm_le_three hz_norm hzero with hzrho | hznegrho
        · exact hpos hzrho
        · exact hneg hznegrho
      have hraw : AnalyticAt ℂ tanRemRaw z :=
        tanRemRaw_analyticAt_of_not_poles hcos hpos hneg
      refine hraw.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hpos, isOpen_ne.mem_nhds hneg] with w hwpos hwneg
      simp [tangentRemainderFun, hwpos, hwneg]

theorem tangentRemainderFun_differentiableOn_closedBall_three :
    DifferentiableOn ℂ tangentRemainderFun (Metric.closedBall (0 : ℂ) (3 : ℝ)) := by
  intro z hz
  exact (tangentRemainderFun_analyticAt_on_closedBall_three hz).differentiableAt.differentiableWithinAt

theorem tangentRemainder_radius_gt_two :
    ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius := by
  exact
    SupercriticalSeqGenuine.powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
      (G := tangentRemainder) (gfun := tangentRemainderFun) (R := (2 : ℝ)) (S := (3 : ℝ))
      (by norm_num) (by norm_num) tangentRemainderFun_hasFPowerSeriesAt_zero
      tangentRemainderFun_differentiableOn_closedBall_three

/-- Conditional tangent coefficient asymptotic from the two dominant poles.  The remaining
analytic input is exactly the radius bound for the two-pole-subtracted tangent remainder. -/
theorem coeff_tangentEGFℂ_odd_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) tangentEGFℂ) ~[atTop]
      (fun k : ℕ => 2 * (1 : ℂ) * rho⁻¹ ^ (2 * k + 2)) := by
  exact twoDominantSimplePole_isEquivalent_odd
    tangentEGFℂ tangentRemainder (ρ := rho) (c := (1 : ℂ)) (R := (2 : ℝ))
    rho_norm_pos rho_norm_lt_two one_ne_zero_complex hrem
    tangentEGFℂ_eq_twoPolePrincipal_add_remainder

lemma two_mul_one_mul (z : ℂ) : 2 * (1 : ℂ) * z = 2 * z := by
  ring

theorem tangentNumber_div_factorial_odd_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius) :
    (fun k : ℕ => tangentNumber (2 * k + 1) / ((2 * k + 1).factorial : ℂ))
      ~[atTop]
    (fun k : ℕ => 2 * rho⁻¹ ^ (2 * k + 2)) := by
  have hbridge :
      (fun k : ℕ => tangentNumber (2 * k + 1) / ((2 * k + 1).factorial : ℂ))
        =ᶠ[atTop]
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) tangentEGFℂ) :=
    Eventually.of_forall fun k => tangentNumber_div_factorial (2 * k + 1)
  exact hbridge.trans_isEquivalent
    ((coeff_tangentEGFℂ_odd_isEquivalent_of_remainder_radius hrem).trans_eventuallyEq
      (Eventually.of_forall fun k => by ring))

lemma Complex_ofReal_rho_inv_eq_two_div_pi :
    rho⁻¹ = (((2 / Real.pi : ℝ) : ℂ)) := by
  rw [rho, rhoReal]
  norm_num [Complex.ofReal_inv]

theorem tangentNumber_div_factorial_odd_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius) :
    (fun k : ℕ => tangentNumber (2 * k + 1) / ((2 * k + 1).factorial : ℂ))
      ~[atTop]
    (fun k : ℕ => 2 * (((2 / Real.pi : ℝ) : ℂ) ^ (2 * k + 2))) := by
  have h := tangentNumber_div_factorial_odd_isEquivalent_of_remainder_radius hrem
  refine h.trans_eventuallyEq (Eventually.of_forall fun k => ?_)
  rw [Complex_ofReal_rho_inv_eq_two_div_pi]

private lemma complex_re_isEquivalent_of_ofReal_right {f : ℕ → ℂ} {g : ℕ → ℝ}
    (h : f ~[atTop] fun n => (g n : ℂ)) :
    (fun n => (f n).re) ~[atTop] g := by
  rw [Asymptotics.IsEquivalent] at h ⊢
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  specialize h hc
  filter_upwards [h] with n hn
  have hle : ‖(f n).re - g n‖ ≤ ‖f n - (g n : ℂ)‖ := by
    simpa [Pi.sub_apply, Complex.sub_re] using Complex.abs_re_le_norm (f n - (g n : ℂ))
  exact hle.trans (by simpa [Pi.sub_apply, Complex.norm_real] using hn)

theorem coeff_tangentEGFℂ_odd_re_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius) :
    (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k + 1) tangentEGFℂ).re)
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 2)) := by
  have h := coeff_tangentEGFℂ_odd_isEquivalent_of_remainder_radius hrem
  have h' :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k + 1) tangentEGFℂ)
        ~[atTop]
      (fun k : ℕ => ((2 * (2 / Real.pi) ^ (2 * k + 2) : ℝ) : ℂ)) := by
    refine h.trans_eventuallyEq (Eventually.of_forall fun k => ?_)
    rw [Complex_ofReal_rho_inv_eq_two_div_pi]
    norm_num [Complex.ofReal_pow]
  exact complex_re_isEquivalent_of_ofReal_right h'

/-- Real tangent numbers attached to the real Taylor coefficients of `tan`. -/
def tangentNumberReal (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n tangentEGFℂ).re

lemma tangentNumberReal_div_factorial (n : ℕ) :
    tangentNumberReal n / (n.factorial : ℝ) =
      (PowerSeries.coeff (R := ℂ) n tangentEGFℂ).re := by
  rw [tangentNumberReal]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

theorem tangentNumberReal_div_factorial_odd_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS tangentRemainder).radius) :
    (fun k : ℕ => tangentNumberReal (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 2)) := by
  have hbridge :
      (fun k : ℕ => tangentNumberReal (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
        =ᶠ[atTop]
      (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k + 1) tangentEGFℂ).re) :=
    Eventually.of_forall fun k => tangentNumberReal_div_factorial (2 * k + 1)
  exact hbridge.trans_isEquivalent
    (coeff_tangentEGFℂ_odd_re_isEquivalent_two_div_pi hrem)

theorem tangentNumber_div_factorial_odd_isEquivalent :
    (fun k : ℕ => tangentNumberReal (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 2)) :=
  tangentNumberReal_div_factorial_odd_isEquivalent_two_div_pi tangentRemainder_radius_gt_two

def knownOddTangentNumbers : List (ℕ × ℕ) :=
  [(1, 1), (3, 2), (5, 16), (7, 272), (9, 7936)]

def tangentAsymptoticScaleReal (n : ℕ) : ℝ :=
  2 * (2 / Real.pi) ^ (n + 1)

def tangentRatioCheckReal : List (ℕ × ℝ) :=
  knownOddTangentNumbers.map fun p =>
    (p.1, (p.2 : ℝ) / ((p.1.factorial : ℝ) * tangentAsymptoticScaleReal p.1))

def piFloat : Float :=
  3.141592653589793

def tangentAsymptoticScaleFloat (n : ℕ) : Float :=
  2.0 * Float.pow (2.0 / piFloat) (Nat.toFloat (n + 1))

def tangentRatioCheckFloat : List (ℕ × Float) :=
  knownOddTangentNumbers.map fun p =>
    (p.1, p.2.toFloat / (p.1.factorial.toFloat * tangentAsymptoticScaleFloat p.1))

#eval tangentRatioCheckFloat

end Tangent
end Meromorphic
end Ch5
end AnalyticCombinatorics
