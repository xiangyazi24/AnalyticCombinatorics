import AnalyticCombinatorics.Ch5.Meromorphic.Tangent
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace Secant

abbrev rhoReal : ℝ :=
  Tangent.rhoReal

abbrev rho : ℂ :=
  Tangent.rho

lemma rho_norm_pos : 0 < ‖rho‖ :=
  Tangent.rho_norm_pos

lemma rho_norm_lt_two : ‖rho‖ < (2 : ℝ) :=
  Tangent.rho_norm_lt_two

lemma one_ne_zero_complex : (1 : ℂ) ≠ 0 :=
  one_ne_zero

/-- The principal part with residues `-c` at `rho` and `c` at `-rho`.  In the
`c / (rho - z)` normalization this is `c / (rho - z) - c / (-rho - z)`. -/
def oppositeTwoPolePrincipal (ρ c : ℂ) : PowerSeries ℂ :=
  Tangent.simplePolePrincipal ρ c + Tangent.simplePolePrincipal (-ρ) (-c)

/-- Analytic representative of `oppositeTwoPolePrincipal`. -/
def oppositeTwoPolePrincipalFun (ρ c : ℂ) (z : ℂ) : ℂ :=
  Tangent.simplePolePrincipalFun ρ c z + Tangent.simplePolePrincipalFun (-ρ) (-c) z

lemma coeff_oppositeTwoPolePrincipal (ρ c : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (oppositeTwoPolePrincipal ρ c) =
      c * ρ⁻¹ ^ (n + 1) - c * (-ρ)⁻¹ ^ (n + 1) := by
  simp [oppositeTwoPolePrincipal, Tangent.coeff_simplePolePrincipal]
  ring

lemma neg_inv_pow_odd (ρ : ℂ) (k : ℕ) :
    (-ρ)⁻¹ ^ (2 * k + 1) = -ρ⁻¹ ^ (2 * k + 1) := by
  rw [inv_neg]
  have hOdd : Odd (2 * k + 1) := odd_two_mul_add_one k
  exact hOdd.neg_pow ρ⁻¹

lemma coeff_oppositeTwoPolePrincipal_even (ρ c : ℂ) (k : ℕ) :
    PowerSeries.coeff (R := ℂ) (2 * k) (oppositeTwoPolePrincipal ρ c) =
      2 * c * ρ⁻¹ ^ (2 * k + 1) := by
  rw [coeff_oppositeTwoPolePrincipal, neg_inv_pow_odd]
  ring

private lemma tendsto_two_mul_atTop :
    Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun k : ℕ => k) atTop atTop).nsmul_atTop
      (by norm_num : 0 < 2))

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_oppositeTwoPole_even
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hpowLittleEven :
      (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k) : ℕ → ℝ) :=
    hpowLittle.comp_tendsto tendsto_two_mul_atTop
  have hmainO :
      (fun k : ℕ => ‖ρ‖⁻¹ ^ (2 * k) : ℕ → ℝ) =O[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
    have hcnorm : ‖2 * c‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact mul_ne_zero (by norm_num) hc
    have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
    have hρinv : ‖ρ‖⁻¹ ≠ 0 := inv_ne_zero hρnorm
    refine isBigO_of_le' (l := atTop) (c := (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro k
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ (2 * k) :=
      pow_nonneg hbase_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    have hnorm_main :
        ‖2 * c * ρ⁻¹ ^ (2 * k + 1)‖ =
          ‖2 * c‖ * ‖ρ‖⁻¹ ^ (2 * k + 1) := by
      rw [norm_mul, norm_pow, norm_inv]
    calc
      ‖ρ‖⁻¹ ^ (2 * k) =
          (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            (‖2 * c‖ * (‖ρ‖⁻¹ ^ (2 * k + 1))) := by
        rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_succ]
        field_simp [hcnorm, hρnorm, hρinv]
      _ = (‖2 * c‖ * ‖ρ‖⁻¹)⁻¹ *
            ‖2 * c * ρ⁻¹ ^ (2 * k + 1)‖ := by rw [hnorm_main]
  exact hpowLittleEven.trans_isBigO hmainO

/-- Two opposite dominant simple poles transfer, restricted to even indices. -/
theorem oppositeTwoDominantSimplePole_isEquivalent_even
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = oppositeTwoPolePrincipal ρ c + g) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f) ~[atTop]
      (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
  let S : PowerSeries ℂ := oppositeTwoPolePrincipal ρ c
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR (by simpa [S] using hfg)
  have hremOEven :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f -
        PowerSeries.coeff (R := ℂ) (2 * k) S) =O[atTop]
        (fun k : ℕ => R⁻¹ ^ (2 * k)) :=
    hremO.comp_tendsto tendsto_two_mul_atTop
  have hgeom :
      (fun k : ℕ => R⁻¹ ^ (2 * k) : ℕ → ℝ) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    inv_radius_pow_isLittleO_oppositeTwoPole_even hρ hρR hc
  have hremLittle :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) f -
        PowerSeries.coeff (R := ℂ) (2 * k) S) =o[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    hremOEven.trans_isLittleO hgeom
  have hS :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) S) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) := by
    apply Filter.EventuallyEq.isEquivalent
    exact Eventually.of_forall fun k => by
      simpa [S] using coeff_oppositeTwoPolePrincipal_even (ρ := ρ) (c := c) k
  have hsum :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) S +
        (PowerSeries.coeff (R := ℂ) (2 * k) f -
          PowerSeries.coeff (R := ℂ) (2 * k) S)) ~[atTop]
        (fun k : ℕ => 2 * c * ρ⁻¹ ^ (2 * k + 1)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun k => by ring)

theorem sec_analyticAt_zero :
    AnalyticAt ℂ (fun z : ℂ => (Complex.cos z)⁻¹) (0 : ℂ) := by
  have hcos : AnalyticAt ℂ Complex.cos (0 : ℂ) :=
    (Complex.contDiff_cos (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt
  exact hcos.inv (by simp)

/-- The Taylor power series of `sec z = 1 / cos z` at the origin. -/
def secantEGFℂ : PowerSeries ℂ :=
  Tangent.PowerSeries.ofFMLS (Classical.choose sec_analyticAt_zero)

theorem secantEGFℂ_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => (Complex.cos z)⁻¹)
      (PowerSeries.toFMLS secantEGFℂ) (0 : ℂ) := by
  rw [secantEGFℂ, Tangent.PowerSeries.toFMLS_ofFMLS]
  exact Classical.choose_spec sec_analyticAt_zero

/-- Secant/Euler numbers attached to the real Taylor coefficients of `sec z`. -/
def secantNumber (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (PowerSeries.coeff (R := ℂ) n secantEGFℂ).re

lemma secantNumber_div_factorial (n : ℕ) :
    secantNumber n / (n.factorial : ℝ) =
      (PowerSeries.coeff (R := ℂ) n secantEGFℂ).re := by
  rw [secantNumber]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

/-- The formal remainder after subtracting the two dominant secant principal parts. -/
def secantRemainder : PowerSeries ℂ :=
  secantEGFℂ - oppositeTwoPolePrincipal rho (1 : ℂ)

lemma secantEGFℂ_eq_oppositeTwoPolePrincipal_add_remainder :
    secantEGFℂ = oppositeTwoPolePrincipal rho (1 : ℂ) + secantRemainder := by
  simp [secantRemainder]

theorem oppositeTwoPolePrincipalFun_hasFPowerSeriesAt_zero
    {ρ c : ℂ} (hρ : 0 < ‖ρ‖) :
    HasFPowerSeriesAt (oppositeTwoPolePrincipalFun ρ c)
      (PowerSeries.toFMLS (oppositeTwoPolePrincipal ρ c)) (0 : ℂ) := by
  have hpos :
      HasFPowerSeriesAt (Tangent.simplePolePrincipalFun ρ c)
        (PowerSeries.toFMLS (Tangent.simplePolePrincipal ρ c)) (0 : ℂ) :=
    Tangent.simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := ρ) (c := c) hρ
  have hneg :
      HasFPowerSeriesAt (Tangent.simplePolePrincipalFun (-ρ) (-c))
        (PowerSeries.toFMLS (Tangent.simplePolePrincipal (-ρ) (-c))) (0 : ℂ) :=
    Tangent.simplePolePrincipalFun_hasFPowerSeriesAt_zero (ρ := -ρ) (c := -c) (by
      simpa using hρ)
  simpa [oppositeTwoPolePrincipalFun, oppositeTwoPolePrincipal, Tangent.toFMLS_add] using
    hpos.add hneg

/-- The raw two-pole-subtracted secant function. Its pole values are field defaults; the
removable function below installs analytic values at `±rho`. -/
def secRemRaw (z : ℂ) : ℂ :=
  (Complex.cos z)⁻¹ - (rho - z)⁻¹ - (z + rho)⁻¹

lemma oppositeTwoPolePrincipalFun_one_eq (z : ℂ) :
    oppositeTwoPolePrincipalFun rho (1 : ℂ) z =
      (rho - z)⁻¹ + (z + rho)⁻¹ := by
  have hneg_inv : (-rho - z)⁻¹ = - (z + rho)⁻¹ := by
    have h : -rho - z = -(z + rho) := by ring
    rw [h, inv_neg]
  simp [oppositeTwoPolePrincipalFun, Tangent.simplePolePrincipalFun, hneg_inv]

lemma secRemRaw_eq_sec_sub_oppositeTwoPolePrincipalFun (z : ℂ) :
    secRemRaw z =
      (Complex.cos z)⁻¹ - oppositeTwoPolePrincipalFun rho (1 : ℂ) z := by
  rw [oppositeTwoPolePrincipalFun_one_eq]
  simp [secRemRaw]
  ring

theorem secRemRaw_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt secRemRaw (PowerSeries.toFMLS secantRemainder) (0 : ℂ) := by
  have hprincipal :
      HasFPowerSeriesAt (oppositeTwoPolePrincipalFun rho (1 : ℂ))
        (PowerSeries.toFMLS (oppositeTwoPolePrincipal rho (1 : ℂ))) (0 : ℂ) :=
    oppositeTwoPolePrincipalFun_hasFPowerSeriesAt_zero (ρ := rho) (c := (1 : ℂ)) rho_norm_pos
  have hsub := secantEGFℂ_hasFPowerSeriesAt_zero.sub hprincipal
  have hsub' :
      HasFPowerSeriesAt
        (fun z : ℂ => (Complex.cos z)⁻¹ - oppositeTwoPolePrincipalFun rho (1 : ℂ) z)
        (PowerSeries.toFMLS secantRemainder) (0 : ℂ) := by
    simpa [secantRemainder, Tangent.toFMLS_sub] using hsub
  exact hsub'.congr (Eventually.of_forall fun z => by
    exact (secRemRaw_eq_sec_sub_oppositeTwoPolePrincipalFun z).symm)

private lemma analyticAt_dslope_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0 : ℂ)) :
    AnalyticAt ℂ (dslope f 0) (0 : ℂ) := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.fslope, by simpa using hp.has_fpower_series_dslope_fslope⟩

/-- The removable core `(1 / sinDiv w - 1) / w`, analytically defined at `w = 0`. -/
def secPoleCore (w : ℂ) : ℂ :=
  dslope (fun u : ℂ => (Tangent.sinDiv u)⁻¹) 0 w

lemma secPoleCore_analyticAt_zero :
    AnalyticAt ℂ secPoleCore (0 : ℂ) := by
  have hsinDiv : AnalyticAt ℂ Tangent.sinDiv (0 : ℂ) :=
    Tangent.sinDiv_analyticAt_zero
  have hne : Tangent.sinDiv 0 ≠ 0 := by
    rw [Tangent.sinDiv_zero]
    norm_num
  have hinv : AnalyticAt ℂ (fun u : ℂ => (Tangent.sinDiv u)⁻¹) (0 : ℂ) :=
    hsinDiv.inv hne
  simpa [secPoleCore] using analyticAt_dslope_zero hinv

lemma secPoleCore_eq_inv_sinDiv_sub_inv {w : ℂ} (hw : w ≠ 0) :
    secPoleCore w = w⁻¹ * ((Tangent.sinDiv w)⁻¹ - 1) := by
  rw [secPoleCore, dslope_of_ne (fun u : ℂ => (Tangent.sinDiv u)⁻¹) hw,
    slope_def_module, Tangent.sinDiv_zero]
  simp [smul_eq_mul]

def secRemLocalPos (z : ℂ) : ℂ :=
  secPoleCore (rho - z) - (z + rho)⁻¹

def secRemLocalNeg (z : ℂ) : ℂ :=
  secPoleCore (z + rho) - (rho - z)⁻¹

/-- The two-pole-subtracted secant function with removable values installed at `±rho`. -/
def secantRemainderFun (z : ℂ) : ℂ :=
  if z = rho then secRemLocalPos z
  else if z = -rho then secRemLocalNeg z
  else secRemRaw z

lemma cos_eq_mul_sinDiv_pos {z : ℂ} (hz : z ≠ rho) :
    Complex.cos z = (rho - z) * Tangent.sinDiv (rho - z) := by
  have hw : rho - z ≠ 0 := by
    intro h
    exact hz (eq_of_sub_eq_zero h).symm
  have hcos : Complex.cos z = Complex.sin (rho - z) := by
    have hzsplit : z = rho - (rho - z) := by ring
    have hrewrite : Complex.cos z = Complex.cos (rho - (rho - z)) :=
      congrArg Complex.cos hzsplit
    have htrig : Complex.cos (rho - (rho - z)) = Complex.sin (rho - z) := by
      simpa [rho, rhoReal, Tangent.rho, Tangent.rhoReal] using
        Complex.cos_pi_div_two_sub (rho - z)
    exact hrewrite.trans htrig
  have hsin : Complex.sin (rho - z) = (rho - z) * Tangent.sinDiv (rho - z) := by
    rw [Tangent.sinDiv_of_ne hw]
    field_simp [hw]
  rw [hcos, hsin]

lemma cos_eq_mul_sinDiv_neg {z : ℂ} (hz : z ≠ -rho) :
    Complex.cos z = (z + rho) * Tangent.sinDiv (z + rho) := by
  have hw : z + rho ≠ 0 := by
    intro h
    exact hz (eq_neg_of_add_eq_zero_left h)
  have hcos : Complex.cos z = Complex.sin (z + rho) := by
    have hzsplit : z = -(rho - (z + rho)) := by ring
    have hrewrite : Complex.cos z = Complex.cos (-(rho - (z + rho))) :=
      congrArg Complex.cos hzsplit
    have hneg : Complex.cos (-(rho - (z + rho))) = Complex.cos (rho - (z + rho)) := by
      rw [Complex.cos_neg]
    have htrig : Complex.cos (rho - (z + rho)) = Complex.sin (z + rho) := by
      simpa [rho, rhoReal, Tangent.rho, Tangent.rhoReal] using
        Complex.cos_pi_div_two_sub (z + rho)
    exact hrewrite.trans (hneg.trans htrig)
  have hsin : Complex.sin (z + rho) = (z + rho) * Tangent.sinDiv (z + rho) := by
    rw [Tangent.sinDiv_of_ne hw]
    field_simp [hw]
  rw [hcos, hsin]

lemma secRemRaw_eq_secRemLocalPos {z : ℂ}
    (hz : z ≠ rho) (hdiv : Tangent.sinDiv (rho - z) ≠ 0) :
    secRemRaw z = secRemLocalPos z := by
  have hw : rho - z ≠ 0 := by
    intro h
    exact hz (eq_of_sub_eq_zero h).symm
  rw [secRemRaw, secRemLocalPos, cos_eq_mul_sinDiv_pos hz,
    secPoleCore_eq_inv_sinDiv_sub_inv hw]
  field_simp [hw, hdiv]

lemma secRemRaw_eq_secRemLocalNeg {z : ℂ}
    (hz : z ≠ -rho) (hdiv : Tangent.sinDiv (z + rho) ≠ 0) :
    secRemRaw z = secRemLocalNeg z := by
  have hw : z + rho ≠ 0 := by
    intro h
    exact hz (eq_neg_of_add_eq_zero_left h)
  rw [secRemRaw, secRemLocalNeg, cos_eq_mul_sinDiv_neg hz,
    secPoleCore_eq_inv_sinDiv_sub_inv hw]
  field_simp [hw, hdiv]
  ring

lemma secRemLocalPos_analyticAt_rho :
    AnalyticAt ℂ secRemLocalPos rho := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => rho - z) rho :=
    (analyticAt_const (𝕜 := ℂ) (v := rho) (x := rho)).sub analyticAt_id
  have hcore : AnalyticAt ℂ (fun z : ℂ => secPoleCore (rho - z)) rho :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := secPoleCore) (f := fun z : ℂ => rho - z)
      (x := rho) (by simpa using secPoleCore_analyticAt_zero) hshift
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
  simpa [secRemLocalPos] using hcore.sub hinv

lemma secRemLocalNeg_analyticAt_neg_rho :
    AnalyticAt ℂ secRemLocalNeg (-rho) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + rho) (-rho) :=
    analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho))
  have hcore : AnalyticAt ℂ (fun z : ℂ => secPoleCore (z + rho)) (-rho) :=
    AnalyticAt.comp' (𝕜 := ℂ) (g := secPoleCore) (f := fun z : ℂ => z + rho)
      (x := -rho) (by simpa using secPoleCore_analyticAt_zero) hshift
  have hinv_ne : rho - (-rho) ≠ 0 := by
    intro h
    have hmul : (2 : ℂ) * rho = 0 := by
      simpa [two_mul] using h
    have hzero : rho = 0 := by
      rcases mul_eq_zero.mp hmul with htwo | hrho
      · exact (False.elim ((by norm_num : (2 : ℂ) ≠ 0) htwo))
      · exact hrho
    exact (norm_ne_zero_iff.mp (ne_of_gt rho_norm_pos)) hzero
  have hinv : AnalyticAt ℂ (fun z : ℂ => (rho - z)⁻¹) (-rho) :=
    ((analyticAt_const (𝕜 := ℂ) (v := rho) (x := -rho)).sub analyticAt_id).inv hinv_ne
  simpa [secRemLocalNeg] using hcore.sub hinv

lemma secantRemainderFun_eventually_eq_secRemRaw_at_zero :
    secRemRaw =ᶠ[𝓝 (0 : ℂ)] secantRemainderFun := by
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
  simp [secantRemainderFun, hzρ, hznegρ]

theorem secantRemainderFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt secantRemainderFun (PowerSeries.toFMLS secantRemainder) (0 : ℂ) :=
  secRemRaw_hasFPowerSeriesAt_zero.congr secantRemainderFun_eventually_eq_secRemRaw_at_zero

lemma secantRemainderFun_eventually_eq_localPos_at_rho :
    secantRemainderFun =ᶠ[𝓝 rho] secRemLocalPos := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 rho, Tangent.sinDiv (rho - z) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => rho - z) rho :=
      ((continuous_const.sub continuous_id).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => Tangent.sinDiv (rho - z)) rho := by
      have hcomp :=
        Tangent.sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
      simpa [Function.comp_def] using hcomp
    have hne : Tangent.sinDiv (rho - rho) ≠ 0 := by
      simp [Tangent.sinDiv_zero]
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
  · simp [secantRemainderFun, secRemLocalPos, hz]
  · simp [secantRemainderFun, hz, hne_neg, secRemRaw_eq_secRemLocalPos hz hdiv]

lemma secantRemainderFun_eventually_eq_localNeg_at_neg_rho :
    secantRemainderFun =ᶠ[𝓝 (-rho)] secRemLocalNeg := by
  have hdiv_event :
      ∀ᶠ z in 𝓝 (-rho), Tangent.sinDiv (z + rho) ≠ 0 := by
    have hshift : ContinuousAt (fun z : ℂ => z + rho) (-rho) :=
      ((continuous_id.add continuous_const).continuousAt)
    have hcont : ContinuousAt (fun z : ℂ => Tangent.sinDiv (z + rho)) (-rho) := by
      have hcomp :=
        Tangent.sinDiv_analyticAt_zero.continuousAt.comp_of_eq hshift (by simp)
      simpa [Function.comp_def] using hcomp
    have hne : Tangent.sinDiv ((-rho) + rho) ≠ 0 := by
      simp [Tangent.sinDiv_zero]
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
    simp [secantRemainderFun, secRemLocalNeg, hz, hne_pos']
  · simp [secantRemainderFun, hne_pos, hz, secRemRaw_eq_secRemLocalNeg hz hdiv]

lemma secRemRaw_analyticAt_of_not_poles {z : ℂ}
    (hcos : Complex.cos z ≠ 0) (hpos : z ≠ rho) (hneg : z ≠ -rho) :
    AnalyticAt ℂ secRemRaw z := by
  have hsec : AnalyticAt ℂ (fun w : ℂ => (Complex.cos w)⁻¹) z :=
    ((Complex.contDiff_cos (n := (⊤ : WithTop ℕ∞))).contDiffAt.analyticAt).inv hcos
  have hpos_den : rho - z ≠ 0 := by
    intro h
    exact hpos (eq_of_sub_eq_zero h).symm
  have hneg_den : z + rho ≠ 0 := by
    intro h
    exact hneg (eq_neg_of_add_eq_zero_left h)
  have hpos_inv : AnalyticAt ℂ (fun w : ℂ => (rho - w)⁻¹) z :=
    ((analyticAt_const (𝕜 := ℂ) (v := rho) (x := z)).sub analyticAt_id).inv hpos_den
  have hneg_inv : AnalyticAt ℂ (fun w : ℂ => (w + rho)⁻¹) z :=
    (analyticAt_id.add (analyticAt_const (𝕜 := ℂ) (v := rho) (x := z))).inv hneg_den
  simpa [secRemRaw] using (hsec.sub hpos_inv).sub hneg_inv

theorem secantRemainderFun_analyticAt_on_closedBall_three {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) (3 : ℝ)) :
    AnalyticAt ℂ secantRemainderFun z := by
  by_cases hpos : z = rho
  · subst z
    exact secRemLocalPos_analyticAt_rho.congr
      secantRemainderFun_eventually_eq_localPos_at_rho.symm
  · by_cases hneg : z = -rho
    · subst z
      exact secRemLocalNeg_analyticAt_neg_rho.congr
        secantRemainderFun_eventually_eq_localNeg_at_neg_rho.symm
    · have hz_norm : ‖z‖ ≤ 3 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      have hcos : Complex.cos z ≠ 0 := by
        intro hzero
        rcases Tangent.eq_pm_rho_of_cos_eq_zero_of_norm_le_three hz_norm hzero with hzrho | hznegrho
        · exact hpos hzrho
        · exact hneg hznegrho
      have hraw : AnalyticAt ℂ secRemRaw z :=
        secRemRaw_analyticAt_of_not_poles hcos hpos hneg
      refine hraw.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hpos, isOpen_ne.mem_nhds hneg] with w hwpos hwneg
      simp [secantRemainderFun, hwpos, hwneg]

theorem secantRemainderFun_differentiableOn_closedBall_three :
    DifferentiableOn ℂ secantRemainderFun (Metric.closedBall (0 : ℂ) (3 : ℝ)) := by
  intro z hz
  exact (secantRemainderFun_analyticAt_on_closedBall_three hz).differentiableAt.differentiableWithinAt

theorem secantRemainder_radius_gt_two :
    ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius := by
  exact
    SupercriticalSeqGenuine.powerSeries_radius_gt_of_hasFPowerSeriesAt_differentiableOn_larger
      (G := secantRemainder) (gfun := secantRemainderFun) (R := (2 : ℝ)) (S := (3 : ℝ))
      (by norm_num) (by norm_num) secantRemainderFun_hasFPowerSeriesAt_zero
      secantRemainderFun_differentiableOn_closedBall_three

theorem coeff_secantEGFℂ_even_isEquivalent_of_remainder_radius
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ) ~[atTop]
      (fun k : ℕ => 2 * (1 : ℂ) * rho⁻¹ ^ (2 * k + 1)) := by
  exact oppositeTwoDominantSimplePole_isEquivalent_even
    secantEGFℂ secantRemainder (ρ := rho) (c := (1 : ℂ)) (R := (2 : ℝ))
    rho_norm_pos rho_norm_lt_two one_ne_zero_complex hrem
    secantEGFℂ_eq_oppositeTwoPolePrincipal_add_remainder

lemma Complex_ofReal_rho_inv_eq_two_div_pi :
    rho⁻¹ = (((2 / Real.pi : ℝ) : ℂ)) := by
  simpa [rho] using Tangent.Complex_ofReal_rho_inv_eq_two_div_pi

theorem coeff_secantEGFℂ_even_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ)
      ~[atTop]
    (fun k : ℕ => 2 * (((2 / Real.pi : ℝ) : ℂ) ^ (2 * k + 1))) := by
  have h := coeff_secantEGFℂ_even_isEquivalent_of_remainder_radius hrem
  refine h.trans_eventuallyEq (Eventually.of_forall fun k => ?_)
  rw [Complex_ofReal_rho_inv_eq_two_div_pi]
  ring

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

theorem coeff_secantEGFℂ_even_re_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ).re)
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) := by
  have h := coeff_secantEGFℂ_even_isEquivalent_of_remainder_radius hrem
  have h' :
      (fun k : ℕ => PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ)
        ~[atTop]
      (fun k : ℕ => ((2 * (2 / Real.pi) ^ (2 * k + 1) : ℝ) : ℂ)) := by
    refine h.trans_eventuallyEq (Eventually.of_forall fun k => ?_)
    rw [Complex_ofReal_rho_inv_eq_two_div_pi]
    norm_num [Complex.ofReal_pow]
  exact complex_re_isEquivalent_of_ofReal_right h'

theorem secantNumber_div_factorial_even_isEquivalent_two_div_pi
    (hrem : ENNReal.ofReal (2 : ℝ) < (PowerSeries.toFMLS secantRemainder).radius) :
    (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) := by
  have hbridge :
      (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
        =ᶠ[atTop]
      (fun k : ℕ => (PowerSeries.coeff (R := ℂ) (2 * k) secantEGFℂ).re) :=
    Eventually.of_forall fun k => secantNumber_div_factorial (2 * k)
  exact hbridge.trans_isEquivalent
    (coeff_secantEGFℂ_even_re_isEquivalent_two_div_pi hrem)

theorem secantNumber_div_factorial_even_isEquivalent :
    (fun k : ℕ => secantNumber (2 * k) / ((2 * k).factorial : ℝ))
      ~[atTop]
    (fun k : ℕ => 2 * (2 / Real.pi) ^ (2 * k + 1)) :=
  secantNumber_div_factorial_even_isEquivalent_two_div_pi secantRemainder_radius_gt_two

def knownEvenSecantNumbers : List (ℕ × ℕ) :=
  [(0, 1), (2, 1), (4, 5), (6, 61), (8, 1385)]

def secantAsymptoticScaleReal (n : ℕ) : ℝ :=
  2 * (2 / Real.pi) ^ (n + 1)

def secantRatioCheckReal : List (ℕ × ℝ) :=
  knownEvenSecantNumbers.map fun p =>
    (p.1, (p.2 : ℝ) / ((p.1.factorial : ℝ) * secantAsymptoticScaleReal p.1))

def piFloat : Float :=
  3.141592653589793

def secantAsymptoticScaleFloat (n : ℕ) : Float :=
  2.0 * Float.pow (2.0 / piFloat) (Nat.toFloat (n + 1))

def secantRatioCheckFloat : List (ℕ × Float) :=
  knownEvenSecantNumbers.map fun p =>
    (p.1, p.2.toFloat / (p.1.factorial.toFloat * secantAsymptoticScaleFloat p.1))

#eval secantRatioCheckFloat

end Secant
end Meromorphic
end Ch5
end AnalyticCombinatorics
