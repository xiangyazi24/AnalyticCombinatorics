import Mathlib
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer

/-!
# Fibonacci compositions via the meromorphic transfer

Compositions of `n` into parts `1` and `2` are represented here by the shifted
Fibonacci count `Nat.fib (n + 1)`.  The ordinary generating function is
`1 / (1 - z - z^2)`, whose dominant pole is
`rho = (sqrt 5 - 1) / 2`.
-/

open Complex Filter Asymptotics
open scoped ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace FibonacciCompositionsNS

local notation "φc" => ((Real.goldenRatio : ℝ) : ℂ)
local notation "ψc" => ((Real.goldenConj : ℝ) : ℂ)
local notation "√5c" => ((Real.sqrt 5 : ℝ) : ℂ)

/-- The dominant pole `rho = (sqrt 5 - 1) / 2 = 1 / phi`. -/
def rho : ℂ := (((Real.sqrt 5 - 1) / 2 : ℝ) : ℂ)

/-- The other pole, `-phi`. -/
def otherRoot : ℂ := ((-Real.goldenRatio : ℝ) : ℂ)

/-- The shifted Fibonacci count for `{1,2}`-compositions. -/
def fibonacciCompositionCount (n : ℕ) : ℕ := Nat.fib (n + 1)

/-- The formal power series with coefficients `F_{n+1}`. -/
def fibonacciSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (fibonacciCompositionCount n : ℂ)

/-- The rational OGF `1 / (1 - z - z^2)`. -/
def fibonacciOGFℂ : PowerSeries ℂ :=
  (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ)⁻¹

/-- The `c = -residue` constant at the dominant pole. -/
def dominantResidueConstant : ℂ := √5c⁻¹

/-- The `c = -residue` constant at the conjugate pole. -/
def conjugateResidueConstant : ℂ := -√5c⁻¹

/-- Principal part at the dominant pole in the normalization used by
`dominant_simplePole_isEquivalent`. -/
def dominantPrincipal : PowerSeries ℂ :=
  PowerSeries.C (dominantResidueConstant * rho⁻¹) *
    PowerSeries.rescale rho⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The non-dominant simple-pole contribution. -/
def conjugatePrincipal : PowerSeries ℂ :=
  PowerSeries.C (conjugateResidueConstant * otherRoot⁻¹) *
    PowerSeries.rescale otherRoot⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))

/-- The analytic remainder past the dominant pole. -/
def remainder : PowerSeries ℂ := conjugatePrincipal

lemma sqrt_five_pos : (0 : ℝ) < Real.sqrt 5 := by
  positivity

lemma sqrt_five_ne_zero : √5c ≠ 0 := by
  exact_mod_cast (ne_of_gt sqrt_five_pos)

lemma dominantResidueConstant_ne_zero : dominantResidueConstant ≠ 0 := by
  exact inv_ne_zero sqrt_five_ne_zero

lemma phi_ne_zero : φc ≠ 0 := by
  exact_mod_cast Real.goldenRatio_ne_zero

lemma psi_ne_zero : ψc ≠ 0 := by
  exact_mod_cast Real.goldenConj_ne_zero

lemma phi_add_psi : φc + ψc = 1 := by
  exact_mod_cast Real.goldenRatio_add_goldenConj

lemma phi_mul_psi : φc * ψc = -1 := by
  exact_mod_cast Real.goldenRatio_mul_goldenConj

lemma phi_sub_psi : φc - ψc = √5c := by
  exact_mod_cast Real.goldenRatio_sub_goldenConj

lemma rho_real_eq_inv_phi : ((Real.sqrt 5 - 1) / 2 : ℝ) = Real.goldenRatio⁻¹ := by
  rw [Real.inv_goldenRatio, Real.goldenConj]
  ring

lemma rho_eq_inv_phi : rho = φc⁻¹ := by
  rw [rho]
  exact_mod_cast rho_real_eq_inv_phi

lemma rho_inv : rho⁻¹ = φc := by
  rw [rho_eq_inv_phi]
  simp

lemma otherRoot_inv : otherRoot⁻¹ = ψc := by
  rw [otherRoot]
  have hreal : (-Real.goldenRatio : ℝ)⁻¹ = Real.goldenConj := by
    rw [inv_neg, Real.inv_goldenRatio]
    ring
  exact_mod_cast hreal

lemma rho_nonneg_real : (0 : ℝ) ≤ (Real.sqrt 5 - 1) / 2 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith

lemma rho_norm : ‖rho‖ = Real.goldenRatio⁻¹ := by
  rw [rho, Complex.norm_of_nonneg rho_nonneg_real]
  exact rho_real_eq_inv_phi

lemma rho_norm_pos : 0 < ‖rho‖ := by
  rw [rho_norm]
  exact inv_pos.mpr Real.goldenRatio_pos

lemma rho_norm_lt_one : ‖rho‖ < 1 := by
  rw [rho_norm]
  exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

lemma otherRoot_norm : ‖otherRoot‖ = Real.goldenRatio := by
  rw [otherRoot]
  have hcast : ((-Real.goldenRatio : ℝ) : ℂ) = -φc := by
    norm_num
  rw [hcast, norm_neg]
  exact Complex.norm_of_nonneg Real.goldenRatio_pos.le

/-- The pole `rho` is strictly closer to the origin than the other root. -/
theorem rho_norm_lt_otherRoot_norm : ‖rho‖ < ‖otherRoot‖ := by
  calc
    ‖rho‖ = Real.goldenRatio⁻¹ := rho_norm
    _ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    _ < Real.goldenRatio := Real.one_lt_goldenRatio
    _ = ‖otherRoot‖ := otherRoot_norm.symm

/-- `rho` is a root of `1 - z - z^2`. -/
theorem rho_is_root : 1 - rho - rho ^ 2 = 0 := by
  rw [rho]
  norm_cast
  have hnonneg : (0 : ℝ) ≤ 5 := by
    norm_num
  have hsq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    exact Real.sq_sqrt hnonneg
  ring_nf
  rw [hsq]
  norm_num

/-- The non-dominant pole is the other root of `1 - z - z^2`. -/
theorem otherRoot_is_root : 1 - otherRoot - otherRoot ^ 2 = 0 := by
  rw [otherRoot]
  have hcast : ((-Real.goldenRatio : ℝ) : ℂ) = -φc := by
    norm_num
  rw [hcast]
  have hφsq : φc ^ 2 = φc + 1 := by
    exact_mod_cast Real.goldenRatio_sq
  calc
    1 - -φc - (-φc) ^ 2 = 1 + φc - φc ^ 2 := by ring
    _ = 0 := by
      rw [hφsq]
      ring

lemma one_add_two_mul_rho : 1 + 2 * rho = √5c := by
  rw [rho]
  norm_num
  ring

/-- The residue at the dominant pole is `-1 / sqrt 5`. -/
theorem denominatorDerivative_inv_at_rho : (-1 - 2 * rho)⁻¹ = -√5c⁻¹ := by
  have h : -1 - 2 * rho = -√5c := by
    rw [← one_add_two_mul_rho]
    ring
  rw [h, inv_neg]

@[simp] lemma coeff_fibonacciSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n fibonacciSeriesℂ =
      (fibonacciCompositionCount n : ℂ) := by
  simp [fibonacciSeriesℂ]

lemma constantCoeff_fibonacciSeriesℂ :
    PowerSeries.constantCoeff fibonacciSeriesℂ = 1 := by
  simp [fibonacciSeriesℂ, fibonacciCompositionCount]

/-- Formal OGF identity:
`sum F_{n+1} z^n` is the inverse of `1 - z - z^2`. -/
theorem fibonacciSeries_mul_denominator :
    fibonacciSeriesℂ * (1 - (PowerSeries.X + PowerSeries.X ^ 2)) = 1 := by
  rw [show fibonacciSeriesℂ * (1 - (PowerSeries.X + PowerSeries.X ^ 2)) =
      fibonacciSeriesℂ - fibonacciSeriesℂ * PowerSeries.X -
        fibonacciSeriesℂ * PowerSeries.X ^ 2 by ring]
  ext n
  cases n with
  | zero =>
      simp [constantCoeff_fibonacciSeriesℂ]
  | succ n =>
      cases n with
      | zero =>
          simp [PowerSeries.coeff_mul_X_pow', fibonacciCompositionCount]
      | succ n =>
          simp only [map_sub, coeff_fibonacciSeriesℂ, PowerSeries.coeff_one,
            Nat.succ_ne_zero, ↓reduceIte, fibonacciCompositionCount]
          rw [show n + 1 + 1 = n + 2 by omega]
          rw [PowerSeries.coeff_succ_mul_X]
          rw [PowerSeries.coeff_mul_X_pow]
          have h := Nat.fib_add_two (n := n + 1)
          rw [h]
          simp [fibonacciCompositionCount]

lemma denominator_constantCoeff_ne_zero :
    PowerSeries.constantCoeff
      (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ) ≠ 0 := by
  simp

/-- The shifted Fibonacci series is exactly `1 / (1 - z - z^2)`. -/
theorem fibonacciSeries_eq_fibonacciOGFℂ :
    fibonacciSeriesℂ = fibonacciOGFℂ := by
  rw [fibonacciOGFℂ]
  exact (PowerSeries.eq_inv_iff_mul_eq_one denominator_constantCoeff_ne_zero).2
    fibonacciSeries_mul_denominator

/-- Coefficients of the rational OGF are the shifted Fibonacci numbers. -/
theorem coeff_fibonacciOGFℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n fibonacciOGFℂ =
      (fibonacciCompositionCount n : ℂ) := by
  rw [← fibonacciSeries_eq_fibonacciOGFℂ]
  simp

lemma denominator_factor :
    (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ) =
      (1 - PowerSeries.C φc * PowerSeries.X) *
        (1 - PowerSeries.C ψc * PowerSeries.X) := by
  have hCadd : (PowerSeries.C (φc + ψc) : PowerSeries ℂ) = 1 := by
    rw [phi_add_psi]
    simp
  have hCmul : (PowerSeries.C (φc * ψc) : PowerSeries ℂ) = -1 := by
    rw [phi_mul_psi]
    simp
  calc
    (1 - (PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℂ)
        = 1 - PowerSeries.X - PowerSeries.X ^ 2 := by ring
    _ = 1 - PowerSeries.C (φc + ψc) * PowerSeries.X +
          PowerSeries.C (φc * ψc) * PowerSeries.X ^ 2 := by
        rw [hCadd, hCmul]
        ring
    _ = (1 - PowerSeries.C φc * PowerSeries.X) *
          (1 - PowerSeries.C ψc * PowerSeries.X) := by
        rw [map_add, map_mul]
        ring

lemma geom_mul_factor (a : ℂ) :
    PowerSeries.rescale a (PowerSeries.invUnitsSub (1 : ℂˣ)) *
      (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.invUnitsSub_mul_sub (u := (1 : ℂˣ)))
  simpa [PowerSeries.rescale_X] using h

lemma dominantCoeff_add_conjugateCoeff :
    dominantResidueConstant * rho⁻¹ +
        conjugateResidueConstant * otherRoot⁻¹ = 1 := by
  rw [dominantResidueConstant, conjugateResidueConstant, rho_inv, otherRoot_inv]
  calc
    √5c⁻¹ * φc + -√5c⁻¹ * ψc = √5c⁻¹ * (φc - ψc) := by ring
    _ = 1 := by
      rw [phi_sub_psi]
      field_simp [sqrt_five_ne_zero]

lemma crossCoeff_zero_inv :
    dominantResidueConstant * rho⁻¹ * otherRoot⁻¹ +
        conjugateResidueConstant * otherRoot⁻¹ * rho⁻¹ = 0 := by
  rw [dominantResidueConstant, conjugateResidueConstant, rho_inv, otherRoot_inv]
  ring

lemma principal_add_remainder_mul_denominator :
    (dominantPrincipal + remainder) *
      (1 - (PowerSeries.X + PowerSeries.X ^ 2)) = 1 := by
  let Gφ : PowerSeries ℂ :=
    PowerSeries.rescale φc (PowerSeries.invUnitsSub (1 : ℂˣ))
  let Gψ : PowerSeries ℂ :=
    PowerSeries.rescale ψc (PowerSeries.invUnitsSub (1 : ℂˣ))
  let Fφ : PowerSeries ℂ := 1 - PowerSeries.C φc * PowerSeries.X
  let Fψ : PowerSeries ℂ := 1 - PowerSeries.C ψc * PowerSeries.X
  have hφgeom : Gφ * Fφ = 1 := by
    simpa [Gφ, Fφ] using geom_mul_factor φc
  have hψgeom : Gψ * Fψ = 1 := by
    simpa [Gψ, Fψ] using geom_mul_factor ψc
  rw [denominator_factor]
  change (dominantPrincipal + remainder) * (Fφ * Fψ) = 1
  rw [dominantPrincipal, remainder, conjugatePrincipal, rho_inv, otherRoot_inv]
  change (PowerSeries.C (dominantResidueConstant * φc) * Gφ +
      PowerSeries.C (conjugateResidueConstant * ψc) * Gψ) * (Fφ * Fψ) = 1
  calc
    (PowerSeries.C (dominantResidueConstant * φc) * Gφ +
        PowerSeries.C (conjugateResidueConstant * ψc) * Gψ) * (Fφ * Fψ)
        = PowerSeries.C (dominantResidueConstant * φc) * (Gφ * Fφ) * Fψ +
            PowerSeries.C (conjugateResidueConstant * ψc) * (Gψ * Fψ) * Fφ := by
          ring
    _ = PowerSeries.C (dominantResidueConstant * φc) * Fψ +
          PowerSeries.C (conjugateResidueConstant * ψc) * Fφ := by
        rw [hφgeom, hψgeom]
        ring
    _ = PowerSeries.C ((dominantResidueConstant * φc) +
            (conjugateResidueConstant * ψc)) -
          PowerSeries.C ((dominantResidueConstant * φc) * ψc +
            (conjugateResidueConstant * ψc) * φc) * PowerSeries.X := by
        rw [map_add, map_mul, map_mul]
        simp [Fφ, Fψ]
        ring_nf
    _ = 1 := by
        rw [← rho_inv, ← otherRoot_inv]
        rw [dominantCoeff_add_conjugateCoeff, crossCoeff_zero_inv]
        simp

/-- Partial-fraction decomposition into the dominant principal part plus the
analytic non-dominant remainder. -/
theorem fibonacciOGFℂ_eq_principal_add_remainder :
    fibonacciOGFℂ = dominantPrincipal + remainder := by
  rw [fibonacciOGFℂ]
  symm
  exact (PowerSeries.eq_inv_iff_mul_eq_one denominator_constantCoeff_ne_zero).2
    principal_add_remainder_mul_denominator

lemma coeff_remainder (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n remainder =
      conjugateResidueConstant * otherRoot⁻¹ ^ (n + 1) := by
  rw [remainder, conjugatePrincipal, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale_invUnitsSub_one]
  rw [pow_succ]
  ring

lemma psi_norm : ‖ψc‖ = -Real.goldenConj := by
  have hnonneg : 0 ≤ -Real.goldenConj := by
    linarith [Real.goldenConj_neg]
  calc
    ‖ψc‖ = ‖((-Real.goldenConj : ℝ) : ℂ)‖ := by
      rw [← norm_neg]
      simp
    _ = -Real.goldenConj := Complex.norm_of_nonneg hnonneg

lemma psi_norm_lt_one : ‖ψc‖ < 1 := by
  rw [psi_norm]
  linarith [Real.neg_one_lt_goldenConj]

/-- The non-dominant contribution is analytic past radius `1`. -/
theorem remainder_radius_gt_one :
    ENNReal.ofReal (1 : ℝ) < (PowerSeries.toFMLS remainder).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := PowerSeries.toFMLS remainder
  have hO :
      (fun n : ℕ => ‖p n‖ * (1 : ℝ) ^ n) =O[atTop]
        (fun n : ℕ => ‖ψc‖ ^ n) := by
    refine isBigO_of_le' (l := atTop)
      (c := ‖conjugateResidueConstant‖ * ‖ψc‖) ?_
    intro n
    have hp_norm : ‖p n‖ = ‖conjugateResidueConstant * ψc ^ (n + 1)‖ := by
      calc
        ‖p n‖ = ‖p.coeff n‖ := by
          simp [p, PowerSeries.toFMLS]
        _ = ‖PowerSeries.coeff (R := ℂ) n remainder‖ := by
          simp [p]
        _ = ‖conjugateResidueConstant * ψc ^ (n + 1)‖ := by
          rw [coeff_remainder, otherRoot_inv]
    have hleft : ‖p n‖ * (1 : ℝ) ^ n =
        (‖conjugateResidueConstant‖ * ‖ψc‖) * ‖ψc‖ ^ n := by
      rw [one_pow, mul_one, hp_norm, norm_mul, norm_pow]
      rw [pow_succ]
      ring
    rw [hleft]
    simp
  have hpsi_interval : ‖ψc‖ ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le (by norm_num) (norm_nonneg ψc)
    · exact psi_norm_lt_one
  have hstrict : ((1 : ℝ≥0) : ℝ≥0∞) < p.radius :=
    p.lt_radius_of_isBigO (r := (1 : ℝ≥0)) one_ne_zero hpsi_interval hO
  simpa [p] using hstrict

/-- Meromorphic transfer at the dominant simple pole. -/
theorem coeff_fibonacciOGFℂ_isEquivalent :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n fibonacciOGFℂ)
      ~[atTop] (fun n : ℕ => dominantResidueConstant * rho⁻¹ ^ (n + 1)) := by
  exact dominant_simplePole_isEquivalent
    fibonacciOGFℂ remainder (ρ := rho) (c := dominantResidueConstant) (R := (1 : ℝ))
    rho_norm_pos rho_norm_lt_one dominantResidueConstant_ne_zero remainder_radius_gt_one
    (by simpa [dominantPrincipal] using fibonacciOGFℂ_eq_principal_add_remainder)

/-- Shifted Fibonacci numbers have the dominant-pole asymptotic
`(1 / sqrt 5) * rho^{-n-1}`. -/
theorem fibonacciCompositionCount_isEquivalent_rho :
    (fun n : ℕ => (fibonacciCompositionCount n : ℂ))
      ~[atTop] (fun n : ℕ => dominantResidueConstant * rho⁻¹ ^ (n + 1)) := by
  have hEq :
      (fun n : ℕ => (fibonacciCompositionCount n : ℂ)) =ᶠ[atTop]
        (fun n : ℕ => PowerSeries.coeff (R := ℂ) n fibonacciOGFℂ) :=
    Eventually.of_forall fun n => (coeff_fibonacciOGFℂ n).symm
  exact hEq.trans_isEquivalent coeff_fibonacciOGFℂ_isEquivalent

/-- Shifted Fibonacci numbers have the usual `phi^{n+1} / sqrt 5` asymptotic. -/
theorem fibonacciCompositionCount_isEquivalent_phi :
    (fun n : ℕ => (fibonacciCompositionCount n : ℂ))
      ~[atTop] (fun n : ℕ => φc ^ (n + 1) / √5c) := by
  exact fibonacciCompositionCount_isEquivalent_rho.trans_eventuallyEq
    (Eventually.of_forall fun n => by
      rw [dominantResidueConstant, rho_inv]
      ring)

/-- The same asymptotic stated directly for `Nat.fib (n + 1)`. -/
theorem natFib_succ_isEquivalent_phi :
    (fun n : ℕ => (Nat.fib (n + 1) : ℂ))
      ~[atTop] (fun n : ℕ => φc ^ (n + 1) / √5c) := by
  simpa [fibonacciCompositionCount] using fibonacciCompositionCount_isEquivalent_phi

end FibonacciCompositionsNS
end Meromorphic
end Ch5
end AnalyticCombinatorics
