import AnalyticCombinatorics.Ch8.SaddlePoint.Bound
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

open Complex
open scoped NNReal ENNReal

noncomputable section

def expCarrier : PowerSeries ℂ := PowerSeries.exp ℂ

@[simp] theorem expCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n expCarrier = ((1 : ℝ) / n.factorial : ℂ) := by
  simp [expCarrier]

def expCarrier_nonneg : NonnegRealCoeff expCarrier where
  coeffR := fun n => (1 : ℝ) / n.factorial
  coeff_nonneg := by
    intro n
    positivity
  coeff_eq := by
    intro n
    simp

theorem expCarrier_toFMLS_eq_expSeries :
    PowerSeries.toFMLS expCarrier = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, expCarrier]

@[simp] theorem expCarrier_radius :
    (PowerSeries.toFMLS expCarrier).radius = ⊤ := by
  rw [expCarrier_toFMLS_eq_expSeries]
  exact NormedSpace.expSeries_radius_eq_top ℂ ℂ

theorem expCarrier_radius_pos :
    0 < (PowerSeries.toFMLS expCarrier).radius := by
  rw [expCarrier_radius]
  exact WithTop.top_pos

theorem expCarrier_mem_eball_of_real (r : ℝ) :
    (r : ℂ) ∈ Metric.eball 0 (PowerSeries.toFMLS expCarrier).radius := by
  simp [expCarrier_radius]

theorem expCarrier_analyticSum_eq_exp (z : ℂ) :
    PowerSeries.analyticSum expCarrier z = Complex.exp z := by
  calc
    PowerSeries.analyticSum expCarrier z = (NormedSpace.expSeries ℂ ℂ).sum z := by
      simp [PowerSeries.analyticSum, expCarrier_toFMLS_eq_expSeries]
    _ = NormedSpace.exp z := by
      exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
    _ = Complex.exp z := by
      exact (congrFun Complex.exp_eq_exp_ℂ z).symm

theorem expCarrier_analyticSum_re (r : ℝ) :
    (PowerSeries.analyticSum expCarrier (r : ℂ)).re = Real.exp r := by
  rw [expCarrier_analyticSum_eq_exp]
  rw [← Complex.ofReal_exp r, Complex.ofReal_re]

theorem expCarrier_differentiableOn (R : ℝ) :
    DifferentiableOn ℂ (PowerSeries.analyticSum expCarrier) (Metric.closedBall 0 R) := by
  have hfun : PowerSeries.analyticSum expCarrier = Complex.exp := by
    funext z
    exact expCarrier_analyticSum_eq_exp z
  rw [hfun]
  exact Complex.differentiable_exp.differentiableOn

theorem expCarrier_norm_coeff (n : ℕ) :
    ‖PowerSeries.coeff (R := ℂ) n expCarrier‖ = (1 : ℝ) / n.factorial := by
  simp

theorem inv_factorial_le_exp_div_pow {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (1 : ℝ) / n.factorial ≤ Real.exp r / r ^ n := by
  have hbound :=
    PowerSeries.norm_coeff_le_analyticSum_of_nonneg expCarrier_nonneg hr
      expCarrier_radius_pos (expCarrier_mem_eball_of_real r)
      (expCarrier_differentiableOn r) n
  calc
    (1 : ℝ) / n.factorial = ‖PowerSeries.coeff (R := ℂ) n expCarrier‖ := by
      rw [expCarrier_norm_coeff]
    _ ≤ (PowerSeries.analyticSum expCarrier (r : ℂ)).re * r⁻¹ ^ n := hbound
    _ = Real.exp r * r⁻¹ ^ n := by rw [expCarrier_analyticSum_re]
    _ = Real.exp r / r ^ n := by
      rw [inv_pow]
      ring

theorem inv_factorial_le_exp_nat_div_pow_self {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / n.factorial ≤ Real.exp n / (n : ℝ) ^ n := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  simpa using inv_factorial_le_exp_div_pow (n := n) (r := (n : ℝ)) hnreal
