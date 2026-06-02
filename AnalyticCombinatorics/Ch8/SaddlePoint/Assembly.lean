import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
import Mathlib

/-!
# Saddle-point assembly bricks

This file contains the exact Cauchy parameterization on `[-pi, pi]` and the
bounded algebraic assembly theorem for a central/tail saddle decomposition.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal

noncomputable section

/-- The unnormalized Cauchy integrand after the circle parameterization. -/
def saddleRawIntegrand (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  f ((r : ℂ) * Complex.exp (θ * Complex.I)) * Complex.exp (-(↑↑n * ↑θ) * Complex.I)

/-- The normalized saddle integrand at a fixed radius. -/
def saddleGAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ) *
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)

/-- The saddle prefactor at a fixed radius. -/
def saddlePrefAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  f (r : ℂ) / (r : ℂ) ^ n

/-- The full normalized integral at a fixed radius. -/
def saddleJfullAt (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ

/-- The central normalized integral at a fixed radius and window. -/
def saddleJcAt (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-δ)..δ, saddleGAt f r n θ

/-- The two tail arcs at a fixed radius and window. -/
def saddleJtAt (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ *
    ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
      ∫ θ in δ..Real.pi, saddleGAt f r n θ)

/-- Sequence version of the normalized saddle integrand. -/
def saddleG (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  saddleGAt f (r n) n θ

/-- Sequence version of the saddle prefactor. -/
def saddlePref (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddlePrefAt f (r n) n

/-- Sequence version of the full normalized integral. -/
def saddleJfull (f : ℂ → ℂ) (r : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJfullAt f (r n) n

/-- Sequence version of the central normalized integral. -/
def saddleJc (f : ℂ → ℂ) (r δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJcAt f (r n) (δ n) n

/-- Sequence version of the normalized tail arcs. -/
def saddleJt (f : ℂ → ℂ) (r δ : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddleJtAt f (r n) (δ n) n

/-- The final saddle scale `f(r_n)/(r_n^n sqrt(2*pi*B_n))`. -/
def saddleScale (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ) : ℂ :=
  saddlePref f r n / (Real.sqrt (2 * Real.pi * B n) : ℂ)

private lemma saddlePhase_periodic (n : ℕ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * Complex.I))
      (2 * Real.pi) := by
  intro θ
  change Complex.exp (-(↑↑n * ↑(θ + 2 * Real.pi)) * Complex.I) =
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  rw [show -(↑↑n * ↑(θ + 2 * Real.pi)) * I =
      -(↑↑n * ↑θ) * I - ↑n * (2 * ↑Real.pi * I) by
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    norm_num
    ring_nf]
  exact Complex.exp_periodic.sub_nat_mul_eq n

private lemma saddleRawIntegrand_periodic (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    Function.Periodic (saddleRawIntegrand f r n) (2 * Real.pi) := by
  have hcircle0 :
      Function.Periodic (fun θ : ℝ => f (circleMap (0 : ℂ) r θ)) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp f
  have hcircle :
      Function.Periodic
        (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I))) (2 * Real.pi) := by
    simpa [circleMap_zero] using hcircle0
  exact hcircle.mul (saddlePhase_periodic n)

private lemma saddleRawIntegral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) =
      ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  have h := (saddleRawIntegrand_periodic f r n).intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

private lemma cauchyCircleIntegrand_param_eq
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) (θ : ℝ) :
    deriv (circleMap (0 : ℂ) r) θ •
      (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
        (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ)) =
    Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [saddleRawIntegrand, deriv_circleMap, circleMap_zero, smul_eq_mul, div_eq_mul_inv,
    mul_pow, Complex.exp_neg, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hrC, Complex.exp_ne_zero]
  rw [← Complex.exp_nat_mul]
  ring_nf

private lemma two_pi_I_inv_mul_I :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) = (2 * Real.pi : ℂ)⁻¹ := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have htwo : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  field_simp [hI, htwo]

/-- Cauchy's coefficient formula parameterized on the interval `[-pi, pi]`. -/
theorem coeff_eq_saddle_param
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  have hc := coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hr hp hd n
  rw [hc]
  rw [circleIntegral]
  have hcongr :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap (0 : ℂ) r) θ •
            (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
              (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ))) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact cauchyCircleIntegrand_param_eq f hr n θ
  rw [hcongr]
  rw [show (∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) =
        Complex.I * ((r : ℂ)⁻¹ ^ n) *
          ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ by
    calc
      (∫ θ in (0 : ℝ)..2 * Real.pi,
          Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
          = ∫ θ in (0 : ℝ)..2 * Real.pi,
              Complex.I * (((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
            apply intervalIntegral.integral_congr
            intro θ _
            ring
      _ = Complex.I *
            (∫ θ in (0 : ℝ)..2 * Real.pi,
              ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
            exact intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
              (μ := MeasureTheory.volume) (r := Complex.I)
              (f := fun θ => ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
      _ = Complex.I * (((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) := by
            exact congrArg (fun z : ℂ => Complex.I * z)
              (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                (μ := MeasureTheory.volume) (r := ((r : ℂ)⁻¹ ^ n))
                (f := fun θ => saddleRawIntegrand f r n θ))
      _ = Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ := by
            ring]
  rw [saddleRawIntegral_zero_to_neg_pi]
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (Complex.I * ((r : ℂ)⁻¹ ^ n) *
          ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
        =
          ((((2 * Real.pi : ℂ) * Complex.I)⁻¹) * Complex.I) *
            ((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
            simp [smul_eq_mul]
            ring
    _ = (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
          ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
            rw [two_pi_I_inv_mul_I]

private lemma saddleRawIntegrand_eq_const_mul_saddleGAt
    (f : ℂ → ℂ) {r : ℝ} (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) (θ : ℝ) :
    saddleRawIntegrand f r n θ = f (r : ℂ) * saddleGAt f r n θ := by
  simp [saddleRawIntegrand, saddleGAt, div_eq_mul_inv, mul_comm, mul_assoc]
  field_simp [hfnz]

/-- Cauchy's parameterization in normalized saddle-integral form. -/
theorem coeff_eq_saddle_param_normalized
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) :
    p.coeff n = saddlePrefAt f r n * saddleJfullAt f r n := by
  rw [coeff_eq_saddle_param hr hp hd n]
  have hraw :
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ) =
        f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          = ∫ θ in (-Real.pi)..Real.pi, f (r : ℂ) * saddleGAt f r n θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact saddleRawIntegrand_eq_const_mul_saddleGAt f hfnz n θ
      _ = f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
            exact intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
              (μ := MeasureTheory.volume) (r := f (r : ℂ)) (f := fun θ => saddleGAt f r n θ)
  rw [hraw]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [saddlePrefAt, saddleJfullAt]
  field_simp [hrC]

/-- Split the full normalized integral into central and tail pieces. -/
theorem saddleJfullAt_eq_saddleJcAt_add_saddleJtAt
    (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    saddleJfullAt f r n = saddleJcAt f r δ n + saddleJtAt f r δ n := by
  have h12 := intervalIntegral.integral_add_adjacent_intervals hleft hcenter
  have hfull := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hcenter) hright
  unfold saddleJfullAt saddleJcAt saddleJtAt
  rw [← hfull, ← h12]
  ring

/-- Exact coefficient split into the central window and the two tails. -/
theorem coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r δ : ℝ} {n : ℕ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    p.coeff n = saddlePrefAt f r n * (saddleJcAt f r δ n + saddleJtAt f r δ n) := by
  rw [coeff_eq_saddle_param_normalized hr hp hd hfnz n]
  rw [saddleJfullAt_eq_saddleJcAt_add_saddleJtAt f r δ n hleft hcenter hright]

/-- Eventual sequence version of the exact central/tail split. -/
theorem eventually_coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenter : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi) :
    ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n) := by
  filter_upwards [hr, hd, hfnz, hleft, hcenter, hright] with
    n hrn hdn hfnzn hleftn hcentern hrightn
  simpa [saddlePref, saddleJc, saddleJt, saddleG] using
    coeff_eq_saddle_split (f := f) (p := p) (r := r n) (δ := δ n) (n := n)
      hrn hp hdn hfnzn hleftn hcentern hrightn

/-- Assembly theorem from an exact central/tail split and normalized limits. -/
theorem coeff_isEquivalent_saddle_assembly
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (Hsplit : ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n))
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  let S : ℕ → ℂ := fun n => (Real.sqrt (2 * Real.pi * B n) : ℂ)
  have hratio :
      (fun n : ℕ => p.coeff n / saddleScale f r B n) =ᶠ[atTop]
        (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n)) := by
    filter_upwards [Hsplit, Hnz] with n hsplit hnz
    rw [hsplit]
    dsimp [S, saddleScale]
    have hS : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
      intro hzero
      apply hnz
      simp [hzero, saddleScale]
    have hpref : saddlePref f r n ≠ 0 := by
      intro hpref_zero
      apply hnz
      simp [hpref_zero, saddleScale]
    field_simp [hpref, hS]
  have hsum :
      Tendsto (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n))
        atTop (𝓝 1) := by
    have hadd :
        Tendsto
          (fun n : ℕ =>
            S n * saddleJc f r δ n + S n * saddleJt f r δ n) atTop (𝓝 1) := by
      simpa [S] using Hcentral.add Htail
    refine Tendsto.congr' ?_ hadd
    exact Eventually.of_forall fun n => by
      dsimp [S]
      ring
  exact Tendsto.congr' hratio.symm hsum

/--
Assembly theorem with the exact split discharged from the Cauchy parameterization
and interval additivity.
-/
theorem coeff_isEquivalent_saddle_assembly_of_cauchy
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenterInt : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) :=
  coeff_isEquivalent_saddle_assembly r B δ
    (eventually_coeff_eq_saddle_split r δ hp hr hd hfnz hleft hcenterInt hright)
    Hcentral Htail Hnz
