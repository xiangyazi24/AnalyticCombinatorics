import Mathlib

/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

noncomputable section

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The real inner product on `R` is multiplication. -/
lemma real_inner_eq_mul (a b : ℝ) : (inner ℝ a b : ℝ) = a * b := by
  conv_lhs =>
    rw [show a = a • (1 : ℝ) by simp, show b = b • (1 : ℝ) by simp]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  norm_num

/-- Characteristic function of a centered and scaled real random variable. -/
lemma charFun_map_center_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X P) (μ σ t : ℝ) :
    charFun (P.map fun ω => (X ω - μ) / σ) t =
      charFun (P.map X) (σ⁻¹ * t) *
        Complex.exp (((-μ) * (σ⁻¹ * t) : ℝ) * Complex.I) := by
  rw [show (fun ω => (X ω - μ) / σ) = fun ω => σ⁻¹ * (X ω - μ) by
    funext ω
    ring]
  rw [charFun_map_mul_comp (hX.sub aemeasurable_const) σ⁻¹ t]
  rw [show (fun ω => X ω - μ) = (fun x : ℝ => x + (-μ)) ∘ X by rfl]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ℝ => x + (-μ)) (P.map X)) hX]
  rw [charFun_map_add_const]
  rw [real_inner_eq_mul]

/-- The real scale identity behind the quasi-powers normalization. -/
lemma quasiPower_scale_sq {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 = t ^ 2 := by
  have hsq : (Real.sqrt (β * u₂)) ^ 2 = β * u₂ := by
    rw [Real.sq_sqrt]
    positivity
  have hs_ne : (Real.sqrt (β * u₂) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hβ hu₂)
  field_simp [pow_two, hs_ne]
  rw [hsq]

/-- The quadratic term in the normalized quasi-powers exponent tends to the Gaussian exponent. -/
lemma quasiPower_quadratic_term {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2) =
      - (t : ℂ) ^ 2 / 2 := by
  have hscale := quasiPower_scale_sq (β := β) (u₂ := u₂) (t := t) hβ hu₂
  calc
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2)
        = - (((β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 : ℝ) : ℂ)) / 2 := by
          rw [show
            (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 =
              - ((((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ) ^ 2) by
            rw [pow_two]
            calc
              (Complex.I * ↑((√(β * u₂))⁻¹ * t)) *
                  (Complex.I * ↑((√(β * u₂))⁻¹ * t))
                  = (Complex.I * Complex.I) *
                      (↑((√(β * u₂))⁻¹ * t) * ↑((√(β * u₂))⁻¹ * t)) := by
                    ring
              _ = -↑((√(β * u₂))⁻¹ * t) ^ 2 := by
                    rw [Complex.I_mul_I]
                    ring]
          norm_num
          ring
    _ = - (t : ℂ) ^ 2 / 2 := by
          rw [hscale]
          norm_num

/-- The centering cancels the linear term of the quasi-powers exponent. -/
lemma quasiPower_linear_cancel {β u₁ u₂ t : ℝ} :
    (β : ℂ) *
        ((u₁ : ℂ) * (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ))) +
      (((-(β * u₁)) * ((Real.sqrt (β * u₂))⁻¹ * t) : ℝ) : ℂ) * Complex.I = 0 := by
  norm_num
  ring

/-- The normalized quasi-powers exponent reduces to the Gaussian exponent plus remainders. -/
lemma quasiPower_exponent_eq {β u₁ u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂)
    (r v : ℂ) :
    let z : ℂ := Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)
    (β : ℂ) * ((u₁ : ℂ) * z + (u₂ : ℂ) * z ^ 2 / 2 + r) + v +
        (((-(β * u₁)) * ((Real.sqrt (β * u₂))⁻¹ * t) : ℝ) : ℂ) * Complex.I =
      - (t : ℂ) ^ 2 / 2 + (β : ℂ) * r + v := by
  dsimp
  have hlin := quasiPower_linear_cancel (β := β) (u₁ := u₁) (u₂ := u₂) (t := t)
  have hquad := quasiPower_quadratic_term (β := β) (u₂ := u₂) (t := t) hβ hu₂
  calc
    (β : ℂ) * ((u₁ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) +
          (u₂ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) ^ 2 / 2 + r) + v +
        ↑(-(β * u₁) * ((√(β * u₂))⁻¹ * t)) * I
        = ((β : ℂ) * ((u₁ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t))) +
            ↑(-(β * u₁) * ((√(β * u₂))⁻¹ * t)) * I) +
          (β : ℂ) * ((u₂ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) ^ 2 / 2) +
          (β : ℂ) * r + v := by
            ring
    _ = - (t : ℂ) ^ 2 / 2 + (β : ℂ) * r + v := by
          rw [hlin, hquad]
          ring

/-- The imaginary scaling point used by the normalized characteristic functions. -/
def qpZ (β : ℕ → ℝ) (u₂ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.I * (((Real.sqrt (β n * u₂))⁻¹ * t : ℝ) : ℂ)

/-- If `β_n -> infinity`, then each fixed scaled imaginary point tends to zero. -/
lemma quasiPower_scaledArgument_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂) :
    Tendsto (fun n => qpZ β u₂ n t) atTop (𝓝 0) := by
  have hprod : Tendsto (fun n => β n * u₂) atTop atTop := hβ.atTop_mul_const hu₂
  have hreal : Tendsto (fun n => (Real.sqrt (β n * u₂))⁻¹ * t) atTop (𝓝 0) := by
    simpa using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hprod)).mul_const t
  simpa [qpZ] using hreal.ofReal.const_mul Complex.I

/-- A continuous analytic prefactor with value `0` at the origin is negligible after scaling. -/
lemma quasiPower_V_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ} {V : ℂ → ℂ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hV : ContinuousAt V 0) (hV0 : V 0 = 0) :
    Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0) := by
  simpa [hV0] using
    hV.tendsto.comp (quasiPower_scaledArgument_tendsto_zero
      (β := β) (u₂ := u₂) (t := t) hβ hu₂)

/-- The expectation is the first derivative of the cumulant-generating function at zero. -/
lemma expectation_eq_deriv_cgf_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    μ[X] = deriv (cgf X μ) 0 := by
  have h' := (deriv_cgf_zero (X := X) (μ := μ) h).symm
  simpa using h'

/-- The variance is the second derivative of the cumulant-generating function at zero. -/
lemma variance_eq_iteratedDeriv_two_cgf_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h : 0 ∈ interior (integrableExpSet X μ)) :
    Var[X; μ] = iteratedDeriv 2 (cgf X μ) 0 := by
  simpa using (variance_tilted_mul (X := X) (μ := μ) (t := 0) h)

section MomentExtraction

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β ε₁ ε₂ : ℕ → ℝ} {u₁ u₂ : ℝ}

/-- If the first cgf derivative has quasi-powers main term plus bounded error,
then the expectations have the corresponding `O(1)` asymptotic. -/
theorem expectation_sub_quasiPowerCoeff_isBigO
    (hint : ∀ n, 0 ∈ interior (integrableExpSet (X n) (P n)))
    (hderiv : ∀ n, deriv (cgf (X n) (P n)) 0 = β n * u₁ + ε₁ n)
    (hε : ε₁ =O[atTop] fun _ : ℕ => (1 : ℝ)) :
    (fun n => (P n)[X n] - β n * u₁) =O[atTop] fun _ : ℕ => (1 : ℝ) := by
  have hEq : (fun n => (P n)[X n] - β n * u₁) = ε₁ := by
    funext n
    have hm := expectation_eq_deriv_cgf_zero (X := X n) (μ := P n) (hint n)
    rw [hm, hderiv n]
    ring
  simpa [hEq] using hε

/-- If the second cgf derivative has quasi-powers main term plus bounded error,
then the variances have the corresponding `O(1)` asymptotic. -/
theorem variance_sub_quasiPowerCoeff_isBigO
    (hint : ∀ n, 0 ∈ interior (integrableExpSet (X n) (P n)))
    (hderiv : ∀ n, iteratedDeriv 2 (cgf (X n) (P n)) 0 = β n * u₂ + ε₂ n)
    (hε : ε₂ =O[atTop] fun _ : ℕ => (1 : ℝ)) :
    (fun n => Var[X n; P n] - β n * u₂) =O[atTop] fun _ : ℕ => (1 : ℝ) := by
  have hEq : (fun n => Var[X n; P n] - β n * u₂) = ε₂ := by
    funext n
    have hv := variance_eq_iteratedDeriv_two_cgf_zero (X := X n) (μ := P n) (hint n)
    rw [hv, hderiv n]
    ring
  simpa [hEq] using hε

end MomentExtraction

section QuasiPowers

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)}
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}

/-- Quasi-powers expansion on the imaginary axis implies normalized characteristic functions
converge pointwise to the standard Gaussian characteristic function. -/
theorem quasiPowers_charFun_tendsto
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβpos : ∀ n, 0 < β n) (hu₂ : 0 < u₂)
    (hChar : ∀ n s,
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0))
    (hV : ∀ t, Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0)) :
    ∀ t, Tendsto
      (fun n => charFun ((P n).map fun ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) t)
      atTop (𝓝 (Complex.exp (- (t : ℂ) ^ 2 / 2))) := by
  intro t
  have hEq :
      (fun n =>
        charFun ((P n).map fun ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) t) =
        fun n => Complex.exp
          (- (t : ℂ) ^ 2 / 2 + (β n : ℂ) * R n (qpZ β u₂ n t) +
            V (qpZ β u₂ n t)) := by
    funext n
    rw [charFun_map_center_div (hX n) (β n * u₁) (Real.sqrt (β n * u₂)) t]
    rw [hChar n ((Real.sqrt (β n * u₂))⁻¹ * t)]
    rw [← Complex.exp_add]
    unfold qpZ
    rw [quasiPower_exponent_eq
      (β := β n) (u₁ := u₁) (u₂ := u₂) (t := t) (hβpos n) hu₂]
  rw [hEq]
  have harg :
      Tendsto
        (fun n => - (t : ℂ) ^ 2 / 2 + (β n : ℂ) * R n (qpZ β u₂ n t) +
          V (qpZ β u₂ n t)) atTop
        (𝓝 (- (t : ℂ) ^ 2 / 2)) := by
    simpa [add_assoc] using (tendsto_const_nhds.add ((hR t).add (hV t)))
  simpa using harg.cexp

/-- Version of `quasiPowers_charFun_tendsto` where the analytic prefactor is discharged from
continuity at zero and `β_n -> infinity`. -/
theorem quasiPowers_charFun_tendsto_of_continuousAt
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβpos : ∀ n, 0 < β n) (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hVcont : ContinuousAt V 0) (hV0 : V 0 = 0)
    (hChar : ∀ n s,
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0)) :
    ∀ t, Tendsto
      (fun n => charFun ((P n).map fun ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) t)
      atTop (𝓝 (Complex.exp (- (t : ℂ) ^ 2 / 2))) :=
  quasiPowers_charFun_tendsto (P := P) (X := X) (β := β) (u₁ := u₁) (u₂ := u₂)
    (R := R) (V := V) hX hβpos hu₂ hChar hR
    (fun t => quasiPower_V_tendsto_zero (β := β) (u₂ := u₂) (t := t)
      hβ hu₂ hVcont hV0)

variable [∀ n, IsProbabilityMeasure (P n)]

/-- The Mathlib-supported core quasi-powers theorem: characteristic-function convergence from the
logarithmic expansion implies convergence in distribution to `gaussianReal 0 1`. -/
theorem quasiPowers_tendstoInDistribution
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβpos : ∀ n, 0 < β n) (hu₂ : 0 < u₂)
    (hChar : ∀ n s,
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0))
    (hV : ∀ t, Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) where
  forall_aemeasurable n := by fun_prop
  aemeasurable_limit := by fun_prop
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
    intro t
    have hcf := quasiPowers_charFun_tendsto (P := P) (X := X) (β := β)
      (u₁ := u₁) (u₂ := u₂) (R := R) (V := V) hX hβpos hu₂ hChar hR hV t
    simpa [charFun_gaussianReal, neg_div] using hcf

/-- Final form with `V` discharged by continuity at zero and `β_n -> infinity`. -/
theorem quasiPowers_tendstoInDistribution_of_continuousAt
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβpos : ∀ n, 0 < β n) (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hVcont : ContinuousAt V 0) (hV0 : V 0 = 0)
    (hChar : ∀ n s,
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) :=
  quasiPowers_tendstoInDistribution (P := P) (X := X) (β := β)
    (u₁ := u₁) (u₂ := u₂) (R := R) (V := V) hX hβpos hu₂ hChar hR
    (fun t => quasiPower_V_tendsto_zero (β := β) (u₂ := u₂) (t := t)
      hβ hu₂ hVcont hV0)

end QuasiPowers

end LimitLaws
end Ch9
end AnalyticCombinatorics
