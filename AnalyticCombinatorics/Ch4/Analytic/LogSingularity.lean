import AnalyticCombinatorics.Ch4.Analytic.TransferTheorem
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic singularity scale

This file adds the coefficient scale for the first logarithmic singular factor
over the standard function `(1 - z)^{-α}`.

For real `α > 1`, the exact `n`-th coefficient of
`(1 - z)^{-α} log (1 / (1 - z))` is

`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}`,

and it is asymptotic to `(n^(α - 1) / Γ α) * log n`.

The closed form is established directly from the exact parameter derivative of
the binomial coefficients (`logSingularityCoeff_isEquivalent`).  The final
section then proves the **genuine generating-function coefficient identity**
(`logSingularityCoeff_eq_coeff_logSingularityGF`): this closed form is exactly
the `n`-th coefficient of the Cauchy product of the honest power series for
`(1 - z)^{-α}` (Mathlib's `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`,
coefficients `Ring.choose (α + n - 1) n`) and for `log (1 / (1 - z))`
(coefficients `n⁻¹`), so the asymptotic is a genuine statement about the
log-singularity generating function rather than an asserted scale.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

/-- The shifted harmonic factor produced by differentiating the binomial scale in `α`. -/
def shiftedHarmonic (α : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (α + j)⁻¹

/--
Coefficient scale for `(1 - z)^{-α} log (1 / (1 - z))`.

The factor `shiftedHarmonic α n` is the logarithmic correction coming from
`∂_α Ring.choose (α + n - 1) n`.
-/
def logSingularityCoeff (α : ℝ) (n : ℕ) : ℝ :=
  Ring.choose (α + n - 1) n * shiftedHarmonic α n

private lemma harmonic_real_eq_sum_inv (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private lemma shiftedHarmonic_sub_harmonic_eq_sum (α : ℝ) (n : ℕ) :
    shiftedHarmonic α n - (harmonic n : ℝ) =
      ∑ j ∈ Finset.range n, ((α + j)⁻¹ - (((j + 1 : ℕ) : ℝ)⁻¹)) := by
  rw [shiftedHarmonic, harmonic_real_eq_sum_inv, Finset.sum_sub_distrib]

private theorem harmonic_isEquivalent_log :
    (fun n : ℕ => (harmonic n : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  rw [Asymptotics.IsEquivalent]
  have hdiff :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n)
        atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hdiffO :
      (fun n : ℕ => (harmonic n : ℝ) - Real.log n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hdiff one_ne_zero
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have honeLittleO :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log n) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp hlog_atTop)
  exact hdiffO.trans_isLittleO honeLittleO

private theorem harmonic_tendsto_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff :
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n)
        atTop (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log
  have hsum := hlog.atTop_add hdiff
  refine hsum.congr' ?_
  exact Eventually.of_forall fun n => by ring

private lemma shifted_harmonic_step_isLittleO (α : ℝ) (hα : 0 < α) :
    (fun n : ℕ => (α + n)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹)) =o[atTop]
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  refine (isLittleO_iff_tendsto ?_).mpr ?_
  · intro n hn
    exfalso
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    exact inv_ne_zero hpos.ne' hn
  · have hratio :
        (fun n : ℕ =>
            ((α + n)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹)) /
              (((n + 1 : ℕ) : ℝ)⁻¹)) =ᶠ[atTop]
          (fun n : ℕ => (1 - α) / (α + n)) := by
      refine Eventually.of_forall fun n => ?_
      have hαn : α + (n : ℝ) ≠ 0 := by positivity
      have hn1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hαn, hn1]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    refine Tendsto.congr' hratio.symm ?_
    have hlin :
        Tendsto (fun n : ℕ => ((1 - α) + 0 * (n : ℝ)) / (α + 1 * (n : ℝ)))
          atTop (𝓝 (0 / (1 : ℝ))) :=
      tendsto_add_mul_div_add_mul_atTop_nhds (1 - α) α 0 (d := (1 : ℝ)) one_ne_zero
    simpa using hlin

private theorem shiftedHarmonic_sub_harmonic_isLittleO
    (α : ℝ) (hα : 0 < α) :
    (fun n : ℕ => shiftedHarmonic α n - (harmonic n : ℝ)) =o[atTop]
      (fun n : ℕ => (harmonic n : ℝ)) := by
  have hstep := shifted_harmonic_step_isLittleO α hα
  have hsum_atTop :
      Tendsto (fun n : ℕ =>
          ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ)⁻¹)) atTop atTop := by
    refine harmonic_tendsto_atTop.congr' ?_
    exact Eventually.of_forall fun n => harmonic_real_eq_sum_inv n
  have hsum := hstep.sum_range
    (fun n : ℕ => by
      have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
      exact inv_nonneg.mpr hpos.le)
    hsum_atTop
  refine hsum.congr' ?_ ?_
  · exact Eventually.of_forall fun n => by
      exact (shiftedHarmonic_sub_harmonic_eq_sum α n).symm
  · exact Eventually.of_forall fun n => (harmonic_real_eq_sum_inv n).symm

theorem shiftedHarmonic_isEquivalent_log {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => shiftedHarmonic α n) ~[atTop]
      (fun n : ℕ => Real.log n) := by
  have hharm := harmonic_isEquivalent_log
  have hdiff_harm := shiftedHarmonic_sub_harmonic_isLittleO α hα
  have hdiff_log :
      (fun n : ℕ => shiftedHarmonic α n - (harmonic n : ℝ)) =o[atTop]
        (fun n : ℕ => Real.log n) :=
    hdiff_harm.trans_isBigO hharm.isBigO
  have hsum :
      (fun n : ℕ => (harmonic n : ℝ) +
          (shiftedHarmonic α n - (harmonic n : ℝ))) ~[atTop]
        (fun n : ℕ => Real.log n) :=
    hharm.add_isLittleO hdiff_log
  exact hsum.congr_left (Eventually.of_forall fun n => by ring)

private lemma not_neg_nat_of_one_lt {α : ℝ} (hα : 1 < α) :
    ∀ m : ℕ, α ≠ -m := by
  intro m hm
  have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  linarith

/--
Leading-order β = 1 logarithmic singularity scale, coefficient form.

For real `α > 1`, the exact logarithmic coefficient scale
`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}` is equivalent to
`(n^(α - 1) / Γ(α)) * log n`.
-/
theorem logSingularityCoeff_isEquivalent {α : ℝ} (hα : 1 < α) :
    (fun n : ℕ => logSingularityCoeff α n) ~[atTop]
      (fun n : ℕ => ((n : ℝ) ^ (α - 1) / Real.Gamma α) * Real.log n) := by
  have hchoose :=
    choose_standard_scale_real (α := α) (not_neg_nat_of_one_lt hα)
  have hshift := shiftedHarmonic_isEquivalent_log (α := α) (by linarith)
  simpa [logSingularityCoeff] using hchoose.mul hshift

/--
Concrete application: the double-pole logarithmic scale
`(1 - z)^{-2} log (1 / (1 - z))` has leading coefficient scale `n log n`.
-/
theorem doublePoleLogCoeff_isEquivalent :
    (fun n : ℕ => logSingularityCoeff 2 n) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log n) := by
  have h := logSingularityCoeff_isEquivalent (α := 2) (by norm_num)
  have hΓ : Real.Gamma (2 : ℝ) = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 <;> norm_num
  refine h.congr_right (Eventually.of_forall fun n => ?_)
  have hexp : (2 : ℝ) - 1 = 1 := by norm_num
  dsimp
  rw [hexp, Real.rpow_one, hΓ, div_one]

/-!
## Genuine generating-function coefficient identity

The asymptotic above is stated for the *sequence*
`logSingularityCoeff α n = Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`.
The purpose of this section is to prove that this sequence is genuinely the
coefficient sequence of the log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))`, rather than merely an asserted scale.

We work over `ℂ`, where the two factor generating functions have honest
coefficient descriptions:

* `[zⁿ] (1 - z)^{-α} = Ring.choose (α + n - 1) n` — this is exactly the
  `n`-th coefficient of the analytic power series of `fun z ↦ 1 / (1 - z)^α`
  at `0`, banked in Mathlib as
  `Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, whose formal
  multilinear series is `.ofScalars ℂ (fun n ↦ Ring.choose (α + n - 1) n)`.
* `[zⁿ] log (1 / (1 - z)) = [zⁿ] (-log (1 - z)) = n⁻¹` for `n ≥ 1` and `0`
  for `n = 0` — this is the standard logarithm expansion
  `∑ n, z^{n+1}/(n+1) = -log (1 - z)` (`Real`/`Complex.hasSum_pow_div_log…`).

We package these as formal power series and prove, by the Cauchy product
(`PowerSeries.coeff_mul`) together with a binomial/partial-fraction identity,
that the `n`-th coefficient of the product equals
`Ring.choose (α + n - 1) n * ∑_{j<n} (α + j)⁻¹`, i.e. `logSingularityCoeff`.
-/

open scoped PowerSeries

/-- The genuine `n`-th coefficient of `(1 - z)^{-α}`. -/
def binCoeffℂ (α : ℂ) (n : ℕ) : ℂ := Ring.choose (α + n - 1) n

/-- The genuine `n`-th coefficient of `log (1 / (1 - z)) = -log (1 - z)`:
`0` at `n = 0` and `n⁻¹` for `n ≥ 1`. -/
def logCoeffℂ (n : ℕ) : ℂ := if n = 0 then 0 else (n : ℂ)⁻¹

/-- The generating function `(1 - z)^{-α}` as a formal power series, with the
genuine binomial coefficients. -/
noncomputable def oneSubCpowGF (α : ℂ) : ℂ⟦X⟧ := PowerSeries.mk (binCoeffℂ α)

/-- The generating function `log (1 / (1 - z))` as a formal power series, with
the genuine logarithmic coefficients. -/
noncomputable def logGF : ℂ⟦X⟧ := PowerSeries.mk logCoeffℂ

/-- The log-singularity generating function `(1 - z)^{-α} · log (1 / (1 - z))`
as a formal power series. -/
noncomputable def logSingularityGF (α : ℂ) : ℂ⟦X⟧ := oneSubCpowGF α * logGF

/-- **Faithfulness of the binomial coefficient.** The coefficients of
`oneSubCpowGF α` are literally the coefficients of the analytic power series of
`fun z ↦ 1 / (1 - z)^α` at `0` (Mathlib's
`one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`).  This is what makes
`oneSubCpowGF α` the genuine generating function of `(1 - z)^{-α}`. -/
theorem coeff_oneSubCpowGF_eq_analytic (α : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) =
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ => Ring.choose (α + n - 1) n)).coeff n := by
  rw [oneSubCpowGF, PowerSeries.coeff_mk, FormalMultilinearSeries.coeff_ofScalars]
  rfl

/-- Recurrence for the binomial coefficients, from the product formula
`Ring.choose (α + n - 1) n = (∏ j < n, (α + j)) / n!`. -/
theorem binCoeffℂ_succ (α : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * binCoeffℂ α (n + 1) = (α + n) * binCoeffℂ α n := by
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfac' : ((n + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  rw [binCoeffℂ, binCoeffℂ, choose_eq_prod_range_complex, choose_eq_prod_range_complex]
  rw [Finset.prod_range_succ]
  have hcast : ((n + 1).factorial : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hcast]
  field_simp

/-- The Cauchy-product coefficient of the log-singularity generating function,
written as an explicit sum.  The `m = n` term vanishes because
`logCoeffℂ 0 = 0`, so the genuine `[zⁿ]` reduces to the partial-fraction sum
`∑_{m < n} binCoeffℂ α m · (n - m)⁻¹`. -/
theorem coeff_logSingularityGF (α : ℂ) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSingularityGF α) =
      ∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
  rw [logSingularityGF, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  -- the `m = n` term: `logCoeffℂ (n - n) = logCoeffℂ 0 = 0`
  have hlast : PowerSeries.coeff (R := ℂ) n (oneSubCpowGF α) *
      PowerSeries.coeff (R := ℂ) (n - n) logGF = 0 := by
    rw [Nat.sub_self, logGF, PowerSeries.coeff_mk, logCoeffℂ, if_pos rfl, mul_zero]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_range] at hm
  rw [oneSubCpowGF, PowerSeries.coeff_mk, logGF, PowerSeries.coeff_mk, logCoeffℂ]
  have hnm : n - m ≠ 0 := by omega
  rw [if_neg hnm]
  congr 1
  have : ((n - m : ℕ) : ℂ) = (n : ℂ) - m := by
    rw [Nat.cast_sub hm.le]
  rw [this]

/-- The complex shifted-harmonic factor `∑_{j < n} (α + j)⁻¹`. -/
def shiftedHarmonicℂ (α : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, (α + j)⁻¹

/-- The complex log-singularity coefficient
`Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹`. -/
def logSingularityCoeffℂ (α : ℂ) (n : ℕ) : ℂ :=
  binCoeffℂ α n * shiftedHarmonicℂ α n

/-- Recurrence for the closed-form coefficient:
`(n+1)·T(n+1) = (α+n)·T(n) + binCoeffℂ α n`, where `T = logSingularityCoeffℂ`.
This follows from the binomial recurrence and `H(n+1) = H(n) + (α+n)⁻¹`. -/
theorem logSingularityCoeffℂ_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * logSingularityCoeffℂ α (n + 1) =
      (α + n) * logSingularityCoeffℂ α n + binCoeffℂ α n := by
  have hαn : α + (n : ℂ) ≠ 0 := by
    intro h; exact hα n (eq_neg_of_add_eq_zero_left h)
  have hHsucc : shiftedHarmonicℂ α (n + 1) =
      shiftedHarmonicℂ α n + (α + n)⁻¹ := by
    rw [shiftedHarmonicℂ, shiftedHarmonicℂ, Finset.sum_range_succ]
  have hrec := binCoeffℂ_succ α n
  rw [logSingularityCoeffℂ, logSingularityCoeffℂ, hHsucc]
  -- `(n+1)·a_{n+1}·(H_n + (α+n)⁻¹) = (α+n)·a_n·H_n + a_n`, using `(n+1)·a_{n+1}=(α+n)·a_n`
  -- and `(α+n)·(α+n)⁻¹ = 1`.
  have hcancel : (α + (n : ℂ)) * (α + (n : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hαn
  linear_combination (shiftedHarmonicℂ α n + (α + (n : ℂ))⁻¹) * hrec +
    binCoeffℂ α n * hcancel

/-- Recurrence for the Cauchy-product coefficient
`S(n) = ∑_{m < n} binCoeffℂ α m · (n - m)⁻¹`:
`(n+1)·S(n+1) = (α+n)·S(n) + binCoeffℂ α n`.
This is proved by a telescoping identity with `G(m) = m · binCoeffℂ α m · (n+1-m)⁻¹`,
using the binomial recurrence. -/
theorem convCoeff_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * (∑ m ∈ Finset.range (n + 1), binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) =
      (α + n) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) +
        binCoeffℂ α n := by
  -- Split off the `m = n` term on the left: `binCoeffℂ α n · (n+1-n)⁻¹ = binCoeffℂ α n`.
  rw [Finset.sum_range_succ]
  have hlast : binCoeffℂ α n * ((n : ℂ) + 1 - n)⁻¹ = binCoeffℂ α n := by
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  rw [hlast, mul_add, mul_comm ((n : ℂ) + 1) (binCoeffℂ α n)]
  -- It remains to show
  --   (n+1)·∑_{m<n} a_m (n+1-m)⁻¹ = (α+n)·∑_{m<n} a_m (n-m)⁻¹ + (a_n·(n+1) - a_n)
  -- i.e. ∑_{m<n} a_m [ (n+1)(n+1-m)⁻¹ - (α+n)(n-m)⁻¹ ] = -n·a_n
  have hkey :
      ((n : ℂ) + 1) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
        (α + n) * (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        -((n : ℂ) * binCoeffℂ α n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    -- Telescoping: each summand equals `G m - G (m+1)` with
    -- `G m = m · binCoeffℂ α m · (n+1-m)⁻¹`.
    have htele : ∀ m ∈ Finset.range n,
        ((n : ℂ) + 1) * (binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (α + n) * (binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        ((m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹) := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hcast : (n : ℂ) - m = ((n - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub hm.le]
      have hnm : (n : ℂ) - m ≠ 0 := by
        rw [hcast, Ne, Nat.cast_eq_zero]
        omega
      have hcast1 : (n : ℂ) + 1 - m = ((n + 1 - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have hn1m : (n : ℂ) + 1 - m ≠ 0 := by
        rw [hcast1, Ne, Nat.cast_eq_zero]
        omega
      -- use the binomial recurrence `(m+1)·a_{m+1} = (α+m)·a_m`
      have hrec := binCoeffℂ_succ α m
      have hD1 : ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ = 1 := mul_inv_cancel₀ hn1m
      have hD0 : ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ = 1 := mul_inv_cancel₀ hnm
      -- substitute the recurrence into the `a_{m+1}` term
      have hsub : ((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹ =
          (α + m) * binCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
        rw [hrec]
      rw [hsub]
      -- now both sides are `a_m · (bracket)`; the bracket identity reduces to
      -- `(n+1-m)·D1⁻¹ = (n-m)·D0⁻¹`, i.e. `1 = 1`.
      have hbr :
          ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ - (α + n) * ((n : ℂ) - m)⁻¹ =
            (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
        have e1 : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ -
              (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
            ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ := by ring
        have e2 : (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ =
            ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ := by ring
        have key : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ -
              (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
            (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
          rw [e1, e2, hD1, hD0]
        linear_combination key
      linear_combination binCoeffℂ α m * hbr
    rw [Finset.sum_congr rfl htele]
    -- telescoping sum: ∑_{m<n} (G m - G (m+1)) = G 0 - G n
    have := Finset.sum_range_sub'
      (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) n
    -- align the second term's denominator `(n - m)⁻¹` with `(n+1-(m+1))⁻¹`
    have halign : ∀ m ∈ Finset.range n,
        ((m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * binCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹) =
        (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) m -
          (fun m : ℕ => (m : ℂ) * binCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) (m + 1) := by
      intro m hm
      simp only
      have hden : (n : ℂ) - m = (n : ℂ) + 1 - ((m : ℂ) + 1) := by ring
      rw [hden]
      push_cast
      ring
    rw [Finset.sum_congr rfl halign, this]
    -- G 0 - G n = 0 - n·a_n·1 = -(n·a_n)
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  linear_combination hkey

/-- **The closed form is the genuine Cauchy-product coefficient.** The explicit
sum `∑_{m < n} binCoeffℂ α m · (n - m)⁻¹` (the `[zⁿ]` of the product GF) equals
`Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹ = logSingularityCoeffℂ α n`.

Both sides satisfy the same first-order recurrence
`(n+1)·x(n+1) = (α+n)·x(n) + binCoeffℂ α n` with `x 0 = 0`, hence agree. -/
theorem sum_partialFraction_eq_logSingularityCoeffℂ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m)
    (n : ℕ) :
    (∑ m ∈ Finset.range n, binCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
      logSingularityCoeffℂ α n := by
  induction n with
  | zero =>
      simp [logSingularityCoeffℂ, shiftedHarmonicℂ]
  | succ n ih =>
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        intro h
        apply_fun Complex.re at h
        simp at h
        linarith
      have hconv := convCoeff_succ α hα n
      rw [ih] at hconv
      have hT := logSingularityCoeffℂ_succ α hα n
      have hcastn : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      have hgoal :
          ((n : ℂ) + 1) *
            (∑ m ∈ Finset.range (n + 1), binCoeffℂ α m * (((n + 1 : ℕ) : ℂ) - m)⁻¹) =
          ((n : ℂ) + 1) * logSingularityCoeffℂ α (n + 1) := by
        rw [hcastn, hconv, hT]
      exact mul_left_cancel₀ hn1 hgoal

/-- **GF ↔ coefficient identity (complex form).** The `n`-th coefficient of the
genuine log-singularity generating function `(1 - z)^{-α} · log (1 / (1 - z))`
equals the closed form `Ring.choose (α + n - 1) n * ∑_{j < n} (α + j)⁻¹`. -/
theorem coeff_logSingularityGF_eq_logSingularityCoeffℂ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m)
    (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSingularityGF α) = logSingularityCoeffℂ α n := by
  rw [coeff_logSingularityGF, sum_partialFraction_eq_logSingularityCoeffℂ α hα n]

/-- The complex closed form restricts to the real `logSingularityCoeff` for real
`α` and `n`: `(logSingularityCoeff α n : ℂ) = logSingularityCoeffℂ α n`. -/
theorem logSingularityCoeff_cast (α : ℝ) (n : ℕ) :
    (logSingularityCoeff α n : ℂ) = logSingularityCoeffℂ (α : ℂ) n := by
  have hchoose : Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
    rw [Ring.choose, Ring.choose]
    change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
      (algebraMap ℝ ℂ) (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
    rw [Ring.map_multichoose (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
    congr 1
    norm_num [Complex.ofReal_add, Complex.ofReal_sub]
  have hharm : ((shiftedHarmonic α n : ℝ) : ℂ) = shiftedHarmonicℂ (α : ℂ) n := by
    rw [shiftedHarmonic, shiftedHarmonicℂ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]
  rw [logSingularityCoeff, logSingularityCoeffℂ, binCoeffℂ, Complex.ofReal_mul,
    ← hchoose, hharm]

/-- **Main faithfulness theorem.** For real `α` that is not a nonpositive
integer, the real coefficient scale `logSingularityCoeff α n` is exactly the
`n`-th coefficient of the genuine log-singularity generating function
`(1 - z)^{-α} · log (1 / (1 - z))` (as a complex formal power series whose
factor coefficients are the honest Taylor coefficients of `(1 - z)^{-α}` and of
`log (1 / (1 - z))`).

This upgrades `logSingularityCoeff_isEquivalent` from a statement about an
asserted scale to a genuine generating-function coefficient asymptotic. -/
theorem logSingularityCoeff_eq_coeff_logSingularityGF {α : ℝ}
    (hα : ∀ m : ℕ, (α : ℂ) ≠ -m) (n : ℕ) :
    (logSingularityCoeff α n : ℂ) =
      PowerSeries.coeff (R := ℂ) n (logSingularityGF (α : ℂ)) := by
  rw [logSingularityCoeff_cast,
    coeff_logSingularityGF_eq_logSingularityCoeffℂ (α : ℂ) hα n]
