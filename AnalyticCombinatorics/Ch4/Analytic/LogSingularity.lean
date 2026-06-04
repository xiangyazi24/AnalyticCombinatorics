import AnalyticCombinatorics.Ch4.Analytic.TransferTheorem
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Logarithmic singularity scale

This file adds the coefficient scale for the first logarithmic singular factor
over the standard function `(1 - z)^{-α}`.  The analytic Δ-transfer theorem for
arbitrary logarithmic singular expansions is not in this repository yet; the
result below proves the leading coefficient scale directly from the exact
parameter derivative of the binomial coefficients.

For real `α > 1`, the coefficient scale of
`(1 - z)^{-α} log (1 / (1 - z))` is

`choose (α + n - 1) n * ∑_{j<n} (α + j)^{-1}`,

and it is asymptotic to `(n^(α - 1) / Γ α) * log n`.
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
