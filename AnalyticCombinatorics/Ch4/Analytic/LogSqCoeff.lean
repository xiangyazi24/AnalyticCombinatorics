import AnalyticCombinatorics.Ch4.Analytic.LogSingularity

/-!
# Coefficient identity for the squared-logarithm singularity GF

`logSqGF α := logSingularityGF α * logGF` is the formal power series of
`(1-z)^{-α}·(-log(1-z))²`.  Its coefficient is the closed form (morally `∂²_α` of the
binomial coefficient)

  `coeff n (logSqGF α) = logSqSingularityCoeffℂ α n
     = binCoeffℂ α n · ((shiftedHarmonicℂ α n)² - shiftedHarmonic2ℂ α n)`.

Proof (recurrence matching, mirroring the first-log `convCoeff_succ`/`sum_partialFraction`):
the Cauchy-product coefficient `∑_{m<n} logSingularityCoeffℂ α m · (n-m)⁻¹` and the closed form
both satisfy `(n+1)x(n+1) = (α+n)x(n) + 2·logSingularityCoeffℂ α n` with `x 0 = 0`.
-/

open scoped BigOperators

noncomputable section

namespace AnalyticCombinatorics

/-- `∑_{j<n} (α+j)⁻²` (complex). -/
def shiftedHarmonic2ℂ (α : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, ((α + j)⁻¹) ^ 2

/-- Closed-form squared-log coefficient `binCoeffℂ α n · (H² - H₂)`. -/
def logSqSingularityCoeffℂ (α : ℂ) (n : ℕ) : ℂ :=
  binCoeffℂ α n * ((shiftedHarmonicℂ α n) ^ 2 - shiftedHarmonic2ℂ α n)

/-- The squared-log generating function. -/
noncomputable def logSqGF (α : ℂ) : PowerSeries ℂ := logSingularityGF α * logGF

/-- Recurrence `(n+1)T(n+1) = (α+n)T(n) + 2·L(n)`, `T=logSqSingularityCoeffℂ`,
`L=logSingularityCoeffℂ`.  From `H(n+1)=H+d⁻¹`, `H₂(n+1)=H₂+(d⁻¹)²`, `(n+1)a(n+1)=d·a`. -/
theorem logSqSingularityCoeffℂ_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * logSqSingularityCoeffℂ α (n + 1) =
      (α + n) * logSqSingularityCoeffℂ α n + 2 * logSingularityCoeffℂ α n := by
  have hαn : α + (n : ℂ) ≠ 0 := by intro h; exact hα n (eq_neg_of_add_eq_zero_left h)
  have hHsucc : shiftedHarmonicℂ α (n + 1) = shiftedHarmonicℂ α n + (α + n)⁻¹ := by
    rw [shiftedHarmonicℂ, shiftedHarmonicℂ, Finset.sum_range_succ]
  have hH2succ : shiftedHarmonic2ℂ α (n + 1) = shiftedHarmonic2ℂ α n + ((α + n)⁻¹) ^ 2 := by
    rw [shiftedHarmonic2ℂ, shiftedHarmonic2ℂ, Finset.sum_range_succ]
  have hrec := binCoeffℂ_succ α n
  have hcancel : (α + (n : ℂ)) * (α + (n : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hαn
  rw [logSqSingularityCoeffℂ, logSqSingularityCoeffℂ, logSingularityCoeffℂ, hHsucc, hH2succ]
  linear_combination
    (((shiftedHarmonicℂ α n) ^ 2 - shiftedHarmonic2ℂ α n)
      + 2 * shiftedHarmonicℂ α n * (α + (n : ℂ))⁻¹) * hrec
    + 2 * binCoeffℂ α n * shiftedHarmonicℂ α n * hcancel

/-- The `[zⁿ]` of `logSqGF` as a convolution with the first-log closed coefficient. -/
theorem coeff_logSqGF (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSqGF α) =
      ∑ m ∈ Finset.range n, logSingularityCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
  rw [logSqGF, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  have hlast : PowerSeries.coeff (R := ℂ) n (logSingularityGF α) *
      PowerSeries.coeff (R := ℂ) (n - n) logGF = 0 := by
    rw [Nat.sub_self, logGF, PowerSeries.coeff_mk, logCoeffℂ, if_pos rfl, mul_zero]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [coeff_logSingularityGF_eq_logSingularityCoeffℂ α hα m, logGF, PowerSeries.coeff_mk, logCoeffℂ]
  have hnm : n - m ≠ 0 := by omega
  rw [if_neg hnm]
  congr 1
  rw [Nat.cast_sub hm.le]

/-- Convolution recurrence: `(n+1)S(n+1) = (α+n)S(n) + 2·L(n)`,
`S(n) = ∑_{m<n} L(m)·(n-m)⁻¹`, `L=logSingularityCoeffℂ`. -/
theorem logSqConvCoeff_succ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    ((n : ℂ) + 1) * (∑ m ∈ Finset.range (n + 1), logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) =
      (α + n) * (∑ m ∈ Finset.range n, logSingularityCoeffℂ α m * ((n : ℂ) - m)⁻¹) +
        2 * logSingularityCoeffℂ α n := by
  rw [Finset.sum_range_succ]
  have hlast : logSingularityCoeffℂ α n * ((n : ℂ) + 1 - n)⁻¹ = logSingularityCoeffℂ α n := by
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  rw [hlast, mul_add, mul_comm ((n : ℂ) + 1) (logSingularityCoeffℂ α n)]
  have hkey :
      ((n : ℂ) + 1) * (∑ m ∈ Finset.range n, logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
        (α + n) * (∑ m ∈ Finset.range n, logSingularityCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        -((n : ℂ) * logSingularityCoeffℂ α n) + logSingularityCoeffℂ α n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have htele : ∀ m ∈ Finset.range n,
        ((n : ℂ) + 1) * (logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (α + n) * (logSingularityCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
        (((m : ℂ) * logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * logSingularityCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹)) +
          binCoeffℂ α m * ((n : ℂ) - m)⁻¹ := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hcast : (n : ℂ) - m = ((n - m : ℕ) : ℂ) := by rw [Nat.cast_sub hm.le]
      have hnm : (n : ℂ) - m ≠ 0 := by rw [hcast, Ne, Nat.cast_eq_zero]; omega
      have hcast1 : (n : ℂ) + 1 - m = ((n + 1 - m : ℕ) : ℂ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have hn1m : (n : ℂ) + 1 - m ≠ 0 := by rw [hcast1, Ne, Nat.cast_eq_zero]; omega
      have hLrec := logSingularityCoeffℂ_succ α hα m
      have hD1 : ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ = 1 := mul_inv_cancel₀ hn1m
      have hD0 : ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ = 1 := mul_inv_cancel₀ hnm
      -- (α+m)·L_m = (m+1)·L_{m+1} - a_m
      have hbr :
          ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ - (α + n) * ((n : ℂ) - m)⁻¹ =
            (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
        have key : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ - (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
            (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ := by
          have e1 : ((n : ℂ) + 1) * ((n : ℂ) + 1 - m)⁻¹ - (m : ℂ) * ((n : ℂ) + 1 - m)⁻¹ =
              ((n : ℂ) + 1 - m) * ((n : ℂ) + 1 - m)⁻¹ := by ring
          have e2 : (α + n) * ((n : ℂ) - m)⁻¹ - (α + m) * ((n : ℂ) - m)⁻¹ =
              ((n : ℂ) - m) * ((n : ℂ) - m)⁻¹ := by ring
          rw [e1, e2, hD1, hD0]
        linear_combination key
      linear_combination logSingularityCoeffℂ α m * hbr +
        ((n : ℂ) - m)⁻¹ * hLrec
    rw [Finset.sum_congr rfl htele, Finset.sum_add_distrib]
    rw [sum_partialFraction_eq_logSingularityCoeffℂ α hα n]
    -- telescoping part
    have halign : ∀ m ∈ Finset.range n,
        ((m : ℂ) * logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) -
          (((m : ℂ) + 1) * logSingularityCoeffℂ α (m + 1) * ((n : ℂ) - m)⁻¹) =
        (fun m : ℕ => (m : ℂ) * logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) m -
          (fun m : ℕ => (m : ℂ) * logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) (m + 1) := by
      intro m hm
      simp only
      rw [show (n : ℂ) - m = (n : ℂ) + 1 - ((m : ℂ) + 1) by ring]
      push_cast; ring
    rw [Finset.sum_congr rfl halign,
      Finset.sum_range_sub' (fun m : ℕ => (m : ℂ) * logSingularityCoeffℂ α m * ((n : ℂ) + 1 - m)⁻¹) n]
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    rw [show (n : ℂ) + 1 - n = 1 by ring, inv_one, mul_one]
  linear_combination hkey

/-- The convolution coefficient equals the closed form (same recurrence, `x 0 = 0`). -/
theorem sum_logSqPartialFraction_eq (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    (∑ m ∈ Finset.range n, logSingularityCoeffℂ α m * ((n : ℂ) - m)⁻¹) =
      logSqSingularityCoeffℂ α n := by
  induction n with
  | zero => simp [logSqSingularityCoeffℂ, shiftedHarmonicℂ, shiftedHarmonic2ℂ]
  | succ n ih =>
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by
        intro h; apply_fun Complex.re at h; simp at h; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hconv := logSqConvCoeff_succ α hα n
      rw [ih] at hconv
      have hT := logSqSingularityCoeffℂ_succ α hα n
      have hcastn : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      have hgoal :
          ((n : ℂ) + 1) *
            (∑ m ∈ Finset.range (n + 1), logSingularityCoeffℂ α m * (((n + 1 : ℕ) : ℂ) - m)⁻¹) =
          ((n : ℂ) + 1) * logSqSingularityCoeffℂ α (n + 1) := by
        rw [hcastn, hconv, hT]
      exact mul_left_cancel₀ hn1 hgoal

/-- **GF ↔ closed coefficient identity** for the squared-log singularity. -/
theorem coeff_logSqGF_eq_logSqSingularityCoeffℂ (α : ℂ) (hα : ∀ m : ℕ, α ≠ -m) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (logSqGF α) = logSqSingularityCoeffℂ α n := by
  rw [coeff_logSqGF α hα n, sum_logSqPartialFraction_eq α hα n]

end AnalyticCombinatorics
