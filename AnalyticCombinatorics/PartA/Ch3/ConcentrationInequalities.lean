import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-! # Ch III — Concentration inequalities and tail bounds

Finite numerical checks for binomial tails, variance tables, Cantelli bounds,
standardized fourth moments, and fourth-moment tail estimates.
-/

namespace ConcentrationInequalities

/-! ## Binomial tails -/

/-- Binomial coefficients `C(8,k)` for `k = 0..8`. -/
def binomial8Coefficients : Fin 9 → ℕ :=
  ![1, 8, 28, 56, 70, 56, 28, 8, 1]

/-- Upper tail counts `sum_{j=k}^8 C(8,j)` for `k = 0..8`. -/
def binomial8TailCounts : Fin 9 → ℕ :=
  ![256, 255, 247, 219, 163, 93, 37, 9, 1]

/-- A bounded formula for the finite binomial upper tail. -/
def binomial8TailFormula (k : Fin 9) : ℕ :=
  (List.range (9 - k.val)).foldl
    (fun acc j => acc + Nat.choose 8 (k.val + j)) 0

theorem binomial8Coefficients_eq_choose :
    ∀ k : Fin 9, binomial8Coefficients k = Nat.choose 8 k.val := by
  native_decide

theorem binomial8TailCounts_eq_formula :
    ∀ k : Fin 9, binomial8TailCounts k = binomial8TailFormula k := by
  native_decide

theorem binomial8TailCounts_monotone :
    ∀ k : Fin 8,
      binomial8TailCounts k.succ ≤ binomial8TailCounts k.castSucc := by
  native_decide

theorem binomial8_upper_tail_small :
    binomial8TailCounts 6 * 4 ≤ 2 ^ 8 ∧
      binomial8TailCounts 7 * 16 ≤ 2 ^ 8 ∧
      binomial8TailCounts 8 * 128 ≤ 2 ^ 8 := by
  native_decide

/-! ## Variance tables -/

/-- Squared deviations `(2x - 5)^2` for the uniform distribution on `0..5`. -/
def fairDieCenteredSquareTable : Fin 6 → ℕ :=
  ![25, 9, 1, 1, 9, 25]

/-- Fourth powers `(2x - 5)^4` for the uniform distribution on `0..5`. -/
def fairDieCenteredFourthTable : Fin 6 → ℕ :=
  ![625, 81, 1, 1, 81, 625]

/-- Squared absolute difference on natural numbers. -/
def natSqDiff (a b : ℕ) : ℕ :=
  if a ≤ b then (b - a) ^ 2 else (a - b) ^ 2

theorem fairDieCenteredSquareTable_eq_formula :
    ∀ x : Fin 6, fairDieCenteredSquareTable x = natSqDiff (2 * x.val) 5 := by
  native_decide

theorem fairDieVarianceScaledSum :
    (∑ x : Fin 6, fairDieCenteredSquareTable x) = 70 := by
  native_decide

theorem fairDieFourthScaledSum :
    (∑ x : Fin 6, fairDieCenteredFourthTable x) = 1414 := by
  native_decide

/-- Variance numerators for fair Bernoulli, uniform `0..3`, and uniform `0..5`. -/
def varianceNumeratorTable : Fin 3 → ℕ :=
  ![1, 5, 35]

/-- Variance denominators for fair Bernoulli, uniform `0..3`, and uniform `0..5`. -/
def varianceDenominatorTable : Fin 3 → ℕ :=
  ![4, 4, 12]

/-- Squared support ranges for the same three distributions. -/
def supportRangeSquaredTable : Fin 3 → ℕ :=
  ![1, 9, 25]

theorem varianceTables_satisfy_popoviciu_bound :
    ∀ i : Fin 3,
      4 * varianceNumeratorTable i ≤
        varianceDenominatorTable i * supportRangeSquaredTable i := by
  native_decide

/-! ## Cantelli inequality instances -/

/-- Tail masses in four small Cantelli checks. -/
def cantelliTailMassTable : Fin 4 → ℕ :=
  ![1, 2, 1, 2]

/-- Total masses in four small Cantelli checks. -/
def cantelliTotalMassTable : Fin 4 → ℕ :=
  ![6, 6, 4, 4]

/-- Variance terms after a common denominator has been cleared. -/
def cantelliVarianceScaledTable : Fin 4 → ℕ :=
  ![35, 35, 20, 20]

/-- Squared threshold terms after the same denominator has been cleared. -/
def cantelliThresholdSquaredScaledTable : Fin 4 → ℕ :=
  ![75, 27, 36, 4]

theorem cantelliInstances_hold :
    ∀ i : Fin 4,
      cantelliTailMassTable i *
          (cantelliVarianceScaledTable i + cantelliThresholdSquaredScaledTable i) ≤
        cantelliTotalMassTable i * cantelliVarianceScaledTable i := by
  native_decide

/-! ## Standardized fourth moments and kurtosis -/

/-- Kurtosis numerators for fair Bernoulli, uniform `0..3`, and uniform `0..5`. -/
def kurtosisNumeratorTable : Fin 3 → ℕ :=
  ![1, 41, 2121]

/-- Kurtosis denominators for fair Bernoulli, uniform `0..3`, and uniform `0..5`. -/
def kurtosisDenominatorTable : Fin 3 → ℕ :=
  ![1, 25, 1225]

theorem kurtosisTables_are_below_two :
    ∀ i : Fin 3, kurtosisNumeratorTable i ≤ 2 * kurtosisDenominatorTable i := by
  native_decide

theorem kurtosisTables_are_at_least_one :
    ∀ i : Fin 3, kurtosisDenominatorTable i ≤ kurtosisNumeratorTable i := by
  native_decide

/-! ## Fourth moment method examples -/

/-- Tail masses for fourth-moment method examples. -/
def fourthMomentTailMassTable : Fin 4 → ℕ :=
  ![2, 4, 2, 2]

/-- Fourth powers of the scaled thresholds. -/
def fourthMomentThresholdFourthTable : Fin 4 → ℕ :=
  ![625, 81, 81, 1]

/-- Scaled fourth central moments for the examples. -/
def fourthMomentScaledTable : Fin 4 → ℕ :=
  ![1414, 1414, 164, 2]

theorem fourthMomentTailInstances_hold :
    ∀ i : Fin 4,
      fourthMomentTailMassTable i * fourthMomentThresholdFourthTable i ≤
        fourthMomentScaledTable i := by
  native_decide

/-- A compact table of standardized moment numerators up to order four. -/
def standardizedMomentNumerators : Fin 5 → ℕ :=
  ![1, 0, 35, 0, 2121]

theorem standardizedMomentNumerators_even_nonzero :
    standardizedMomentNumerators 0 = 1 ∧
      standardizedMomentNumerators 2 = 35 ∧
      standardizedMomentNumerators 4 = 2121 := by
  native_decide

theorem standardizedMomentNumerators_odd_zero :
    standardizedMomentNumerators 1 = 0 ∧ standardizedMomentNumerators 3 = 0 := by
  native_decide

end ConcentrationInequalities
