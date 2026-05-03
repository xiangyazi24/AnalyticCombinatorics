/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Saddle-point method coefficient checks.

  The analytic saddle-point method applies to entire generating functions.
  This file records computable coefficient streams for the Chapter VIII
  examples and Prop-valued placeholders for later analytic hypotheses.
-/
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.BellNumbers
import AnalyticCombinatorics.PartA.Ch1.IntPartTheory

set_option linter.style.nativeDecide false

open Finset

/-! ## Basic computable coefficient streams -/

/-- Cauchy-product coefficient for two coefficient streams. -/
def cauchyCoeff (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Coefficient of the `k`-th power of a coefficient stream. -/
def seriesPowCoeff (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => cauchyCoeff a (seriesPowCoeff a k) n

/-! ## The entire function `exp z` -/

/-- Coefficient of `z^n` in the ordinary power-series expansion of `exp z`. -/
def expCoeff (n : ℕ) : ℚ :=
  1 / (n.factorial : ℚ)

/-- Coefficients of `exp z` satisfy `n! [z^n] exp z = 1` for `n = 0, ..., 10`. -/
theorem expCoeff_factorial_samples :
    ((0 : ℕ).factorial : ℚ) * expCoeff 0 = 1 ∧
    ((1 : ℕ).factorial : ℚ) * expCoeff 1 = 1 ∧
    ((2 : ℕ).factorial : ℚ) * expCoeff 2 = 1 ∧
    ((3 : ℕ).factorial : ℚ) * expCoeff 3 = 1 ∧
    ((4 : ℕ).factorial : ℚ) * expCoeff 4 = 1 ∧
    ((5 : ℕ).factorial : ℚ) * expCoeff 5 = 1 ∧
    ((6 : ℕ).factorial : ℚ) * expCoeff 6 = 1 ∧
    ((7 : ℕ).factorial : ℚ) * expCoeff 7 = 1 ∧
    ((8 : ℕ).factorial : ℚ) * expCoeff 8 = 1 ∧
    ((9 : ℕ).factorial : ℚ) * expCoeff 9 = 1 ∧
    ((10 : ℕ).factorial : ℚ) * expCoeff 10 = 1 := by
  native_decide

/-! ## Bell numbers and `exp(exp z - 1)` -/

/-- Coefficient stream for `exp z - 1`. -/
def expMinusOneCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else expCoeff n

/-- Coefficient of `z^n` in `exp(exp z - 1)`, computed from
`exp A(z) = ∑ A(z)^k/k!`.  The finite truncation to `k ≤ n` is valid because
`A(0)=0`. -/
def bellEgfCoeff (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), seriesPowCoeff expMinusOneCoeff k n / (k.factorial : ℚ)

/-- Count-level form of the Bell EGF coefficient. -/
def bellPrefactoredCount (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * bellEgfCoeff n

/-- Bell numbers from `BellNumbers.lean`, extended by direct computation to `n = 8`. -/
theorem BellNumbers.bell_values_0_8 :
    BellNumbers.bell 0 = 1 ∧
    BellNumbers.bell 1 = 1 ∧
    BellNumbers.bell 2 = 2 ∧
    BellNumbers.bell 3 = 5 ∧
    BellNumbers.bell 4 = 15 ∧
    BellNumbers.bell 5 = 52 ∧
    BellNumbers.bell 6 = 203 ∧
    BellNumbers.bell 7 = 877 ∧
    BellNumbers.bell 8 = 4140 := by
  native_decide

/-- The first Bell EGF coefficients satisfy
`B_n = n! [z^n] exp(exp z - 1)` for `n = 0, ..., 8`. -/
theorem bellEgfCoeff_prefactored_samples :
    bellPrefactoredCount 0 = (BellNumbers.bell 0 : ℚ) ∧
    bellPrefactoredCount 1 = (BellNumbers.bell 1 : ℚ) ∧
    bellPrefactoredCount 2 = (BellNumbers.bell 2 : ℚ) ∧
    bellPrefactoredCount 3 = (BellNumbers.bell 3 : ℚ) ∧
    bellPrefactoredCount 4 = (BellNumbers.bell 4 : ℚ) ∧
    bellPrefactoredCount 5 = (BellNumbers.bell 5 : ℚ) ∧
    bellPrefactoredCount 6 = (BellNumbers.bell 6 : ℚ) ∧
    bellPrefactoredCount 7 = (BellNumbers.bell 7 : ℚ) ∧
    bellPrefactoredCount 8 = (BellNumbers.bell 8 : ℚ) := by
  native_decide

/-! ## Integer partitions and Euler's product -/

/-- Coefficient of `z^n` in the Euler factor `(1 - z^k)^{-1}`. -/
def eulerFactorCoeff (k n : ℕ) : ℕ :=
  if k ∣ n then 1 else 0

/-- Coefficient of `z^n` in the finite Euler product
`∏_{k=1}^{K} (1 - z^k)^{-1}`. -/
def eulerProductCoeffUpTo : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | K + 1, n =>
      ∑ p ∈ Finset.antidiagonal n,
        eulerProductCoeffUpTo K p.1 * eulerFactorCoeff (K + 1) p.2

/-- Coefficient of `z^n` in Euler's partition product.  For coefficient `n`,
factors with exponent larger than `n` contribute only their constant term. -/
def eulerPartitionProductCoeff (n : ℕ) : ℕ :=
  eulerProductCoeffUpTo n n

/-- First coefficients of Euler's product:
`1, 1, 2, 3, 5, 7`. -/
theorem eulerPartitionProductCoeff_samples :
    eulerPartitionProductCoeff 0 = 1 ∧
    eulerPartitionProductCoeff 1 = 1 ∧
    eulerPartitionProductCoeff 2 = 2 ∧
    eulerPartitionProductCoeff 3 = 3 ∧
    eulerPartitionProductCoeff 4 = 5 ∧
    eulerPartitionProductCoeff 5 = 7 := by
  native_decide

/-- The same first coefficients agree with the integer-partition counts from
`IntPartTheory.lean`. -/
theorem eulerPartitionProductCoeff_matches_partition_count_0_5 :
    eulerPartitionProductCoeff 0 = Nat.Partition.count 0 ∧
    eulerPartitionProductCoeff 1 = Nat.Partition.count 1 ∧
    eulerPartitionProductCoeff 2 = Nat.Partition.count 2 ∧
    eulerPartitionProductCoeff 3 = Nat.Partition.count 3 ∧
    eulerPartitionProductCoeff 4 = Nat.Partition.count 4 ∧
    eulerPartitionProductCoeff 5 = Nat.Partition.count 5 := by
  native_decide

/-! ## Saddle-point framework predicates -/

/-- Super-exponential growth: eventually larger than every fixed exponential
`ρ^n`. -/
def hasSuperExponentialGrowth (f : ℕ → ℕ) : Prop :=
  ∀ ρ : ℕ, ∃ N : ℕ, ∀ n : ℕ, n > N → f n > ρ ^ n

/-- Prop-valued saddle-point applicability placeholder for later analytic
hypotheses. -/
def IsSaddlePointApplicable (f : ℕ → ℕ) : Prop :=
  hasSuperExponentialGrowth f

/-- Check `count` consecutive values starting at `lo`. -/
def factorialDominatesPowerFrom (ρ lo : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
      factorialDominatesPowerFrom ρ lo count &&
        decide (ρ ^ (lo + count) < (lo + count).factorial)

/-- Finite computational check that `n!` dominates `ρ^n` on a bounded interval. -/
def factorialDominatesPowerOn (ρ lo hi : ℕ) : Bool :=
  factorialDominatesPowerFrom ρ lo (hi + 1 - lo)

/-- Finite samples for the super-exponential behavior of `n!`, for
`ρ = 1, ..., 5`. -/
theorem factorial_superExponential_finite_samples :
    factorialDominatesPowerOn 1 2 25 = true ∧
    factorialDominatesPowerOn 2 4 25 = true ∧
    factorialDominatesPowerOn 3 7 25 = true ∧
    factorialDominatesPowerOn 4 9 25 = true ∧
    factorialDominatesPowerOn 5 12 25 = true := by
  native_decide
