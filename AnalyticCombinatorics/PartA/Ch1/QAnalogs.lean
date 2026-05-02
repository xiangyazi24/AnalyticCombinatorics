/-
  Chapter I appendix — q-analogs and Gaussian binomial coefficients.

  The basic q-number is recorded as a natural-number evaluation.  Gaussian
  binomial coefficients are defined by their Pascal recurrence, which avoids
  polynomial arithmetic and divisibility arguments for the closed product form.
-/
import Mathlib.Tactic

set_option linter.style.show false
set_option linter.style.nativeDecide false

open Finset

namespace QAnalogs

/-! ## q-numbers and q-factorials -/

/-- Natural-number evaluation of the q-number `[n]_q = (q^n - 1)/(q - 1)`. -/
def qNumber (q n : ℕ) : ℕ :=
  (q ^ n - 1) / (q - 1)

/-- Product of q-numbers `[1]_q [2]_q ... [n]_q`. -/
def qFactorial (q n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, qNumber q (i + 1)

theorem qNumber_two (n : ℕ) :
    qNumber 2 n = 2 ^ n - 1 := by
  simp [qNumber]

example : qNumber 2 0 = 0 := by native_decide
example : qNumber 2 1 = 1 := by native_decide
example : qNumber 2 2 = 3 := by native_decide
example : qNumber 2 3 = 7 := by native_decide
example : qNumber 2 4 = 15 := by native_decide

example : qFactorial 2 0 = 1 := by native_decide
example : qFactorial 2 1 = 1 := by native_decide
example : qFactorial 2 2 = 3 := by native_decide
example : qFactorial 2 3 = 21 := by native_decide
example : qFactorial 2 4 = 315 := by native_decide

/-! ## Gaussian binomial coefficients -/

/--
Gaussian binomial coefficient evaluated at `q`.

The recurrence is

`[n+1 choose k+1]_q = [n choose k]_q + q^(k+1) * [n choose k+1]_q`,

with the usual boundary values.  At `q = 2` these count subspaces of
`GF(2)^n`.
-/
def gaussianBinomial (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      gaussianBinomial q n k + q ^ (k + 1) * gaussianBinomial q n (k + 1)

@[simp] theorem gaussianBinomial_zero_zero (q : ℕ) :
    gaussianBinomial q 0 0 = 1 := rfl

@[simp] theorem gaussianBinomial_zero_succ (q k : ℕ) :
    gaussianBinomial q 0 (k + 1) = 0 := rfl

@[simp] theorem gaussianBinomial_succ_zero (q n : ℕ) :
    gaussianBinomial q (n + 1) 0 = 1 := rfl

theorem gaussianBinomial_succ_succ (q n k : ℕ) :
    gaussianBinomial q (n + 1) (k + 1) =
      gaussianBinomial q n k + q ^ (k + 1) * gaussianBinomial q n (k + 1) := rfl

/-! ## Sanity checks at `q = 2` -/

example : gaussianBinomial 2 0 0 = 1 := by native_decide
example : gaussianBinomial 2 1 0 = 1 := by native_decide
example : gaussianBinomial 2 1 1 = 1 := by native_decide
example : gaussianBinomial 2 2 1 = 3 := by native_decide
example : gaussianBinomial 2 3 1 = 7 := by native_decide
example : gaussianBinomial 2 3 2 = 7 := by native_decide
example : gaussianBinomial 2 4 2 = 35 := by native_decide
example : gaussianBinomial 2 5 2 = 155 := by native_decide

example : gaussianBinomial 2 2 3 = 0 := by native_decide
example : gaussianBinomial 2 3 4 = 0 := by native_decide

/-! ## Pascal-like checks -/

example :
    gaussianBinomial 2 3 1 =
      gaussianBinomial 2 2 0 + 2 ^ 1 * gaussianBinomial 2 2 1 := by
  native_decide

example :
    gaussianBinomial 2 4 2 =
      gaussianBinomial 2 3 1 + 2 ^ 2 * gaussianBinomial 2 3 2 := by
  native_decide

example :
    gaussianBinomial 2 5 2 =
      gaussianBinomial 2 4 1 + 2 ^ 2 * gaussianBinomial 2 4 2 := by
  native_decide

example :
    gaussianBinomial 2 5 3 =
      gaussianBinomial 2 4 2 + 2 ^ 3 * gaussianBinomial 2 4 3 := by
  native_decide

/-! ## Row sums -/

/-- Sum of the `n`th Gaussian-binomial row at a fixed `q`. -/
def gaussianRowSum (q n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), gaussianBinomial q n k

example : gaussianRowSum 2 0 = 1 := by native_decide
example : gaussianRowSum 2 1 = 2 := by native_decide
example : gaussianRowSum 2 2 = 5 := by native_decide
example : gaussianRowSum 2 3 = 16 := by native_decide
example : gaussianRowSum 2 4 = 67 := by native_decide
example : gaussianRowSum 2 5 = 374 := by native_decide



end QAnalogs