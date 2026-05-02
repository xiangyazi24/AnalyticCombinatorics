/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter IV — Meromorphic and rational generating-function coefficients

  Lightweight executable checks for the partial-fraction coefficient formula.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

set_option linter.style.nativeDecide false

/-! ## Coefficients of `(1 - α z)^{-r}` -/

/-- Coefficient of `z^n` in `(1 - α z)^{-r}` for natural `α`.

For `r = 0`, the expression is only a totalized arithmetic definition; the
intended partial-fraction use is `r ≥ 1`.
-/
def rationalCoeff (α : ℕ) (r : ℕ) (n : ℕ) : ℕ :=
    Nat.choose (n + r - 1) (r - 1) * α ^ n

/-- The case `r = 1` is the geometric sequence. -/
theorem rationalCoeff_geometric (α n : ℕ) :
    rationalCoeff α 1 n = α ^ n := by
  simp [rationalCoeff]

/-- The case `(1 - z)^{-2}` has coefficients `n + 1`. -/
theorem rationalCoeff_one_orderTwo (n : ℕ) :
    rationalCoeff 1 2 n = n + 1 := by
  simp [rationalCoeff, Nat.choose_one_right]

/-- Boolean finite check for the triangular-number coefficients of `(1 - z)^{-3}`. -/
def rationalCoeffOrderThreeCheckUpTo (N : ℕ) : Bool :=
    (List.range (N + 1)).all fun n =>
      rationalCoeff 1 3 n == (n + 1) * (n + 2) / 2

/-- `(1 - z)^{-3}` has coefficients `(n + 1)(n + 2)/2` for `n = 0, ..., 5`. -/
theorem rationalCoeff_one_orderThree_upto_five :
    rationalCoeffOrderThreeCheckUpTo 5 = true := by
  native_decide

/-! ## Fibonacci recurrence checks -/

/-- The Fibonacci recurrence predicate at index `n`. -/
def fibRecurrence (n : ℕ) : Prop :=
    Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n

/-- Boolean finite check for the Fibonacci recurrence. -/
def fibRecurrenceCheckUpTo (N : ℕ) : Bool :=
    (List.range (N + 1)).all fun n =>
      Nat.fib (n + 2) == Nat.fib (n + 1) + Nat.fib n

/-- Fibonacci satisfies `F(n+2) = F(n+1) + F(n)` for `n = 0, ..., 10`. -/
theorem fibRecurrence_upto_ten :
    fibRecurrenceCheckUpTo 10 = true := by
  native_decide

/-! ## A small linear-recurrence structure -/

/-- A homogeneous linear recurrence, stored by order and integer coefficients. -/
structure LinearRecurrence where
  order : ℕ
  coeffs : Fin order → ℤ

/-- The Fibonacci recurrence `a(n+2) = a(n) + a(n+1)`. -/
def fibonacciLinearRecurrence : LinearRecurrence where
  order := 2
  coeffs := fun _ => 1

/-- A sequence satisfies a recurrence at a single starting index. -/
def satisfiesLinearRecurrenceAt
    (rec : LinearRecurrence) (seq : ℕ → ℤ) (n : ℕ) : Prop :=
    seq (n + rec.order) =
      ∑ i : Fin rec.order, rec.coeffs i * seq (n + i.1)

/-- Boolean finite check for a sequence satisfying a recurrence. -/
def linearRecurrenceCheckUpTo
    (rec : LinearRecurrence) (seq : ℕ → ℤ) (N : ℕ) : Bool :=
    (List.range (N + 1)).all fun n =>
      seq (n + rec.order) == ∑ i : Fin rec.order, rec.coeffs i * seq (n + i.1)

/-- Fibonacci satisfies the packaged recurrence for `n = 0, ..., 10`. -/
theorem fibonacci_linearRecurrence_upto_ten :
    linearRecurrenceCheckUpTo fibonacciLinearRecurrence (fun n => (Nat.fib n : ℤ)) 10 = true := by
  native_decide
