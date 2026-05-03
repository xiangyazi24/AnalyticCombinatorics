import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace GFClosure

/-!
Closure properties of ordinary generating functions under basic
combinatorial operations from Chapter I of Analytic Combinatorics.

The file works at the level of coefficient sequences.  A sequence
`a : ℕ → ℕ` represents the OGF `A(z) = ∑ a_n z^n`.
-/

/-! ## Sum -/

/-- Coefficients of `A(z) + B(z)`: `(a_n + b_n)`. -/
def sumSeq (a b : ℕ → ℕ) : ℕ → ℕ :=
  fun n => a n + b n

/-! ## Product: Cauchy convolution -/

/-- Coefficients of `A(z) * B(z)`: `Σ_{k=0}^n a_k b_{n-k}`. -/
def cauchyProduct (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), a k.val * b (n - k.val)

/-! ## Hadamard product -/

/-- Coefficient-wise product: `(a_n * b_n)`. -/
def hadamardProduct (a b : ℕ → ℕ) : ℕ → ℕ :=
  fun n => a n * b n

/-! ## Derivative and integration -/

/-- Formal derivative on OGF coefficients:
`F'(z) = Σ (n+1) * a_{n+1} * z^n`. -/
def derivativeSeq (a : ℕ → ℕ) : ℕ → ℕ :=
  fun n => (n + 1) * a (n + 1)

/-- Formal antiderivative on OGF coefficients, with constant term `0`. -/
def integralSeq (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => a n / (n + 1)

/-! ## Binomial transform -/

/-- Binomial transform: `b_n = Σ_{k=0}^n C(n,k) a_k`. -/
def binomialTransform (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), Nat.choose n k.val * a k.val

/-! ## Standard sequences -/

def onesSeq : ℕ → ℕ :=
  fun _ => 1

def deltaSeq : ℕ → ℕ :=
  fun n => if n = 0 then 1 else 0

def linearSeq : ℕ → ℕ :=
  fun n => n + 1

def powersOfTwoSeq : ℕ → ℕ :=
  fun n => 2 ^ n

def zeroThenOnesSeq : ℕ → ℕ :=
  fun n => if n = 0 then 0 else 1

def fibonacciSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacciSeq (n + 1) + fibonacciSeq n

/-! ## Finite coefficient tables used for checks -/

def onesTable8 : Fin 8 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1]

def deltaTable8 : Fin 8 → ℕ :=
  ![1, 0, 0, 0, 0, 0, 0, 0]

def linearTable8 : Fin 8 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8]

def powersOfTwoTable8 : Fin 8 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128]

def fibonacciTable8 : Fin 8 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13]

def zeroThenOnesTable8 : Fin 8 → ℕ :=
  ![0, 1, 1, 1, 1, 1, 1, 1]

def sumTable8 : Fin 8 → ℕ :=
  ![2, 3, 4, 5, 6, 7, 8, 9]

/-! ## Sequence table checks -/

theorem ones_table_values :
    ∀ n : Fin 8, onesSeq n.val = onesTable8 n := by native_decide

theorem delta_table_values :
    ∀ n : Fin 8, deltaSeq n.val = deltaTable8 n := by native_decide

theorem linear_table_values :
    ∀ n : Fin 8, linearSeq n.val = linearTable8 n := by native_decide

theorem powers_of_two_table_values :
    ∀ n : Fin 8, powersOfTwoSeq n.val = powersOfTwoTable8 n := by native_decide

theorem fibonacci_table_values :
    ∀ n : Fin 8, fibonacciSeq n.val = fibonacciTable8 n := by native_decide

theorem zero_then_ones_table_values :
    ∀ n : Fin 8, zeroThenOnesSeq n.val = zeroThenOnesTable8 n := by native_decide

/-! ## Closure checks -/

/-- Sum closure: the coefficient sequence for `A(z)+B(z)` is `(a_n+b_n)`. -/
theorem sum_linear_ones :
    ∀ n : Fin 8, sumSeq linearSeq onesSeq n.val = sumTable8 n := by native_decide

/-- `(1,1,1,...) * (1,0,0,...) = (1,1,1,...)`. -/
theorem cauchy_ones_delta_identity :
    ∀ n : Fin 8, cauchyProduct onesSeq deltaSeq n.val = onesSeq n.val := by native_decide

/-- `(1,1,1,...) * (1,1,1,...) = (1,2,3,4,...)`. -/
theorem cauchy_ones_ones_sum :
    ∀ n : Fin 8, cauchyProduct onesSeq onesSeq n.val = linearSeq n.val := by native_decide

/-- `Fibonacci * (1,0,0,...) = Fibonacci`. -/
theorem cauchy_fibonacci_delta_identity :
    ∀ n : Fin 8, cauchyProduct fibonacciSeq deltaSeq n.val = fibonacciSeq n.val := by native_decide

/-- Hadamard of `(1,2,3,4,...)` and `(1,1,1,...)` is `(1,2,3,4,...)`. -/
theorem hadamard_linear_ones :
    ∀ n : Fin 8, hadamardProduct linearSeq onesSeq n.val = linearSeq n.val := by native_decide

/-- Hadamard of `(1,1,1,...)` and `(1,2,4,8,...)` is `(1,2,4,8,...)`. -/
theorem hadamard_ones_powers_of_two :
    ∀ n : Fin 8, hadamardProduct onesSeq powersOfTwoSeq n.val = powersOfTwoSeq n.val := by
  native_decide

/-- The derivative of the geometric sequence `(1,1,1,...)` is `(1,2,3,4,...)`. -/
theorem derivative_geometric :
    ∀ n : Fin 8, derivativeSeq onesSeq n.val = linearSeq n.val := by native_decide

/-- The antiderivative of `(1,2,3,4,...)` is `(0,1,1,1,1,...)`. -/
theorem integral_linear :
    ∀ n : Fin 8, integralSeq linearSeq n.val = zeroThenOnesSeq n.val := by native_decide

/-- The binomial transform of `(1,0,0,...)` is `(1,1,1,...)`. -/
theorem binomial_transform_delta :
    ∀ n : Fin 8, binomialTransform deltaSeq n.val = onesSeq n.val := by native_decide

end GFClosure
