import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace NumberTheoreticGF2

/-!
# Number-theoretic generating functions

Computable finite checks for arithmetic functions used in the
number-theoretic generating functions of Flajolet--Sedgewick, Chapter IV.
-/

def dividesBool (d n : ℕ) : Bool :=
  if d = 0 then false else n % d == 0

def divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun d => dividesBool d n)

def valuesOneTo (n : ℕ) : List ℕ :=
  (List.range n).map (fun k => k + 1)

def isPrimeBool (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    ((List.range (n + 1)).filter (fun d => decide (2 ≤ d ∧ d < n))).all
      (fun d => !dividesBool d n)

/-! ## Euler totient -/

def phi (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ((List.range n).map (fun k => k + 1)).filter (fun k => Nat.gcd k n == 1) |>.length

def totientDivisorSum (n : ℕ) : ℕ :=
  ((divisors n).map phi).sum

example : phi 1 = 1 := by native_decide
example : phi 2 = 1 := by native_decide
example : phi 3 = 2 := by native_decide
example : phi 4 = 2 := by native_decide
example : phi 5 = 4 := by native_decide
example : phi 6 = 2 := by native_decide

example : phi 2 = 2 - 1 := by native_decide
example : phi 3 = 3 - 1 := by native_decide
example : phi 5 = 5 - 1 := by native_decide
example : phi 7 = 7 - 1 := by native_decide
example : phi 11 = 11 - 1 := by native_decide

theorem totient_divisor_sum_1_to_12 :
    (valuesOneTo 12).map totientDivisorSum = valuesOneTo 12 := by
  native_decide

/-! ## Möbius function -/

def hasPrimeSquareFactor (n : ℕ) : Bool :=
  (divisors n).any (fun p => isPrimeBool p && dividesBool (p * p) n)

def primeDivisorCount (n : ℕ) : ℕ :=
  ((divisors n).filter isPrimeBool).length

def mu (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if hasPrimeSquareFactor n then 0
  else if primeDivisorCount n % 2 == 0 then 1 else -1

example : mu 1 = 1 := by native_decide
example : mu 2 = -1 := by native_decide
example : mu 3 = -1 := by native_decide
example : mu 5 = -1 := by native_decide
example : mu (2 ^ 2) = 0 := by native_decide
example : mu (3 ^ 2) = 0 := by native_decide
example : mu (2 * 3) = 1 := by native_decide
example : mu (2 * 5) = 1 := by native_decide

theorem mobius_values_1_to_10 :
    (valuesOneTo 10).map mu = ([1, -1, -1, 0, -1, 1, -1, 0, 0, 1] : List ℤ) := by
  native_decide

/-! ## Divisor functions -/

def sigma0 (n : ℕ) : ℕ :=
  (divisors n).length

def sigma1 (n : ℕ) : ℕ :=
  (divisors n).sum

theorem sigma0_values_1_to_12 :
    (valuesOneTo 12).map sigma0 = ([1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6] : List ℕ) := by
  native_decide

theorem sigma1_values_1_to_12 :
    (valuesOneTo 12).map sigma1 = ([1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28] : List ℕ) := by
  native_decide

example : sigma1 6 = 12 := by native_decide
example : sigma1 12 = 28 := by native_decide

/-! ## Ramanujan tau coefficients of the discriminant -/

def tau (n : ℕ) : ℤ :=
  match n with
  | 1 => 1
  | 2 => -24
  | 3 => 252
  | 4 => -1472
  | 5 => 4830
  | _ => 0

example : tau 1 = 1 := by native_decide
example : tau 2 = -24 := by native_decide
example : tau 3 = 252 := by native_decide
example : tau 4 = -1472 := by native_decide
example : tau 5 = 4830 := by native_decide

/-! ## Dirichlet convolution -/

def dirichletConv (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ((divisors n).map (fun d => f d * g (n / d))).sum

def oneFn (_ : ℕ) : ℤ := 1

def idFn (n : ℕ) : ℤ := n

def phiFn (n : ℕ) : ℤ := phi n

def epsilonFn (n : ℕ) : ℤ :=
  if n = 1 then 1 else 0

example : dirichletConv idFn mu 6 = phiFn 6 := by native_decide
example : dirichletConv idFn mu 12 = phiFn 12 := by native_decide
example : dirichletConv oneFn idFn 6 = sigma1 6 := by native_decide
example : dirichletConv oneFn idFn 12 = sigma1 12 := by native_decide

theorem one_convolved_with_phi_1_to_12 :
    (valuesOneTo 12).map (dirichletConv oneFn phiFn) =
      (valuesOneTo 12).map idFn := by
  native_decide

theorem mobius_convolved_with_one_1_to_10 :
    (valuesOneTo 10).map (dirichletConv mu oneFn) =
      (valuesOneTo 10).map epsilonFn := by
  native_decide

end NumberTheoreticGF2
