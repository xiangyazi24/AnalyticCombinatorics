import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CoefficientAsymptotics

/-! # Coefficient Asymptotics

Formalizations related to growth rates and asymptotic behavior of
combinatorial sequences, following Chapter 5 of Flajolet & Sedgewick.
-/

-- Section 1: Growth rate estimation

/-- The ratio a(n+1)/a(n) as a rational number. -/
def growthRatio (a : ℕ → ℕ) (n : ℕ) : ℚ :=
  if a n = 0 then 0 else (a (n + 1) : ℚ) / (a n : ℚ)

/-- Fibonacci growth ratio bounds: for n=12..15, the ratio is between 1.617 and 1.619. -/
example : 1617 * Nat.fib 12 < 1000 * Nat.fib 13 := by native_decide
example : 1000 * Nat.fib 13 < 1619 * Nat.fib 12 := by native_decide

example : 1617 * Nat.fib 13 < 1000 * Nat.fib 14 := by native_decide
example : 1000 * Nat.fib 14 < 1619 * Nat.fib 13 := by native_decide

example : 1617 * Nat.fib 14 < 1000 * Nat.fib 15 := by native_decide
example : 1000 * Nat.fib 15 < 1619 * Nat.fib 14 := by native_decide

example : 1617 * Nat.fib 15 < 1000 * Nat.fib 16 := by native_decide
example : 1000 * Nat.fib 16 < 1619 * Nat.fib 15 := by native_decide

-- Section 2: Catalan ratio recurrence

/-- The n-th Catalan number. -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Check that C_{n+1}*(n+2) = C_n*2*(2*n+1). -/
def catalanRatioCheck (n : ℕ) : Bool :=
  catalanNum (n + 1) * (n + 2) == catalanNum n * (2 * (2 * n + 1))

example : catalanRatioCheck 0 = true := by native_decide
example : catalanRatioCheck 1 = true := by native_decide
example : catalanRatioCheck 2 = true := by native_decide
example : catalanRatioCheck 3 = true := by native_decide
example : catalanRatioCheck 4 = true := by native_decide
example : catalanRatioCheck 5 = true := by native_decide
example : catalanRatioCheck 6 = true := by native_decide
example : catalanRatioCheck 7 = true := by native_decide
example : catalanRatioCheck 8 = true := by native_decide
example : catalanRatioCheck 9 = true := by native_decide
example : catalanRatioCheck 10 = true := by native_decide
example : catalanRatioCheck 11 = true := by native_decide
example : catalanRatioCheck 12 = true := by native_decide

-- Section 3: Motzkin numbers and growth

/-- Table of the first 10 Motzkin numbers. -/
def motzkinTable : Fin 10 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 9
  | ⟨5, _⟩ => 21
  | ⟨6, _⟩ => 51
  | ⟨7, _⟩ => 127
  | ⟨8, _⟩ => 323
  | ⟨9, _⟩ => 835

/-- Motzkin numbers grow slower than 3^n for n=1..9. -/
example : motzkinTable ⟨1, by omega⟩ < 3 ^ 1 := by native_decide
example : motzkinTable ⟨2, by omega⟩ < 3 ^ 2 := by native_decide
example : motzkinTable ⟨3, by omega⟩ < 3 ^ 3 := by native_decide
example : motzkinTable ⟨4, by omega⟩ < 3 ^ 4 := by native_decide
example : motzkinTable ⟨5, by omega⟩ < 3 ^ 5 := by native_decide
example : motzkinTable ⟨6, by omega⟩ < 3 ^ 6 := by native_decide
example : motzkinTable ⟨7, by omega⟩ < 3 ^ 7 := by native_decide
example : motzkinTable ⟨8, by omega⟩ < 3 ^ 8 := by native_decide
example : motzkinTable ⟨9, by omega⟩ < 3 ^ 9 := by native_decide

-- Section 4: Central binomial coefficient decreasing ratio
-- C(2n,n)/4^n is decreasing: C(2n,n)*4^{m} > C(2m,m)*4^{n} when m = n+1

example : Nat.choose 10 5 * 4 ^ 6 > Nat.choose 12 6 * 4 ^ 5 := by native_decide
example : Nat.choose 14 7 * 4 ^ 8 > Nat.choose 16 8 * 4 ^ 7 := by native_decide
example : Nat.choose 4 2 * 4 ^ 3 > Nat.choose 6 3 * 4 ^ 2 := by native_decide
example : Nat.choose 6 3 * 4 ^ 4 > Nat.choose 8 4 * 4 ^ 3 := by native_decide
example : Nat.choose 8 4 * 4 ^ 5 > Nat.choose 10 5 * 4 ^ 4 := by native_decide

-- Section 5: Catalan partial sum convergence

/-- Partial sum of C_k / 5^k up to index N. -/
def catalanPartialSum (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), (catalanNum k : ℚ) / (5 : ℚ) ^ k

/-- The partial sum is increasing. -/
example : catalanPartialSum 5 < catalanPartialSum 10 := by native_decide

/-- The partial sum is bounded above by 2. -/
example : catalanPartialSum 10 < 2 := by native_decide

/-- Further verification of monotonicity. -/
example : catalanPartialSum 0 < catalanPartialSum 1 := by native_decide
example : catalanPartialSum 1 < catalanPartialSum 2 := by native_decide
example : catalanPartialSum 2 < catalanPartialSum 5 := by native_decide

end CoefficientAsymptotics
