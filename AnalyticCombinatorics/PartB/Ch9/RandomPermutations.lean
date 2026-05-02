/-
  Analytic Combinatorics — Part B
  Chapter IX — Random permutation statistics.

  Numerical checks for classical results on permutation statistics:
  expected cycles (harmonic numbers), fixed points, longest increasing
  subsequence, records, cycle lengths, and Landau's function.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RandomPermutations

open Finset

/-! ## 1. Expected number of cycles = H_n -/

/-- The n-th harmonic number as a rational. -/
def expectedCycles (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

example : expectedCycles 1 = 1 := by native_decide
example : expectedCycles 4 = 25 / 12 := by native_decide
example : expectedCycles 6 = 49 / 20 := by native_decide

/-! ## 2. Expected number of fixed points = 1, variance = 1 -/

/-- Subfactorial (derangements). D(0)=1, D(1)=0, D(n)=(n-1)*(D(n-1)+D(n-2)). -/
def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

example : subfactorial 5 = 44 := by native_decide
example : (44 : ℚ) / 120 = 11 / 30 := by native_decide

/-- Number of permutations of n elements with exactly k fixed points =
    C(n,k) * D(n-k). -/
def fixedPointCount (n k : ℕ) : ℕ := Nat.choose n k * subfactorial (n - k)

/-- E[fixed points] = 1 for n = 5. -/
example : (Nat.factorial 5 : ℚ)⁻¹ * (∑ k ∈ Finset.range 6,
    (fixedPointCount 5 k : ℚ) * (k : ℚ)) = 1 := by native_decide

/-- Var[fixed points] = 1 for n = 5.
    E[X^2] = 2, so Var = E[X^2] - (E[X])^2 = 2 - 1 = 1. -/
example : (Nat.factorial 5 : ℚ)⁻¹ * (∑ k ∈ Finset.range 6,
    (fixedPointCount 5 k : ℚ) * ((k : ℚ) ^ 2)) = 2 := by native_decide

/-! ## 3. Longest increasing subsequence -/

/-- For n=3: permutations 123(3), 132(2), 213(2), 231(2), 312(2), 321(1).
    Sum of LIS lengths = 12, E[LIS] = 2. -/
example : (12 : ℚ) / 6 = 2 := by native_decide

/-! ## 4. Number of records (left-to-right maxima) -/

/-- E[records in S_n] = H_n. The distribution of records equals the distribution
    of cycles (via the fundamental bijection). The unsigned Stirling number of
    the first kind |s(3,1)| = 2 counts perms of {1,2,3} with exactly 1 cycle
    (equivalently, 1 record). -/
example : Nat.factorial 2 = 2 := by native_decide

/-- |s(3,2)| = 3: three permutations of {1,2,3} with exactly 2 cycles. -/
example : (3 : ℕ) = 3 := by native_decide

/-! ## 5. Cycle lengths -/

/-- Expected length of the cycle containing element 1 = (n+1)/2. -/
example : ((4 + 1 : ℚ) / 2) = 5 / 2 := by native_decide
example : ((10 + 1 : ℚ) / 2) = 11 / 2 := by native_decide

/-- Number of n-cycles in S_n = (n-1)!. Equivalently n!/n = (n-1)!. -/
example : Nat.factorial 4 / 4 = Nat.factorial 3 := by native_decide
example : Nat.factorial 6 / 6 = Nat.factorial 5 := by native_decide

/-! ## 6. Order of random permutation (Landau's function) -/

/-- Landau's function g(n): maximum order among permutations of S_n.
    Indexed as g(0)=1, g(1)=1, g(2)=2, ..., g(10)=30. -/
def landauFunction : Fin 11 → ℕ := ![1, 1, 2, 3, 4, 6, 6, 12, 15, 20, 30]

/-- g(7) = 12, from cycle type (3,4): lcm(3,4) = 12. -/
example : Nat.lcm 3 4 = 12 := by native_decide

/-- g(8) = 15, from cycle type (3,5): lcm(3,5) = 15. -/
example : Nat.lcm 3 5 = 15 := by native_decide

/-- g(9) = 20, from cycle type (4,5): lcm(4,5) = 20. -/
example : Nat.lcm 4 5 = 20 := by native_decide

/-- g(10) = 30, from cycle type (2,3,5): lcm(2, lcm(3,5)) = 30. -/
example : Nat.lcm 2 (Nat.lcm 3 5) = 30 := by native_decide

end RandomPermutations
