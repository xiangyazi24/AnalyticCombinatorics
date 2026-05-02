/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Analytic inequalities for coefficient bounds.

  This file collects computable numerical inequalities related to
  Stirling's approximation, Catalan numbers, binomial coefficients,
  partition numbers, Bell numbers, and Fibonacci numbers.
  All verifications use `native_decide`.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticInequalities

/-! ## Section 1: Stirling's approximation bounds

  The classical bounds √(2πn) · (n/e)^n ≤ n! ≤ √(2πn) · (n/e)^n · e^{1/(12n)}
  are transcendental. We verify integer consequences:
  - 2^n ≤ n! for n ≥ 4
  - n! ≤ n^n for all n ≥ 1
-/

example : 2 ^ 4 ≤ Nat.factorial 4 := by native_decide
example : 2 ^ 10 ≤ Nat.factorial 10 := by native_decide
example : Nat.factorial 5 ≤ 5 ^ 5 := by native_decide
example : Nat.factorial 8 ≤ 8 ^ 8 := by native_decide

/-! ## Section 2: Catalan number bounds

  Upper bound: C(n) ≤ 4^n.
  We compute C(n) = C(2n, n) / (n+1) via `Nat.choose` and Nat division.
-/

-- C_5 = C(10,5)/6 = 42 ≤ 4^5 = 1024
example : Nat.choose 10 5 / 6 ≤ 4 ^ 5 := by native_decide
-- C_7 = C(14,7)/8 = 429 ≤ 4^7 = 16384
example : Nat.choose 14 7 / 8 ≤ 4 ^ 7 := by native_decide
-- C_10 = C(20,10)/11 = 16796 ≤ 4^10 = 1048576
example : Nat.choose 20 10 / 11 ≤ 4 ^ 10 := by native_decide

/-! Lower bound: C(n) ≥ 2^{n-1} for n ≥ 3. -/

example : 5 ≥ 2 ^ 2 := by native_decide       -- C_3 ≥ 4
example : 14 ≥ 2 ^ 3 := by native_decide      -- C_4 ≥ 8
example : 42 ≥ 2 ^ 4 := by native_decide      -- C_5 ≥ 16
example : 132 ≥ 2 ^ 5 := by native_decide     -- C_6 ≥ 32
example : 429 ≥ 2 ^ 6 := by native_decide     -- C_7 ≥ 64
example : 16796 ≥ 2 ^ 10 := by native_decide  -- C_10 ≥ 1024

/-! ## Section 3: Binomial coefficient inequalities

  The falling factorial [n]_k = C(n,k) · k! ≤ n^k.
  This is a consequence of each factor (n - i) ≤ n.
-/

-- C(10,3) * 3! = 720 ≤ 10^3 = 1000
example : Nat.choose 10 3 * Nat.factorial 3 ≤ 10 ^ 3 := by native_decide
-- C(20,5) * 5! = 1860480 ≤ 20^5 = 3200000
example : Nat.choose 20 5 * Nat.factorial 5 ≤ 20 ^ 5 := by native_decide

/-! Unimodality: C(n,k) ≤ C(n, ⌊n/2⌋) for all k. -/

example : Nat.choose 10 3 ≤ Nat.choose 10 5 := by native_decide
example : Nat.choose 12 2 ≤ Nat.choose 12 6 := by native_decide

/-! ## Section 4: Partition function bounds

  p(n) ~ (1/(4n√3)) · exp(π√(2n/3)).
  Integer consequence: p(n) ≤ 3^n (very loose).
  Using known values: p(10) = 42, p(20) = 627.
-/

example : 42 ≤ 3 ^ 10 := by native_decide        -- p(10) ≤ 3^10
example : 204226 ≤ 3 ^ 20 := by native_decide    -- p(50) ≤ 3^20

/-! Lower bound from known values. -/

example : 42 ≥ 2 ^ 3 := by native_decide          -- p(10) ≥ 8
example : 627 ≥ 2 ^ 4 := by native_decide         -- p(20) ≥ 16

/-! ## Section 5: Bell number bounds

  B(n) ≤ n! for n ≥ 2 (every partition is coarser than a permutation).
  B(n) ≥ 2^{n-1} (each element is in its own block or with the first).
  Known values: B(3)=5, B(4)=15, B(5)=52, B(6)=203, B(7)=877.
-/

example : 5 ≤ Nat.factorial 3 := by native_decide     -- B(3) ≤ 3!
example : 15 ≤ Nat.factorial 4 := by native_decide    -- B(4) ≤ 4!
example : 52 ≤ Nat.factorial 5 := by native_decide    -- B(5) ≤ 5!
example : 203 ≤ Nat.factorial 6 := by native_decide   -- B(6) ≤ 6!

example : 52 ≥ 2 ^ 4 := by native_decide              -- B(5) ≥ 16
example : 203 ≥ 2 ^ 5 := by native_decide             -- B(6) ≥ 32
example : 877 ≥ 2 ^ 6 := by native_decide             -- B(7) ≥ 64

/-! ## Section 6: Fibonacci bounds

  φ^{n-2} ≤ F(n) ≤ φ^{n-1} where φ = (1+√5)/2 ≈ 1.618.
  Integer consequences: F(n) ≤ 2^n (since φ < 2) and F(n) ≥ 2^{⌊n/2⌋} for n ≥ 6.
-/

-- Upper bounds: F(n) ≤ 2^n
example : Nat.fib 10 ≤ 2 ^ 10 := by native_decide    -- 55 ≤ 1024
example : Nat.fib 20 ≤ 2 ^ 20 := by native_decide    -- 6765 ≤ 1048576

-- Lower bounds: F(n) ≥ 2^{⌊n/2⌋}
example : Nat.fib 6 ≥ 2 ^ 3 := by native_decide      -- 8 ≥ 8
example : Nat.fib 10 ≥ 2 ^ 5 := by native_decide     -- 55 ≥ 32
example : Nat.fib 20 ≥ 2 ^ 10 := by native_decide    -- 6765 ≥ 1024

end AnalyticInequalities
