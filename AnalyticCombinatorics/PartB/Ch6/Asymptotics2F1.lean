/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Numerical verifications of coefficient asymptotics
  from algebraic and logarithmic singularities.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace Asymptotics2F1

/-! ## 1. Central binomial coefficient recurrence -/

/-- The central binomial satisfies C(2n+2,n+1) = C(2n,n) * 2*(2n+1)/(n+1).
In integers this reads C(2n+2,n+1) * (n+1) = C(2n,n) * 2*(2n+1).
We verify n = 3,4,5. -/
-- n=3: C(8,4)*4 = 280 = C(6,3)*14
example : Nat.choose 8 4 * 4 = Nat.choose 6 3 * 14 := by native_decide
-- n=4: C(10,5)*5 = 1260 = C(8,4)*18
example : Nat.choose 10 5 * 5 = Nat.choose 8 4 * 18 := by native_decide
-- n=5: C(12,6)*6 = 5544 = C(10,5)*22
example : Nat.choose 12 6 * 6 = Nat.choose 10 5 * 22 := by native_decide

/-- Numerical values of central binomial coefficients. -/
example : Nat.choose 2 1   = 2   := by native_decide
example : Nat.choose 4 2   = 6   := by native_decide
example : Nat.choose 6 3   = 20  := by native_decide
example : Nat.choose 8 4   = 70  := by native_decide
example : Nat.choose 10 5  = 252 := by native_decide
example : Nat.choose 12 6  = 924 := by native_decide

/-! ## 2. Harmonic numbers (rational arithmetic) -/

/-- Partial harmonic sums H_n = 1 + 1/2 + ... + 1/n. -/
def harmonicN (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, 1 / ((k : ℚ) + 1)

example : harmonicN 1 = 1       := by native_decide
example : harmonicN 2 = 3 / 2   := by native_decide
example : harmonicN 3 = 11 / 6  := by native_decide
example : harmonicN 4 = 25 / 12 := by native_decide
example : harmonicN 5 = 137 / 60 := by native_decide

/-- harmonicN is strictly increasing. -/
example : harmonicN 3 > harmonicN 2 := by native_decide
example : harmonicN 4 > harmonicN 3 := by native_decide
example : harmonicN 5 > harmonicN 4 := by native_decide

/-! ## 3. Catalan number bounds -/

/-- Catalan number: C_n = C(2n,n) / (n+1). -/
def catalanAS (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : catalanAS 0 = 1  := by native_decide
example : catalanAS 1 = 1  := by native_decide
example : catalanAS 2 = 2  := by native_decide
example : catalanAS 3 = 5  := by native_decide
example : catalanAS 4 = 14 := by native_decide
example : catalanAS 5 = 42 := by native_decide
example : catalanAS 6 = 132 := by native_decide
example : catalanAS 7 = 429 := by native_decide
example : catalanAS 8 = 1430 := by native_decide

/-- Upper bound: C_n * (n+1) = C(2n,n) < 4^n for n ≥ 2.
(Since C(2n,n) < 4^n follows from the binomial theorem: sum of all C(2n,k) = 4^n.) -/
example : catalanAS 2 * 3 < 4 ^ 2 := by native_decide
example : catalanAS 3 * 4 < 4 ^ 3 := by native_decide
example : catalanAS 4 * 5 < 4 ^ 4 := by native_decide
example : catalanAS 5 * 6 < 4 ^ 5 := by native_decide
example : catalanAS 6 * 7 < 4 ^ 6 := by native_decide
example : catalanAS 8 * 9 < 4 ^ 8 := by native_decide
example : catalanAS 10 * 11 < 4 ^ 10 := by native_decide

/-- Lower bound: C_n * (n+1) * (2n+1) > 4^n for n ≥ 2.
This comes from C(2n,n) > 4^n/(2n+1), a standard lower bound. -/
example : catalanAS 2 * 3 * 5 > 4 ^ 2 := by native_decide
example : catalanAS 3 * 4 * 7 > 4 ^ 3 := by native_decide
example : catalanAS 4 * 5 * 9 > 4 ^ 4 := by native_decide
example : catalanAS 5 * 6 * 11 > 4 ^ 5 := by native_decide
example : catalanAS 6 * 7 * 13 > 4 ^ 6 := by native_decide
example : catalanAS 8 * 9 * 17 > 4 ^ 8 := by native_decide
example : catalanAS 10 * 11 * 21 > 4 ^ 10 := by native_decide

/-! ## 4. Singularity type: [z^n](1-z)^{-α} = C(n+α-1, n) for integer α -/

/-- [z^n](1-z)^{-1} = 1. Verified via trivial coefficient. -/
example : Nat.choose (5 + 0) 5 = 1 := by native_decide

/-- [z^n](1-z)^{-2} = n+1. Coefficient of z^n is C(n+1,1) = n+1. -/
example : Nat.choose 6 1 = 6   := by native_decide   -- n=5
example : Nat.choose 11 1 = 11 := by native_decide   -- n=10

/-- [z^n](1-z)^{-3} = C(n+2,2) = (n+1)(n+2)/2. -/
example : Nat.choose 7 2 = 21  := by native_decide   -- n=5
example : Nat.choose 12 2 = 66 := by native_decide   -- n=10
example : Nat.choose 17 2 = 136 := by native_decide  -- n=15

/-- [z^n](1-z)^{-4} = C(n+3,3). -/
example : Nat.choose 9 3 = 84   := by native_decide  -- n=6
example : Nat.choose 13 3 = 286 := by native_decide  -- n=10

/-- [z^n](1-z)^{-5} = C(n+4,4). -/
example : Nat.choose 9 4 = 126  := by native_decide  -- n=5
example : Nat.choose 14 4 = 1001 := by native_decide -- n=10

/-! ## 5. Partial Euler product for ζ(2) approaching π²/6 -/

/-- The Euler product for ζ(2) = Π_p 1/(1-p^{-2}) = π²/6.
First factor (p=2): 1/(1-1/4) = 4/3. -/
example : (1 : ℚ) / (1 - 1/4) = 4/3 := by native_decide

/-- After p=2,3: 4/3 * 9/8 = 3/2. -/
example : (4 : ℚ)/3 * (9/8) = 3/2 := by native_decide

/-- After p=2,3,5: 3/2 * 25/24 = 25/16. -/
example : (3 : ℚ)/2 * (25/24) = 25/16 := by native_decide

/-- After p=2,3,5,7: 25/16 * 49/48 = 1225/768. -/
example : (25 : ℚ)/16 * (49/48) = 1225/768 := by native_decide

/-- After p=2,3,5,7,11: 1225/768 * 121/120 = 29645/18432. -/
example : (1225 : ℚ)/768 * (121/120) = 29645/18432 := by native_decide

/-- Verify these partial products are increasing toward π²/6 ≈ 1.6449...
We verify each is positive and that the sequence grows. -/
example : (4 : ℚ)/3 < 3/2 := by native_decide
example : (3 : ℚ)/2 < 25/16 := by native_decide
example : (25 : ℚ)/16 < 1225/768 := by native_decide
example : (1225 : ℚ)/768 < 29645/18432 := by native_decide

/-- The partial product after 5 primes is already > 1.6 (as 29645/18432 > 8/5). -/
example : (29645 : ℚ)/18432 > 8/5 := by native_decide

/-! ## 6. Stirling / Legendre duplication identity for factorials -/

/-- Legendre duplication in integer form: (2n)! = C(2n,n) * (n!)^2. -/
example : Nat.factorial 6 = Nat.choose 6 3 * (Nat.factorial 3) ^ 2 := by native_decide
example : Nat.factorial 8 = Nat.choose 8 4 * (Nat.factorial 4) ^ 2 := by native_decide
example : Nat.factorial 10 = Nat.choose 10 5 * (Nat.factorial 5) ^ 2 := by native_decide
example : Nat.factorial 12 = Nat.choose 12 6 * (Nat.factorial 6) ^ 2 := by native_decide
example : Nat.factorial 14 = Nat.choose 14 7 * (Nat.factorial 7) ^ 2 := by native_decide
example : Nat.factorial 16 = Nat.choose 16 8 * (Nat.factorial 8) ^ 2 := by native_decide

/-- Factorial growth: n! is strictly increasing for n ≥ 1. -/
example : Nat.factorial 5 < Nat.factorial 6 := by native_decide
example : Nat.factorial 8 < Nat.factorial 9 := by native_decide
example : Nat.factorial 10 < Nat.factorial 11 := by native_decide

/-- A Stirling-flavored integer inequality:
(n!)^2 * 4 ≥ (2n)! / n for moderate n, reflecting n! ~ √(2πn)*(n/e)^n.
We check: (n!)^2 * (2n+1) > (2n)! for small n (equivalent to C(2n,n) < 2n+1, which fails for n≥2).
Instead verify: C(2n,n) < 4^n (summing all binomials). -/
example : Nat.choose 4 2 < 4 ^ 2 := by native_decide   -- 6 < 16
example : Nat.choose 6 3 < 4 ^ 3 := by native_decide   -- 20 < 64
example : Nat.choose 8 4 < 4 ^ 4 := by native_decide   -- 70 < 256
example : Nat.choose 10 5 < 4 ^ 5 := by native_decide  -- 252 < 1024
example : Nat.choose 12 6 < 4 ^ 6 := by native_decide  -- 924 < 4096
example : Nat.choose 20 10 < 4 ^ 10 := by native_decide

/-! ## 7. Interplay: central binomials and Catalan via harmonic bounds -/

/-- C_n < C(2n,n) for all n ≥ 1, since n+1 > 1. -/
example : catalanAS 5 < Nat.choose 10 5 := by native_decide
example : catalanAS 8 < Nat.choose 16 8 := by native_decide

/-- C_n * (n+1) = C(2n,n) exactly. -/
example : catalanAS 5 * 6 = Nat.choose 10 5 := by native_decide
example : catalanAS 8 * 9 = Nat.choose 16 8 := by native_decide
example : catalanAS 10 * 11 = Nat.choose 20 10 := by native_decide

/-- Ratio C(2n,n)/4^n is decreasing: verify 4^n * C(2(n+1),n+1) < 4^(n+1) * C(2n,n)
i.e. C(2n+2,n+1)/C(2n,n) < 4, which follows from C(2n+2,n+1)/C(2n,n) = 2(2n+1)/(n+1) < 4. -/
example : Nat.choose 8 4 * 4 < Nat.choose 6 3 * 16 := by native_decide
example : Nat.choose 10 5 * 4 < Nat.choose 8 4 * 16 := by native_decide
example : Nat.choose 12 6 * 4 < Nat.choose 10 5 * 16 := by native_decide

end Asymptotics2F1
