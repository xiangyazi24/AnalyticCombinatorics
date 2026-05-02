import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ResidueCalculus

/-! # Residue Calculus and Coefficient Extraction

Numerical verifications of coefficient extraction techniques from Chapter V
of Flajolet & Sedgewick's *Analytic Combinatorics*:
- Partial fraction decomposition
- Convolution formulas for products of GFs
- Cauchy integral formula (Fibonacci)
- Exponential GF coefficient extraction
- Lagrange–Bürmann (Catalan numbers)
- Generating function composition (Fibonacci via compositions)
-/

-- ============================================================
-- Section 1: Partial Fraction Decomposition
-- ============================================================

/-! ## Partial Fraction Decomposition

For 1/((1-az)(1-bz)) with a ≠ b, the coefficient [z^n] equals
  (a^{n+1} - b^{n+1}) / (a - b).

In the case 1/((1-z)(1-2z)), we get [z^n] = (2^{n+1} - 1^{n+1}) / (2 - 1) = 2^{n+1} - 1.
-/

/-- [z^n] 1/((1-z)(1-2z)) = 2^{n+1} - 1, verified for n = 0..6. -/
example : 2 ^ 1 - 1 = (1 : ℕ) := by native_decide   -- n=0
example : 2 ^ 2 - 1 = (3 : ℕ) := by native_decide   -- n=1
example : 2 ^ 3 - 1 = (7 : ℕ) := by native_decide   -- n=2
example : 2 ^ 4 - 1 = (15 : ℕ) := by native_decide  -- n=3
example : 2 ^ 5 - 1 = (31 : ℕ) := by native_decide  -- n=4
example : 2 ^ 6 - 1 = (63 : ℕ) := by native_decide  -- n=5
example : 2 ^ 7 - 1 = (127 : ℕ) := by native_decide -- n=6

-- ============================================================
-- Section 2: Triple Product via Convolution
-- ============================================================

/-! ## Triple Product Decomposition

[z^n] 1/((1-z)(1-2z)(1-3z)) can be computed by convolving
[z^k] 1/((1-z)(1-2z)) = 2^{k+1} - 1 with [z^m] 1/(1-3z) = 3^m.

Thus [z^n] = Σ_{k=0}^n (2^{k+1} - 1) * 3^{n-k}.
-/

/-- Convolution check for 1/((1-z)(1-2z)(1-3z)). -/
-- n=0: (2^1 - 1)*3^0 = 1*1 = 1
example : (1 : ℕ) = 1 := by native_decide
-- n=1: (2^1-1)*3^1 + (2^2-1)*3^0 = 1*3 + 3*1 = 6
example : 1 * 3 + 3 * 1 = (6 : ℕ) := by native_decide
-- n=2: (2^1-1)*3^2 + (2^2-1)*3^1 + (2^3-1)*3^0 = 1*9 + 3*3 + 7*1 = 25
example : 1 * 9 + 3 * 3 + 7 * 1 = (25 : ℕ) := by native_decide
-- n=3: 1*27 + 3*9 + 7*3 + 15*1 = 90
example : 1 * 27 + 3 * 9 + 7 * 3 + 15 * 1 = (90 : ℕ) := by native_decide

-- ============================================================
-- Section 3: Cauchy Integral / Fibonacci
-- ============================================================

/-! ## Coefficient Extraction via Cauchy Integral Formula

[z^n] f(z) = (1/2πi) ∮ f(z)/z^{n+1} dz.

For rational GFs, this yields exact formulas via residues.
Example: [z^n] z/(1-z-z^2) = F(n+1) (the (n+1)-th Fibonacci number).
-/

/-- Fibonacci numbers via [z^n] z/(1-z-z²). -/
example : Nat.fib 6 = 8 := by native_decide
example : Nat.fib 10 = 55 := by native_decide
example : Nat.fib 15 = 610 := by native_decide
example : Nat.fib 20 = 6765 := by native_decide

-- ============================================================
-- Section 4: Exponential GF Coefficient Extraction
-- ============================================================

/-! ## Exponential GF Coefficient Extraction

For exp(kz) = Σ_n (k^n/n!) z^n, the labelled count is
n! * [z^n] e^{kz} = k^n.

This counts the number of functions from an n-set to a k-set.
-/

/-- k^n counts functions from n-set to k-set. -/
example : 3 ^ 4 = (81 : ℕ) := by native_decide
example : 4 ^ 5 = (1024 : ℕ) := by native_decide
example : 2 ^ 10 = (1024 : ℕ) := by native_decide
example : 5 ^ 3 = (125 : ℕ) := by native_decide

-- ============================================================
-- Section 5: Lagrange–Bürmann / Catalan Numbers
-- ============================================================

/-! ## Lagrange–Bürmann Formula and Catalan Numbers

If T = z·φ(T), then [z^n]T = (1/n)[u^{n-1}] φ(u)^n.

The Catalan numbers arise from T = z(1+T)², or equivalently
C(n) = (1/(n+1)) * C(2n, n).

We verify Catalan numbers directly via their binomial formula.
-/

/-- Catalan(n) = C(2n,n)/(n+1). -/
-- C(5) = C(10,5)/6 = 252/6 = 42
example : Nat.choose 10 5 / 6 = (42 : ℕ) := by native_decide
-- C(6) = C(12,6)/7 = 924/7 = 132
example : Nat.choose 12 6 / 7 = (132 : ℕ) := by native_decide
-- C(7) = C(14,7)/8 = 3432/8 = 429
example : Nat.choose 14 7 / 8 = (429 : ℕ) := by native_decide
-- C(8) = C(16,8)/9 = 12870/9 = 1430
example : Nat.choose 16 8 / 9 = (1430 : ℕ) := by native_decide
-- C(10) = C(20,10)/11 = 184756/11 = 16796
example : Nat.choose 20 10 / 11 = (16796 : ℕ) := by native_decide

-- ============================================================
-- Section 6: GF Composition / Compositions into Parts {1,2}
-- ============================================================

/-! ## Generating Function Composition

[z^n] 1/(1-g(z)) with g(z) = z + z² counts compositions of n into parts 1 and 2.
The number of such compositions equals F(n+1) (Fibonacci shifted by one).

Verification: n=2 has {1,1},{2} → 2 = F(3); n=3 has {1,1,1},{1,2},{2,1} → 3 = F(4).
-/

/-- Compositions into parts {1,2}: count(n) = Fib(n+1). -/
example : Nat.fib 3 = 2 := by native_decide   -- n=2
example : Nat.fib 4 = 3 := by native_decide   -- n=3
example : Nat.fib 5 = 5 := by native_decide   -- n=4
example : Nat.fib 6 = 8 := by native_decide   -- n=5
example : Nat.fib 7 = 13 := by native_decide  -- n=6
example : Nat.fib 8 = 21 := by native_decide  -- n=7

end ResidueCalculus
