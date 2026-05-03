import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace GFConvergence

/-! # Generating Function Convergence — Numerical Verifications

Chapter V: Convergence properties of generating functions (Flajolet & Sedgewick).

Topics covered:
1. Radius of convergence via ratio test (Catalan, Fibonacci)
2. Cassini identity for Fibonacci ratios
3. Hadamard product: coefficient-wise products
4. Meromorphic GFs and their coefficients
5. Geometric series partial sums
6. Factorial growth (Borel transform / EGF divergence)
7. Cauchy convolution products
-/

-- ============================================================
-- Section 1: Catalan Numbers — Ratio Test
-- ============================================================

/-! ## Catalan Numbers

C_n = C(2n, n) / (n+1).  Successive-ratio: C_{n+1}/C_n = (4n+2)/(n+2) → 4.
Radius of convergence of Σ C_n z^n is 1/4.

Verification: C_{n+1} * (n+2) = C_n * (4n+2).
-/

-- Catalan coefficients via central binomial
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- First eight Catalan numbers
example : catalan 0 = 1 := by native_decide
example : catalan 1 = 1 := by native_decide
example : catalan 2 = 2 := by native_decide
example : catalan 3 = 5 := by native_decide
example : catalan 4 = 14 := by native_decide
example : catalan 5 = 42 := by native_decide
example : catalan 6 = 132 := by native_decide
example : catalan 7 = 429 := by native_decide

-- Ratio identity: C_{n+1} * (n+2) = C_n * (4n+2)
-- This means C_{n+1}/C_n = (4n+2)/(n+2), so the radius is 1/lim = 1/4.
example : catalan 1 * 2 = catalan 0 * 2 := by native_decide   -- 1*2 = 1*2
example : catalan 2 * 3 = catalan 1 * 6 := by native_decide   -- 2*3 = 1*6
example : catalan 3 * 4 = catalan 2 * 10 := by native_decide  -- 5*4 = 2*10
example : catalan 4 * 5 = catalan 3 * 14 := by native_decide  -- 14*5 = 5*14
example : catalan 5 * 6 = catalan 4 * 18 := by native_decide  -- 42*6 = 14*18
example : catalan 6 * 7 = catalan 5 * 22 := by native_decide  -- 132*7 = 42*22

-- ============================================================
-- Section 2: Fibonacci — Cassini Identity
-- ============================================================

/-! ## Fibonacci Numbers and Cassini's Identity

The Fibonacci OGF is z/(1 - z - z²), with poles at z = (-1 ± √5)/2.
The dominant pole is at 1/φ ≈ 0.618, so ρ = 1/φ.

Cassini's identity: F_{n+1}² - F_n · F_{n+2} = (-1)^n.

Lean's Nat.fib uses index convention: fib 0 = 0, fib 1 = 1, fib 2 = 1, ...
-/

-- First few Fibonacci values
example : Nat.fib 0 = 0 := by native_decide
example : Nat.fib 1 = 1 := by native_decide
example : Nat.fib 2 = 1 := by native_decide
example : Nat.fib 3 = 2 := by native_decide
example : Nat.fib 4 = 3 := by native_decide
example : Nat.fib 5 = 5 := by native_decide
example : Nat.fib 6 = 8 := by native_decide
example : Nat.fib 7 = 13 := by native_decide
example : Nat.fib 8 = 21 := by native_decide
example : Nat.fib 9 = 34 := by native_decide
example : Nat.fib 10 = 55 := by native_decide

/-! ### Cassini identity: numerical spot checks

For even n: F_{n+1}² = F_n · F_{n+2} + 1  (F_{n+1}² > F_n · F_{n+2})
For odd  n: F_{n+1}² + 1 = F_n · F_{n+2}  (F_{n+1}² < F_n · F_{n+2})

This shows the ratio F_{n+1}/F_n alternately over- and under-shoots φ.
-/

-- n=4 (even): F_5² = F_4·F_6 + 1, i.e., 25 = 24 + 1
example : Nat.fib 5 ^ 2 = Nat.fib 4 * Nat.fib 6 + 1 := by native_decide

-- n=5 (odd):  F_6² + 1 = F_5·F_7, i.e., 64 + 1 = 65
example : Nat.fib 6 ^ 2 + 1 = Nat.fib 5 * Nat.fib 7 := by native_decide

-- n=6 (even): F_7² = F_6·F_8 + 1, i.e., 169 = 168 + 1
example : Nat.fib 7 ^ 2 = Nat.fib 6 * Nat.fib 8 + 1 := by native_decide

-- n=7 (odd):  F_8² + 1 = F_7·F_9, i.e., 441 + 1 = 442
example : Nat.fib 8 ^ 2 + 1 = Nat.fib 7 * Nat.fib 9 := by native_decide

-- n=8 (even): F_9² = F_8·F_10 + 1, i.e., 1156 = 1155 + 1
example : Nat.fib 9 ^ 2 = Nat.fib 8 * Nat.fib 10 + 1 := by native_decide

-- n=9 (odd): F_10² + 1 = F_9·F_11
example : Nat.fib 10 ^ 2 + 1 = Nat.fib 9 * Nat.fib 11 := by native_decide

-- ============================================================
-- Section 3: Hadamard Product (Coefficient-wise Product)
-- ============================================================

/-! ## Hadamard Product

For f(z) = Σ aₙ zⁿ and g(z) = Σ bₙ zⁿ, the Hadamard product is
  (f ⊙ g)(z) = Σ aₙ bₙ zⁿ.

Hadamard radius theorem: ρ(f ⊙ g) ≥ ρ(f) · ρ(g).

Examples:
• f = 1/(1-z), g = 1/(1-z):    aₙ = 1, bₙ = 1 → (f⊙g) = 1/(1-z).  ρ ≥ 1·1 = 1. ✓
• f = 1/(1-z), g = 1/(1-2z):   aₙ = 1, bₙ = 2ⁿ → (f⊙g) = 1/(1-2z). ρ = 1/2. ✓
• f = Catalan GF, g = 1/(1-2z): aₙ = Cₙ, bₙ = 2ⁿ → hadamardCatGeo.
-/

-- Hadamard product: Catalan coefficients × geometric sequence 2ⁿ
def hadamardCatGeo (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1) * 2 ^ n

example : hadamardCatGeo 0 = 1 := by native_decide    -- C_0 · 1   = 1
example : hadamardCatGeo 1 = 2 := by native_decide    -- C_1 · 2   = 2
example : hadamardCatGeo 2 = 8 := by native_decide    -- C_2 · 4   = 8
example : hadamardCatGeo 3 = 40 := by native_decide   -- C_3 · 8   = 40
example : hadamardCatGeo 4 = 224 := by native_decide  -- C_4 · 16  = 224
example : hadamardCatGeo 5 = 1344 := by native_decide -- C_5 · 32  = 1344

-- Hadamard product of unit sequences (coefficients all 1) = unit sequence
-- Σ 1·1 zⁿ = 1/(1-z); coefficients remain 1.
example : (∑ _k ∈ Finset.range 8, (1 : ℕ)) = 8 := by native_decide

-- Hadamard product: (1,1,1,...) ⊙ (1,2,4,...) = (1,2,4,...)
-- Coefficient-wise: 1 · 2ⁿ = 2ⁿ.
example : ∀ n ∈ Finset.range 8, (1 : ℕ) * 2 ^ n = 2 ^ n := by decide

-- ============================================================
-- Section 4: Meromorphic GFs — Coefficients from Partial Fractions
-- ============================================================

/-! ## Meromorphic Functions and Their Coefficients

Poles determine exponential growth rates:
• 1/(1-z): single pole at z=1, [zⁿ] = 1.
• 1/((1-z)(1-2z)): poles at z=1 and z=1/2.
  Partial fractions: 2/(1-2z) - 1/(1-z), so [zⁿ] = 2·2ⁿ - 1 = 2^{n+1} - 1.

The recurrence from the denominator (1-z)(1-2z) = 1 - 3z + 2z²:
  aₙ - 3aₙ₋₁ + 2aₙ₋₂ = 0, i.e., aₙ₊₂ = 3aₙ₊₁ - 2aₙ.
-/

def twoMinusOne (n : ℕ) : ℕ := 2 ^ (n + 1) - 1

-- First six values
example : twoMinusOne 0 = 1 := by native_decide
example : twoMinusOne 1 = 3 := by native_decide
example : twoMinusOne 2 = 7 := by native_decide
example : twoMinusOne 3 = 15 := by native_decide
example : twoMinusOne 4 = 31 := by native_decide
example : twoMinusOne 5 = 63 := by native_decide

-- Recurrence (in ℕ, written to avoid subtraction):
-- twoMinusOne(n+2) + 2·twoMinusOne(n) = 3·twoMinusOne(n+1)
example : twoMinusOne 2 + 2 * twoMinusOne 0 = 3 * twoMinusOne 1 := by native_decide  -- 7+2=9
example : twoMinusOne 3 + 2 * twoMinusOne 1 = 3 * twoMinusOne 2 := by native_decide  -- 15+6=21
example : twoMinusOne 4 + 2 * twoMinusOne 2 = 3 * twoMinusOne 3 := by native_decide  -- 31+14=45
example : twoMinusOne 5 + 2 * twoMinusOne 3 = 3 * twoMinusOne 4 := by native_decide  -- 63+30=93
example : twoMinusOne 6 + 2 * twoMinusOne 4 = 3 * twoMinusOne 5 := by native_decide  -- 127+62=189

-- ============================================================
-- Section 5: Geometric Series Partial Sums
-- ============================================================

/-! ## Geometric Series

geoSum r n = Σ_{k=0}^n r^k  = (r^{n+1} - 1) / (r - 1)  for r ≠ 1.

For r=2: geoSum 2 n = 2^{n+1} - 1 = twoMinusOne n.
For r=3: geoSum 3 n = (3^{n+1} - 1) / 2.
-/

def geoSum (r n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), r ^ k

-- r=2 matches twoMinusOne
example : geoSum 2 0 = twoMinusOne 0 := by native_decide
example : geoSum 2 1 = twoMinusOne 1 := by native_decide
example : geoSum 2 2 = twoMinusOne 2 := by native_decide
example : geoSum 2 3 = twoMinusOne 3 := by native_decide
example : geoSum 2 4 = twoMinusOne 4 := by native_decide
example : geoSum 2 5 = twoMinusOne 5 := by native_decide

-- r=3 spot checks: (3^{n+1}-1)/2
example : geoSum 3 3 = 40 := by native_decide   -- 1+3+9+27=40; (81-1)/2=40
example : geoSum 3 4 = 121 := by native_decide  -- +81=121; (243-1)/2=121
example : geoSum 3 5 = 364 := by native_decide  -- +243=364; (729-1)/2=364

-- r=4 spot checks
example : geoSum 4 3 = 85 := by native_decide   -- 1+4+16+64=85
example : geoSum 4 4 = 341 := by native_decide  -- +256=341

-- ============================================================
-- Section 6: Factorial Growth (Borel Transform / EGF Divergence)
-- ============================================================

/-! ## Factorial Growth

If the EGF is e^z, then aₙ = n! and the OGF Σ n! zⁿ has radius of convergence 0.
More precisely, n! grows faster than rⁿ for any fixed r.

We verify n! > 2ⁿ for n ≥ 3, and n! > 4ⁿ for n ≥ 10.
Note: 5! = 120 < 3^5 = 243, so n! > 3ⁿ does NOT hold for n=5 — it requires n ≥ 7.
-/

-- n! values
example : Nat.factorial 5 = 120 := by native_decide
example : Nat.factorial 7 = 5040 := by native_decide
example : Nat.factorial 10 = 3628800 := by native_decide

-- n! > 2ⁿ for n ≥ 4 (crossover: 3!=6 < 2^3=8, but 4!=24 > 2^4=16)
example : Nat.factorial 4 > 2 ^ 4 := by native_decide   -- 24 > 16 ✓
example : Nat.factorial 5 > 2 ^ 5 := by native_decide   -- 120 > 32 ✓
example : Nat.factorial 10 > 2 ^ 10 := by native_decide -- 3628800 > 1024 ✓

-- n! > 3ⁿ for n ≥ 7
example : Nat.factorial 7 > 3 ^ 7 := by native_decide   -- 5040 > 2187 ✓
example : Nat.factorial 10 > 3 ^ 10 := by native_decide -- 3628800 > 59049 ✓

-- n! > 4ⁿ for n ≥ 10
example : Nat.factorial 10 > 4 ^ 10 := by native_decide -- 3628800 > 1048576 ✓
example : Nat.factorial 12 > 4 ^ 12 := by native_decide -- 479001600 > 16777216 ✓

-- Contrast: for small n, rⁿ can dominate n!
example : Nat.factorial 3 < 2 ^ 3 + 2 := by native_decide  -- 6 < 10 (illustrative bound)
example : Nat.factorial 5 < 3 ^ 5 := by native_decide       -- 120 < 243 ✓

-- Rapid growth: n! vs (n/2)ⁿ style lower bounds
-- 10! > 3^10 (already shown), showing divergence of Σ n! zⁿ for |z| = 1/3
example : Nat.factorial 15 > 4 ^ 15 := by native_decide

-- ============================================================
-- Section 7: Cauchy Convolution Products
-- ============================================================

/-! ## Cauchy Convolution

[zⁿ] f(z)·g(z) = Σ_{k=0}^n aₖ · b_{n-k}.

• f = g = 1/(1-z): [zⁿ] 1/(1-z)² = n+1.  convolution1 n = n+1.
• f = 1/(1-z), g = 1/(1-2z): [zⁿ] = Σ_{k=0}^n 1·2^{n-k} = 2^{n+1}-1 = twoMinusOne n.
-/

-- Convolution of unit sequence with itself: [zⁿ] 1/(1-z)² = n+1
def convolution1 (n : ℕ) : ℕ := ∑ _k ∈ Finset.range (n + 1), 1

example : convolution1 0 = 1 := by native_decide
example : convolution1 1 = 2 := by native_decide
example : convolution1 2 = 3 := by native_decide
example : convolution1 3 = 4 := by native_decide
example : convolution1 4 = 5 := by native_decide
example : convolution1 5 = 6 := by native_decide
example : convolution1 10 = 11 := by native_decide

-- Matches the formula: convolution1 n = n + 1
example : ∀ n ∈ Finset.range 12, convolution1 n = n + 1 := by decide

-- Convolution of unit sequence with geometric 2ⁿ: [zⁿ] 1/((1-z)(1-2z))
def convolution12 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), 2 ^ (n - k)

example : convolution12 0 = 1 := by native_decide
example : convolution12 1 = 3 := by native_decide
example : convolution12 2 = 7 := by native_decide
example : convolution12 3 = 15 := by native_decide
example : convolution12 4 = 31 := by native_decide
example : convolution12 5 = 63 := by native_decide
example : convolution12 6 = 127 := by native_decide
example : convolution12 7 = 255 := by native_decide
example : convolution12 8 = 511 := by native_decide

-- Matches twoMinusOne
example : convolution12 0 = twoMinusOne 0 := by native_decide
example : convolution12 1 = twoMinusOne 1 := by native_decide
example : convolution12 2 = twoMinusOne 2 := by native_decide
example : convolution12 3 = twoMinusOne 3 := by native_decide
example : convolution12 4 = twoMinusOne 4 := by native_decide
example : convolution12 5 = twoMinusOne 5 := by native_decide
example : convolution12 6 = twoMinusOne 6 := by native_decide
example : convolution12 7 = twoMinusOne 7 := by native_decide
example : convolution12 8 = twoMinusOne 8 := by native_decide

end GFConvergence
