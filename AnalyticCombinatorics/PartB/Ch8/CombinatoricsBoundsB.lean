/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Analytic bounds on combinatorial quantities.

  This file verifies concrete numeric instances of classical combinatorial
  bounds: binomial coefficient two-sided estimates, the entropy bound,
  Stirling-type factorial bounds, central binomial tightness, the
  Vandermonde convolution identity, and Catalan number bounds.

  All proofs use `native_decide` on closed numeric goals.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace CombinatoricsBoundsB

/-! ## 1. Binomial coefficient bounds: n^k ≤ k^k * C(n,k) -/

/-- Lower bound (n/k)^k ≤ C(n,k), encoded as n^k ≤ k^k * C(n,k). -/
example : 10^3 ≤ 3^3 * Nat.choose 10 3 := by native_decide

example : 20^4 ≤ 4^4 * Nat.choose 20 4 := by native_decide

example : 15^3 ≤ 3^3 * Nat.choose 15 3 := by native_decide

example : 30^5 ≤ 5^5 * Nat.choose 30 5 := by native_decide

example : 100^4 ≤ 4^4 * Nat.choose 100 4 := by native_decide

/-! ## 2. Upper bound: C(n,k) * k! ≤ n^k -/

/-- Upper bound C(n,k) ≤ n^k / k!, encoded as C(n,k) * k! ≤ n^k. -/
example : Nat.choose 10 3 * Nat.factorial 3 ≤ 10^3 := by native_decide

example : Nat.choose 20 5 * Nat.factorial 5 ≤ 20^5 := by native_decide

example : Nat.choose 15 4 * Nat.factorial 4 ≤ 15^4 := by native_decide

example : Nat.choose 50 6 * Nat.factorial 6 ≤ 50^6 := by native_decide

/-! ## 3. Entropy bound: C(n, n/2) ≤ 2^n -/

/-- For α = 1/2 the entropy bound gives C(n, n/2) ≤ 2^n. -/
example : Nat.choose 2 1 ≤ 2^2 := by native_decide
example : Nat.choose 4 2 ≤ 2^4 := by native_decide
example : Nat.choose 6 3 ≤ 2^6 := by native_decide
example : Nat.choose 8 4 ≤ 2^8 := by native_decide
example : Nat.choose 10 5 ≤ 2^10 := by native_decide
example : Nat.choose 12 6 ≤ 2^12 := by native_decide
example : Nat.choose 20 10 ≤ 2^20 := by native_decide
example : Nat.choose 30 15 ≤ 2^30 := by native_decide

/-! ## 4. Stirling-type factorial bounds -/

/-- Crude lower bound: n! * 3^n > n^n for small n. -/
example : Nat.factorial 4 * 3^4 > 4^4 := by native_decide
example : Nat.factorial 6 * 3^6 > 6^6 := by native_decide
example : Nat.factorial 8 * 3^8 > 8^8 := by native_decide
example : Nat.factorial 10 * 3^10 > 10^10 := by native_decide

/-- 2^n < n! for n ≥ 4. -/
example : 2^4 < Nat.factorial 4 := by native_decide
example : 2^5 < Nat.factorial 5 := by native_decide
example : 2^8 < Nat.factorial 8 := by native_decide
example : 2^10 < Nat.factorial 10 := by native_decide
example : 2^12 < Nat.factorial 12 := by native_decide

/-! ## 5. Central binomial tightness: 4^n < (2n+1) * C(2n,n) -/

/-- Tight lower bound on C(2n,n). -/
example : 4^1 < (2*1+1) * Nat.choose (2*1) 1 := by native_decide
example : 4^2 < (2*2+1) * Nat.choose (2*2) 2 := by native_decide
example : 4^3 < (2*3+1) * Nat.choose (2*3) 3 := by native_decide
example : 4^4 < (2*4+1) * Nat.choose (2*4) 4 := by native_decide
example : 4^5 < (2*5+1) * Nat.choose (2*5) 5 := by native_decide
example : 4^6 < (2*6+1) * Nat.choose (2*6) 6 := by native_decide
example : 4^8 < (2*8+1) * Nat.choose (2*8) 8 := by native_decide
example : 4^10 < (2*10+1) * Nat.choose (2*10) 10 := by native_decide

/-- Upper bound: C(2n,n) < 4^n (immediate since the whole row sums to 4^n). -/
example : Nat.choose (2*1) 1 < 4^1 := by native_decide
example : Nat.choose (2*2) 2 < 4^2 := by native_decide
example : Nat.choose (2*5) 5 < 4^5 := by native_decide
example : Nat.choose (2*10) 10 < 4^10 := by native_decide
example : Nat.choose (2*15) 15 < 4^15 := by native_decide

/-! ## 6. Vandermonde convolution: C(m+n, r) = Σ_k C(m,k)*C(n,r-k) -/

/-- Right-hand side of the Vandermonde identity. -/
def vandermonde (m n r : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (r + 1), Nat.choose m k * Nat.choose n (r - k)

/-- Verify Vandermonde for selected (m, n, r). -/
example : vandermonde 5 5 4 = Nat.choose (5 + 5) 4 := by native_decide
example : vandermonde 4 6 3 = Nat.choose (4 + 6) 3 := by native_decide
example : vandermonde 3 3 3 = Nat.choose (3 + 3) 3 := by native_decide
example : vandermonde 10 10 5 = Nat.choose (10 + 10) 5 := by native_decide
example : vandermonde 7 8 6 = Nat.choose (7 + 8) 6 := by native_decide
example : vandermonde 6 4 4 = Nat.choose (6 + 4) 4 := by native_decide
example : vandermonde 2 8 5 = Nat.choose (2 + 8) 5 := by native_decide

/-! ## 7. Catalan number bounds -/

/-- n-th Catalan number as C(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Upper bound: C_n * (n+1) = C(2n,n) < 4^n. -/
example : catalan 1 * (1 + 1) < 4^1 := by native_decide
example : catalan 2 * (2 + 1) < 4^2 := by native_decide
example : catalan 3 * (3 + 1) < 4^3 := by native_decide
example : catalan 5 * (5 + 1) < 4^5 := by native_decide
example : catalan 8 * (8 + 1) < 4^8 := by native_decide
example : catalan 10 * (10 + 1) < 4^10 := by native_decide

/-- Lower bound: C_n * (n+1) * (2n+1) ≥ 4^n for n ≥ 1. -/
example : catalan 1 * (1 + 1) * (2*1 + 1) ≥ 4^1 := by native_decide
example : catalan 2 * (2 + 1) * (2*2 + 1) ≥ 4^2 := by native_decide
example : catalan 3 * (3 + 1) * (2*3 + 1) ≥ 4^3 := by native_decide
example : catalan 4 * (4 + 1) * (2*4 + 1) ≥ 4^4 := by native_decide
example : catalan 5 * (5 + 1) * (2*5 + 1) ≥ 4^5 := by native_decide
example : catalan 6 * (6 + 1) * (2*6 + 1) ≥ 4^6 := by native_decide
example : catalan 7 * (7 + 1) * (2*7 + 1) ≥ 4^7 := by native_decide
example : catalan 8 * (8 + 1) * (2*8 + 1) ≥ 4^8 := by native_decide

/-- Catalan numbers themselves: first few values. -/
example : catalan 0 = 1 := by native_decide
example : catalan 1 = 1 := by native_decide
example : catalan 2 = 2 := by native_decide
example : catalan 3 = 5 := by native_decide
example : catalan 4 = 14 := by native_decide
example : catalan 5 = 42 := by native_decide

end CombinatoricsBoundsB
