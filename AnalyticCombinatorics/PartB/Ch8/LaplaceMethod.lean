/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII — Laplace / Steepest-Descent Method.

  This file collects numerical checks related to the Laplace method and
  saddle-point (steepest-descent) asymptotics:

  1. Stirling-type inequalities for binomial coefficients
  2. Central binomial coefficient bounds  (4^n / (2n+1) ≤ C(2n,n) < 4^n)
  3. Catalan numbers and their relation to central binomials
  4. Partition function upper bound  p(n) < 2^n  for small n
  5. Derangements and their ratio to n! (approx 1/e ≈ 0.3679)
  6. Vandermonde / sum-of-binomials identity  Σ C(n,k) = 2^n

  All proofs use `native_decide` on concrete instances.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace LaplaceMethod

-- ─────────────────────────────────────────────────────────────────────────────
-- §1. Stirling-type binomial inequalities
-- ─────────────────────────────────────────────────────────────────────────────

/-!
  The middle binomial coefficient satisfies  C(2n,n) < 4^n.
  This is the combinatorial shadow of the Stirling estimate
  C(2n,n) ~ 4^n / √(πn).
-/

-- C(20,10) < 4^10
example : Nat.choose 20 10 < 4^10 := by native_decide

-- C(16,8) < 4^8
example : Nat.choose 16 8 < 4^8 := by native_decide

-- Check n! * n! < (2n)! for n = 1 .. 8
-- Equivalently C(2n,n) > 1, which is obvious, but the product form is handy.
example : Nat.factorial 1 * Nat.factorial 1 < Nat.factorial 2 := by native_decide
example : Nat.factorial 2 * Nat.factorial 2 < Nat.factorial 4 := by native_decide
example : Nat.factorial 3 * Nat.factorial 3 < Nat.factorial 6 := by native_decide
example : Nat.factorial 4 * Nat.factorial 4 < Nat.factorial 8 := by native_decide
example : Nat.factorial 5 * Nat.factorial 5 < Nat.factorial 10 := by native_decide
example : Nat.factorial 6 * Nat.factorial 6 < Nat.factorial 12 := by native_decide
example : Nat.factorial 7 * Nat.factorial 7 < Nat.factorial 14 := by native_decide
example : Nat.factorial 8 * Nat.factorial 8 < Nat.factorial 16 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §2. Central binomial coefficients
-- ─────────────────────────────────────────────────────────────────────────────

/-- The central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

-- Spot-check values
example : centralBinom 0 = 1 := by native_decide
example : centralBinom 1 = 2 := by native_decide
example : centralBinom 2 = 6 := by native_decide
example : centralBinom 3 = 20 := by native_decide
example : centralBinom 4 = 70 := by native_decide
example : centralBinom 5 = 252 := by native_decide

/-!
  Lower bound: C(2n,n) * (2n+1) ≥ 4^n  (follows from the integral ∫₀¹ x^n(1−x)^n dx = (n!)²/(2n+1)!)
-/
example : centralBinom 1 * (2 * 1 + 1) ≥ 4^1 := by native_decide
example : centralBinom 2 * (2 * 2 + 1) ≥ 4^2 := by native_decide
example : centralBinom 3 * (2 * 3 + 1) ≥ 4^3 := by native_decide
example : centralBinom 4 * (2 * 4 + 1) ≥ 4^4 := by native_decide
example : centralBinom 5 * (2 * 5 + 1) ≥ 4^5 := by native_decide
example : centralBinom 6 * (2 * 6 + 1) ≥ 4^6 := by native_decide
example : centralBinom 7 * (2 * 7 + 1) ≥ 4^7 := by native_decide
example : centralBinom 8 * (2 * 8 + 1) ≥ 4^8 := by native_decide

/-!
  Upper bound: C(2n,n) < 4^n  for n ≥ 1.
-/
example : centralBinom 1  < 4^1  := by native_decide
example : centralBinom 2  < 4^2  := by native_decide
example : centralBinom 3  < 4^3  := by native_decide
example : centralBinom 4  < 4^4  := by native_decide
example : centralBinom 5  < 4^5  := by native_decide
example : centralBinom 6  < 4^6  := by native_decide
example : centralBinom 7  < 4^7  := by native_decide
example : centralBinom 8  < 4^8  := by native_decide
example : centralBinom 9  < 4^9  := by native_decide
example : centralBinom 10 < 4^10 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §3. Catalan numbers and their connection to central binomials
-- ─────────────────────────────────────────────────────────────────────────────

/-!
  The n-th Catalan number is  Cₙ = C(2n,n) / (n+1).
  In the saddle-point analysis, C(2n,n) ~ 4^n / √(πn)  implies
  Cₙ ~ 4^n / (n^{3/2} √π).
-/

/-- Catalan number as a natural number (integer division). -/
def catalanNum (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Spot-check Catalan values: 1,1,2,5,14,42,132,429,1430,4862
example : catalanNum 0  = 1    := by native_decide
example : catalanNum 1  = 1    := by native_decide
example : catalanNum 2  = 2    := by native_decide
example : catalanNum 3  = 5    := by native_decide
example : catalanNum 4  = 14   := by native_decide
example : catalanNum 5  = 42   := by native_decide
example : catalanNum 6  = 132  := by native_decide
example : catalanNum 7  = 429  := by native_decide
example : catalanNum 8  = 1430 := by native_decide

/-!
  Ratio check: C(2n,n) / catalanNum n = n+1 for n ≥ 1.
  (No Nat division errors since (n+1) | C(2n,n) exactly.)
-/
example : centralBinom 1 / catalanNum 1 = 1 + 1 := by native_decide
example : centralBinom 2 / catalanNum 2 = 2 + 1 := by native_decide
example : centralBinom 3 / catalanNum 3 = 3 + 1 := by native_decide
example : centralBinom 4 / catalanNum 4 = 4 + 1 := by native_decide
example : centralBinom 5 / catalanNum 5 = 5 + 1 := by native_decide
example : centralBinom 6 / catalanNum 6 = 6 + 1 := by native_decide
example : centralBinom 7 / catalanNum 7 = 7 + 1 := by native_decide
example : centralBinom 8 / catalanNum 8 = 8 + 1 := by native_decide

-- Multiplication form (avoids any division ambiguity):
-- catalanNum n * (n + 1) = centralBinom n
example : catalanNum 1 * (1 + 1) = centralBinom 1 := by native_decide
example : catalanNum 2 * (2 + 1) = centralBinom 2 := by native_decide
example : catalanNum 3 * (3 + 1) = centralBinom 3 := by native_decide
example : catalanNum 4 * (4 + 1) = centralBinom 4 := by native_decide
example : catalanNum 5 * (5 + 1) = centralBinom 5 := by native_decide
example : catalanNum 6 * (6 + 1) = centralBinom 6 := by native_decide
example : catalanNum 7 * (7 + 1) = centralBinom 7 := by native_decide
example : catalanNum 8 * (8 + 1) = centralBinom 8 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §4. Partition function upper bound
-- ─────────────────────────────────────────────────────────────────────────────

/-!
  Hardy–Ramanujan: p(n) ~ (1/(4n√3)) · exp(π√(2n/3)).
  As a checkable bound, we verify the weaker  p(n) < 2^n  for small n.
  (The true Laplace-method bound is much tighter, but requires real arithmetic.)
-/

/-- Small partition-number table: p(0)=1, …, p(15)=176. -/
def partTable : Fin 16 → ℕ :=
  ![ 1,  1,  2,  3,  5,  7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176 ]

-- Verify the table values are correct (spot-checks via OEIS A000041).
example : partTable ⟨0,  by norm_num⟩ = 1   := by native_decide
example : partTable ⟨1,  by norm_num⟩ = 1   := by native_decide
example : partTable ⟨4,  by norm_num⟩ = 5   := by native_decide
example : partTable ⟨10, by norm_num⟩ = 42  := by native_decide
example : partTable ⟨15, by norm_num⟩ = 176 := by native_decide

-- p(n) < 2^n for 1 ≤ n ≤ 15
example : partTable ⟨1,  by norm_num⟩ < 2^1  := by native_decide
example : partTable ⟨2,  by norm_num⟩ < 2^2  := by native_decide
example : partTable ⟨3,  by norm_num⟩ < 2^3  := by native_decide
example : partTable ⟨4,  by norm_num⟩ < 2^4  := by native_decide
example : partTable ⟨5,  by norm_num⟩ < 2^5  := by native_decide
example : partTable ⟨6,  by norm_num⟩ < 2^6  := by native_decide
example : partTable ⟨7,  by norm_num⟩ < 2^7  := by native_decide
example : partTable ⟨8,  by norm_num⟩ < 2^8  := by native_decide
example : partTable ⟨9,  by norm_num⟩ < 2^9  := by native_decide
example : partTable ⟨10, by norm_num⟩ < 2^10 := by native_decide
example : partTable ⟨11, by norm_num⟩ < 2^11 := by native_decide
example : partTable ⟨12, by norm_num⟩ < 2^12 := by native_decide
example : partTable ⟨13, by norm_num⟩ < 2^13 := by native_decide
example : partTable ⟨14, by norm_num⟩ < 2^14 := by native_decide
example : partTable ⟨15, by norm_num⟩ < 2^15 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §5. Derangements and the 1/e approximation
-- ─────────────────────────────────────────────────────────────────────────────

/-!
  D(n) = the number of derangements of n elements satisfies
    D(n)/n!  →  1/e  ≈  0.36787…

  Since 1/e ≈ 0.3679, we have  100·D(n)/n! ≈ 36.79, so
    36·n!  ≤  100·D(n)  ≤  37·n!   for n large enough.

  We verify both bounds for n = 4 .. 8.

  The recurrence D(n+2) = (n+1)·(D(n+1) + D(n)) is given as a table
  to avoid termination bookkeeping.
-/

/-- Derangement numbers D(0)=1, D(1)=0, D(2)=1, D(3)=2, …  stored as a table. -/
def derangTable : Fin 9 → ℕ := ![ 1, 0, 1, 2, 9, 44, 265, 1854, 14833 ]

-- Spot-checks
example : derangTable ⟨0, by norm_num⟩ = 1     := by native_decide
example : derangTable ⟨1, by norm_num⟩ = 0     := by native_decide
example : derangTable ⟨2, by norm_num⟩ = 1     := by native_decide
example : derangTable ⟨3, by norm_num⟩ = 2     := by native_decide
example : derangTable ⟨4, by norm_num⟩ = 9     := by native_decide
example : derangTable ⟨5, by norm_num⟩ = 44    := by native_decide
example : derangTable ⟨6, by norm_num⟩ = 265   := by native_decide
example : derangTable ⟨7, by norm_num⟩ = 1854  := by native_decide
example : derangTable ⟨8, by norm_num⟩ = 14833 := by native_decide

-- Verify recurrence D(n+2) = (n+1)*(D(n+1) + D(n)) for n = 0..6
-- (written as separate abbreviations to keep lines under 100 chars)
private abbrev dt (k : ℕ) (h : k < 9) : ℕ := derangTable ⟨k, h⟩

example : dt 2 (by norm_num) =
    1 * (dt 1 (by norm_num) + dt 0 (by norm_num)) := by native_decide
example : dt 3 (by norm_num) =
    2 * (dt 2 (by norm_num) + dt 1 (by norm_num)) := by native_decide
example : dt 4 (by norm_num) =
    3 * (dt 3 (by norm_num) + dt 2 (by norm_num)) := by native_decide
example : dt 5 (by norm_num) =
    4 * (dt 4 (by norm_num) + dt 3 (by norm_num)) := by native_decide
example : dt 6 (by norm_num) =
    5 * (dt 5 (by norm_num) + dt 4 (by norm_num)) := by native_decide
example : dt 7 (by norm_num) =
    6 * (dt 6 (by norm_num) + dt 5 (by norm_num)) := by native_decide
example : dt 8 (by norm_num) =
    7 * (dt 7 (by norm_num) + dt 6 (by norm_num)) := by native_decide

/-!
  1/e approximation:  36 * n! ≤ 100 * D(n) ≤ 38 * n!  for n = 4..8.
  (100/e ≈ 36.79, and for n=4 the ratio is 37.5, hence we need the
  upper constant to be 38 to cover the entire range.)
-/

-- Lower bound: 36 * n! ≤ 100 * D(n)
example : 36 * Nat.factorial 4 ≤ 100 * dt 4 (by norm_num) := by native_decide
example : 36 * Nat.factorial 5 ≤ 100 * dt 5 (by norm_num) := by native_decide
example : 36 * Nat.factorial 6 ≤ 100 * dt 6 (by norm_num) := by native_decide
example : 36 * Nat.factorial 7 ≤ 100 * dt 7 (by norm_num) := by native_decide
example : 36 * Nat.factorial 8 ≤ 100 * dt 8 (by norm_num) := by native_decide

-- Upper bound: 100 * D(n) ≤ 38 * n!
example : 100 * dt 4 (by norm_num) ≤ 38 * Nat.factorial 4 := by native_decide
example : 100 * dt 5 (by norm_num) ≤ 38 * Nat.factorial 5 := by native_decide
example : 100 * dt 6 (by norm_num) ≤ 38 * Nat.factorial 6 := by native_decide
example : 100 * dt 7 (by norm_num) ≤ 38 * Nat.factorial 7 := by native_decide
example : 100 * dt 8 (by norm_num) ≤ 38 * Nat.factorial 8 := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §6. Vandermonde / sum-of-binomials identity: Σ_{k=0}^n C(n,k) = 2^n
-- ─────────────────────────────────────────────────────────────────────────────

/-!
  The generating-function proof of C(2n,n) ~ 4^n/√(πn) ultimately relies on
  the evaluation of (1+z)^n at z=1, giving Σ C(n,k) = 2^n.
  We verify this for n = 1 .. 10.
-/

example : ∑ k ∈ Finset.range (1+1),  Nat.choose 1  k = 2^1  := by native_decide
example : ∑ k ∈ Finset.range (2+1),  Nat.choose 2  k = 2^2  := by native_decide
example : ∑ k ∈ Finset.range (3+1),  Nat.choose 3  k = 2^3  := by native_decide
example : ∑ k ∈ Finset.range (4+1),  Nat.choose 4  k = 2^4  := by native_decide
example : ∑ k ∈ Finset.range (5+1),  Nat.choose 5  k = 2^5  := by native_decide
example : ∑ k ∈ Finset.range (6+1),  Nat.choose 6  k = 2^6  := by native_decide
example : ∑ k ∈ Finset.range (7+1),  Nat.choose 7  k = 2^7  := by native_decide
example : ∑ k ∈ Finset.range (8+1),  Nat.choose 8  k = 2^8  := by native_decide
example : ∑ k ∈ Finset.range (9+1),  Nat.choose 9  k = 2^9  := by native_decide
example : ∑ k ∈ Finset.range (10+1), Nat.choose 10 k = 2^10 := by native_decide

end LaplaceMethod
