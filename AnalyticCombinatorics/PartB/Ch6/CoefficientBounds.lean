/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VI — Numerical verifications of coefficient bounds from singularity analysis.

  References: Flajolet & Sedgewick, Analytic Combinatorics (2009), Chapter VI.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CoefficientBounds

-- ============================================================
-- §1  Catalan numbers and Darboux-type bounds
-- ============================================================

/-- Catalan numbers: C_n = C(2n,n)/(n+1). -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Spot-check values
example : catalan 0 = 1  := by native_decide
example : catalan 1 = 1  := by native_decide
example : catalan 2 = 2  := by native_decide
example : catalan 3 = 5  := by native_decide
example : catalan 4 = 14 := by native_decide
example : catalan 5 = 42 := by native_decide

-- Weaker Darboux bound: C_n * n < 4^n for n ≥ 2.
-- (The sharp asymptotics give C_n ~ 4^n / (n^{3/2} √π),
--  so this is much weaker than the true rate.)
example : catalan 2 * 2 < 4 ^ 2 := by native_decide  -- 4  < 16
example : catalan 3 * 3 < 4 ^ 3 := by native_decide  -- 15 < 64
example : catalan 4 * 4 < 4 ^ 4 := by native_decide  -- 56 < 256
example : catalan 5 * 5 < 4 ^ 5 := by native_decide  -- 210 < 1024
example : catalan 6 * 6 < 4 ^ 6 := by native_decide  -- 792 < 4096
example : catalan 7 * 7 < 4 ^ 7 := by native_decide  -- 3003 < 16384
example : catalan 8 * 8 < 4 ^ 8 := by native_decide  -- 11440 < 65536

-- ============================================================
-- §2  Negative-binomial / power-series coefficients
-- ============================================================

/-- Coefficient of z^n in 1/(1-z)^k (negative-binomial coefficient).
    Equals C(n+k-1, k-1). -/
def negBinCoeff (n k : ℕ) : ℕ := Nat.choose (n + k - 1) (k - 1)

-- For k=1: constant generating function 1/(1-z) → coefficient = 1.
example : negBinCoeff 0 1 = 1 := by native_decide
example : negBinCoeff 3 1 = 1 := by native_decide
example : negBinCoeff 9 1 = 1 := by native_decide

-- For k=2: 1/(1-z)^2 → coefficient of z^n is n+1.
example : negBinCoeff 0 2 = 1  := by native_decide
example : negBinCoeff 1 2 = 2  := by native_decide
example : negBinCoeff 2 2 = 3  := by native_decide
example : negBinCoeff 3 2 = 4  := by native_decide
example : negBinCoeff 4 2 = 5  := by native_decide
example : negBinCoeff 5 2 = 6  := by native_decide

-- For k=3: 1/(1-z)^3 → coefficient of z^n is C(n+2,2) = (n+1)(n+2)/2.
example : negBinCoeff 0 3 = 1  := by native_decide
example : negBinCoeff 1 3 = 3  := by native_decide
example : negBinCoeff 2 3 = 6  := by native_decide
example : negBinCoeff 3 3 = 10 := by native_decide
example : negBinCoeff 4 3 = 15 := by native_decide
example : negBinCoeff 5 3 = 21 := by native_decide  -- C(7,2)=21
example : negBinCoeff 10 3 = 66 := by native_decide  -- C(12,2)=66

-- ============================================================
-- §3  Ratio of consecutive Catalan numbers
-- ============================================================

-- The recurrence C_{n+1}/C_n = (4n+2)/(n+2) → 4  as n → ∞.
-- For finite n the ratio is strictly less than 4:
--   4n+2 < 4(n+2) = 4n+8  ✓ for all n.

example : ∀ n : Fin 20, 4 * (n : ℕ) + 2 < 4 * ((n : ℕ) + 2) := by native_decide

-- Equivalently, C_{n+1}*(n+2) < 4*C_n*(n+1) for small n.
example : catalan 2 * 3 < 4 * catalan 1 * 2 := by native_decide  -- 6 < 8... wait: 2*3=6, 4*1*2=8 ✓
example : catalan 3 * 4 < 4 * catalan 2 * 3 := by native_decide  -- 20 < 24 ✓
example : catalan 4 * 5 < 4 * catalan 3 * 4 := by native_decide  -- 70 < 80 ✓
example : catalan 5 * 6 < 4 * catalan 4 * 5 := by native_decide  -- 252 < 280 ✓
example : catalan 6 * 7 < 4 * catalan 5 * 6 := by native_decide  -- 924 < 1008 ✓

-- ============================================================
-- §4  Bell numbers and Hayman admissibility bounds
-- ============================================================

/-- Bell numbers B_n (small table). -/
def bellCoeff (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 15
  | 5 => 52
  | 6 => 203
  | 7 => 877
  | _ => 0  -- table ends at n=7

-- Strict monotonicity: B_{n+1} > B_n for n ≥ 1.
-- (B_0 = B_1 = 1, so the strict jump starts at n=1.)
example : bellCoeff 1 = bellCoeff 0 := by native_decide  -- both = 1
example : bellCoeff 2 > bellCoeff 1 := by native_decide
example : bellCoeff 3 > bellCoeff 2 := by native_decide
example : bellCoeff 4 > bellCoeff 3 := by native_decide
example : bellCoeff 5 > bellCoeff 4 := by native_decide
example : bellCoeff 6 > bellCoeff 5 := by native_decide
example : bellCoeff 7 > bellCoeff 6 := by native_decide

-- Super-exponential lower bound: B_n > 2^n / 3 for n ≥ 4.
-- (Integer arithmetic: B_n * 3 > 2^n.)
example : bellCoeff 4 * 3 > 2 ^ 4 := by native_decide  -- 45 > 16
example : bellCoeff 5 * 3 > 2 ^ 5 := by native_decide  -- 156 > 32
example : bellCoeff 6 * 3 > 2 ^ 6 := by native_decide  -- 609 > 64
example : bellCoeff 7 * 3 > 2 ^ 7 := by native_decide  -- 2631 > 128

-- Equivalently: B_n > 2^n / 3 verified as B_n > ⌊2^n / 3⌋.
example : bellCoeff 4 > 2 ^ 4 / 3 := by native_decide  -- 15 > 5
example : bellCoeff 5 > 2 ^ 5 / 3 := by native_decide  -- 52 > 10
example : bellCoeff 6 > 2 ^ 6 / 3 := by native_decide  -- 203 > 21

-- Loose growth bound: B_{n+1} ≤ 4 * B_n for n ≤ 5 (the ratio approaches ~4.3 by n=6).
-- For n ∈ Fin 6 (i.e. n = 0..5), B_{n+1} ≤ 4 * B_n holds.
example : ∀ n : Fin 6, bellCoeff (n + 1) ≤ 4 * bellCoeff n := by native_decide

-- ============================================================
-- §5  Transfer theorem: central binomial coefficients
-- ============================================================

-- [z^n](1-z)^{-1/2} = C(2n,n)/4^n.
-- As integers, 4^n * [z^n](1-z)^{-1/2} = C(2n,n).

-- Spot-check central binomial coefficients.
example : Nat.choose 10 5  = 252    := by native_decide
example : Nat.choose 12 6  = 924    := by native_decide
example : Nat.choose 16 8  = 12870  := by native_decide
example : Nat.choose 20 10 = 184756 := by native_decide

-- Upper bound: C(2n,n) < 4^n  (strict for n ≥ 1).
example : Nat.choose 2  1  < 4 ^ 1  := by native_decide  -- 2 < 4
example : Nat.choose 4  2  < 4 ^ 2  := by native_decide  -- 6 < 16
example : Nat.choose 10 5  < 4 ^ 5  := by native_decide  -- 252 < 1024
example : Nat.choose 14 7  < 4 ^ 7  := by native_decide  -- 3432 < 16384
example : Nat.choose 20 10 < 4 ^ 10 := by native_decide  -- 184756 < 1048576

-- Lower bound: C(2n,n) > 4^n / (2n)  i.e.  C(2n,n) * (2n) > 4^n, for n ≥ 2.
-- (At n=1: C(2,1)*2 = 4 = 4^1, so equality holds; the strict bound starts at n=2.)
example : Nat.choose 4  2  * 4  > 4 ^ 2  := by native_decide  -- 24 > 16
example : Nat.choose 10 5  * 10 > 4 ^ 5  := by native_decide  -- 2520 > 1024
example : Nat.choose 14 7  * 14 > 4 ^ 7  := by native_decide  -- 48048 > 16384
example : Nat.choose 20 10 * 20 > 4 ^ 10 := by native_decide  -- 3695120 > 1048576

-- ============================================================
-- §6  Radius of convergence via the ratio test
-- ============================================================

-- For a_n = 2^n: a_{n+1} / a_n = 2 exactly.
example : ∀ n : Fin 10, 2 ^ ((n : ℕ) + 1) = 2 * 2 ^ (n : ℕ) := by native_decide

-- For a_n = n!: a_{n+1} / a_n = n+1 (ratio diverges, r = 0).
example : ∀ n : Fin 8,
    Nat.factorial ((n : ℕ) + 1) = ((n : ℕ) + 1) * Nat.factorial (n : ℕ) := by
  native_decide

-- For a_n = 3^n: ratio = 3.
example : ∀ n : Fin 10, 3 ^ ((n : ℕ) + 1) = 3 * 3 ^ (n : ℕ) := by native_decide

-- For a_n = C_n (Catalan): ratio approaches 4 from below.
-- Verified in §3 above; collect one more explicit instance here.
example : catalan 10 * 12 < 4 * catalan 9 * 11 := by native_decide

-- Geometric bound: a_n = n * 2^n grows faster than 2^n but has the same radius.
-- (n * 2^n) / (2^n) = n; ratio test: (n+1)*2^{n+1} / (n*2^n) = 2*(n+1)/n → 2.
-- Integer check: 2*(n+1)*catalan n < 4*catalan n*(n+1)... too trivial.
-- Instead just confirm: (n+1)*2^(n+1) > n*2^n for all n ≥ 1.
example : ∀ n : Fin 10, ((n : ℕ) + 1) * 2 ^ ((n : ℕ) + 1) > (n : ℕ) * 2 ^ (n : ℕ) := by
  native_decide

end CoefficientBounds
