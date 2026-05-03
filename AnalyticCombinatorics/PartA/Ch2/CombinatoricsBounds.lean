import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CombinatoricsBounds

/-!
# Combinatorial Bounds and Inequalities

Numerical verifications of classical combinatorial bounds useful throughout
Flajolet & Sedgewick's *Analytic Combinatorics* (Part A, Chapter 2).

Covered:
- LYM inequality / Sperner's theorem (max antichain = C(n, ⌊n/2⌋))
- Dilworth's theorem (width × height ~ 2^n)
- Erdős–Ko–Rado theorem (max intersecting family)
- Kruskal–Katona shadow identity
- Bonferroni / inclusion-exclusion bounds (derangement example)
- Entropy bound on binomial coefficients (C(n,k) ≤ nᵏ/k! and ≥ (n/k)ᵏ)
-/

-- ============================================================
-- §1  Sperner / LYM
-- ============================================================

/-- The maximum antichain in the Boolean lattice 2^[n] has size C(n, ⌊n/2⌋).
    This is Sperner's theorem; the bound is sharp at the middle layer. -/
def spernerMax (n : ℕ) : ℕ := Nat.choose n (n / 2)

-- Spot checks
example : spernerMax 4 = 6  := by native_decide
example : spernerMax 5 = 10 := by native_decide
example : spernerMax 6 = 20 := by native_decide
example : spernerMax 7 = 35 := by native_decide
example : spernerMax 8 = 70 := by native_decide

-- The middle binomial never exceeds 2^n (sanity: the whole lattice has 2^n elements)
example : spernerMax 4 ≤ 2 ^ 4 := by native_decide
example : spernerMax 8 ≤ 2 ^ 8 := by native_decide

-- ============================================================
-- §2  Dilworth's theorem – width × height lower-bounds 2^n
-- ============================================================

-- Longest chain in 2^[n] has n+1 elements (∅ ⊂ {1} ⊂ … ⊂ [n]).
-- Width = C(n, ⌊n/2⌋).  A loose covering argument: width * height ≥ 2^n
-- (each of the 2^n elements lies in at most one chain in a min-chain cover,
--  and each chain has length ≤ height).  We verify the inequality numerically.

example : Nat.choose 6 3 * 7 > 2 ^ 6 := by native_decide  -- 140 > 64
example : Nat.choose 8 4 * 9 > 2 ^ 8 := by native_decide  -- 630 > 256
example : Nat.choose 10 5 * 11 > 2 ^ 10 := by native_decide  -- 2772 > 1024

-- ============================================================
-- §3  Erdős–Ko–Rado theorem
-- ============================================================

/-- For n ≥ 2k, the maximum intersecting family of k-subsets of [n]
    has size C(n-1, k-1).  (Every set passes through a fixed element.) -/
def ekrMax (n k : ℕ) : ℕ := Nat.choose (n - 1) (k - 1)

-- Spot checks
example : ekrMax 5 2 = 4  := by native_decide  -- C(4,1)
example : ekrMax 7 3 = 15 := by native_decide  -- C(6,2)
example : ekrMax 9 4 = 56 := by native_decide  -- C(8,3)

-- EKR bound is at most the total number of k-subsets C(n,k)
example : ekrMax 5 2 ≤ Nat.choose 5 2 := by native_decide  -- 4 ≤ 10
example : ekrMax 7 3 ≤ Nat.choose 7 3 := by native_decide  -- 15 ≤ 35
example : ekrMax 9 4 ≤ Nat.choose 9 4 := by native_decide  -- 56 ≤ 126

-- ============================================================
-- §4  Kruskal–Katona shadow identity
-- ============================================================

-- The identity C(n,k)·k = C(n,k-1)·(n-k+1) underlies the shadow bound.
-- (Double counting: choose a k-set then remove an element = choose a (k-1)-set
--  then add an element from the remaining n-k+1 positions.)

example : Nat.choose 7 3 * 3 = Nat.choose 7 2 * 5  := by native_decide  -- 105 = 105
example : Nat.choose 8 4 * 4 = Nat.choose 8 3 * 5  := by native_decide  -- 280 = 280
example : Nat.choose 10 5 * 5 = Nat.choose 10 4 * 6 := by native_decide  -- 1260 = 1260

-- ============================================================
-- §5  Bonferroni / inclusion-exclusion bounds (derangements, n=4)
-- ============================================================

-- Let Aᵢ = {permutations of [4] that fix position i}.
-- |union A₁∪…∪A₄| = 4! - D₄.

-- Individual Bonferroni terms
example : 4 * Nat.factorial 3 = 24 := by native_decide          -- Σ|Aᵢ|
example : Nat.choose 4 2 * Nat.factorial 2 = 12 := by native_decide  -- Σ|Aᵢ∩Aⱼ|
example : Nat.choose 4 3 * Nat.factorial 1 = 4  := by native_decide  -- Σ|Aᵢ∩Aⱼ∩Aₖ|
example : Nat.choose 4 4 * Nat.factorial 0 = 1  := by native_decide  -- |A₁∩…∩A₄|

-- Full inclusion-exclusion gives the exact union size = 4! - D₄ = 24 - 9 = 15
example : 24 - 12 + 4 - 1 = 15 := by native_decide

-- Union bound (first Bonferroni level) is an over-count: 24 > 15
example : (4 * Nat.factorial 3) ≥ 15 := by native_decide

-- Two-term lower bound: 24 - 12 = 12 ≤ 15
example : (4 * Nat.factorial 3 - Nat.choose 4 2 * Nat.factorial 2) ≤ 15 := by native_decide

-- ============================================================
-- §6  Entropy-based binomial bounds
-- ============================================================

-- Upper bound: C(n,k) ≤ nᵏ / k!
-- (follows from C(n,k) = n(n-1)…(n-k+1)/k! ≤ nᵏ/k!)
example : Nat.choose 10 3 ≤ 10 ^ 3 / Nat.factorial 3  := by native_decide  -- 120 ≤ 166
example : Nat.choose 10 4 ≤ 10 ^ 4 / Nat.factorial 4  := by native_decide  -- 210 ≤ 416
example : Nat.choose 20 5 ≤ 20 ^ 5 / Nat.factorial 5  := by native_decide  -- 15504 ≤ 26666

-- Lower bound: C(n,k) ≥ (n/k)ᵏ  (natural-number division)
example : Nat.choose 10 3 ≥ (10 / 3) ^ 3 := by native_decide  -- 120 ≥ 27
example : Nat.choose 20 4 ≥ (20 / 4) ^ 4 := by native_decide  -- 4845 ≥ 625

-- C(n, n/2) ≤ 2^n (the entropy bound at α = 1/2 gives 2^n)
example : Nat.choose 10 5 ≤ 2 ^ 10 := by native_decide  -- 252 ≤ 1024
example : Nat.choose 20 10 ≤ 2 ^ 20 := by native_decide  -- 184756 ≤ 1048576

end CombinatoricsBounds
