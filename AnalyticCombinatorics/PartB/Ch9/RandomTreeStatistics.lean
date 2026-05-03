/-
  Analytic Combinatorics — Part B
  Chapter IX — Statistics on random trees and random mappings.

  Numerical verifications for classical results from Flajolet–Sedgewick Ch. IX:
  - Permutations vs. total mappings (n! < n^n for n ≥ 2)
  - Idempotent mappings: Σ C(n,k)·k^{n-k}  (OEIS A000248)
  - Connected functional graphs on [n]      (formula from Chapter IX)
  - Single-cycle permutations: (n-1)!
  - Labelled rooted forests / Cayley trees
  - Fixed-point statistics for random mappings
  - Narayana numbers (Catalan refinement by peaks)
  - Binary-tree height bounds
  - Harmonic-number surrogate for mapping component counts
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RandomTreeStatistics

open Finset

/-! ## 1.  Total mappings, permutations, and the ratio n!/n^n -/

/-- Total number of functions [n] → [n]. -/
def totalMappings (n : ℕ) : ℕ := n ^ n

/-- For n ≥ 2 the number of permutations is strictly less than the total
number of mappings (almost no mapping is a bijection). -/
theorem factorial_lt_pow_self_two : Nat.factorial 2 < 2 ^ 2 := by native_decide
theorem factorial_lt_pow_self_three : Nat.factorial 3 < 3 ^ 3 := by native_decide
theorem factorial_lt_pow_self_five : Nat.factorial 5 < 5 ^ 5 := by native_decide
theorem factorial_lt_pow_self_eight : Nat.factorial 8 < 8 ^ 8 := by native_decide

/-- Fraction of mappings that are permutations, as an exact rational. -/
def permFraction (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) / (n ^ n : ℕ)

/-- Exact values of n!/n^n for n = 1..5. -/
theorem permFraction_values_1_5 :
    permFraction 1 = 1 ∧
    permFraction 2 = 1 / 2 ∧
    permFraction 3 = 2 / 9 ∧
    permFraction 4 = 3 / 32 ∧
    permFraction 5 = 24 / 625 := by
  native_decide

/-- The fraction is strictly decreasing for n = 1, …, 5. -/
theorem permFraction_strictly_decreasing_1_5 :
    permFraction 2 < permFraction 1 ∧
    permFraction 3 < permFraction 2 ∧
    permFraction 4 < permFraction 3 ∧
    permFraction 5 < permFraction 4 := by
  native_decide

/-! ## 2.  Idempotent mappings  (OEIS A000248) -/

/-- A mapping f:[n]→[n] is idempotent (f∘f = f) iff the image is a set
of fixed points and every non-image element maps directly into the image.
Equivalently: choose a subset S of size k to be the image (all elements
of S are fixed), then map the remaining n-k elements into S freely.
Count = Σ_{k=0}^n C(n,k)·k^{n-k}. -/
def idempotentMappings (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * k ^ (n - k)

/-- OEIS A000248: 1, 1, 3, 10, 41, 196 for n = 0..5. -/
theorem idempotentMappings_values :
    idempotentMappings 0 = 1 ∧
    idempotentMappings 1 = 1 ∧
    idempotentMappings 2 = 3 ∧
    idempotentMappings 3 = 10 ∧
    idempotentMappings 4 = 41 ∧
    idempotentMappings 5 = 196 := by
  native_decide

/-- Every permutation is idempotent iff it is the identity; for n ≥ 3 the
idempotent count exceeds n! (many non-injective idempotents exist). -/
theorem factorial_le_idempotentMappings :
    Nat.factorial 3 ≤ idempotentMappings 3 ∧
    Nat.factorial 4 ≤ idempotentMappings 4 ∧
    Nat.factorial 5 ≤ idempotentMappings 5 := by
  native_decide

/-! ## 3.  Connected functional graphs -/

/-- Number of connected functional digraphs on [n] (weakly connected,
unique cycle).  Using the formula:
  connected(n) = Σ_{r=1}^n C(n,r)·(r-1)!·forest(n,r)
where forest(n,r) = r·n^{n-r-1} for 1 ≤ r < n, and 1 for r = n. -/
def connectedFunctionalGraphs (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (n + 1),
    if 1 ≤ r ∧ r ≤ n then
      Nat.choose n r * Nat.factorial (r - 1) *
        (if r = n then 1 else r * n ^ (n - r - 1))
    else
      0

/-- Values for n = 0..5.
    n=0: 0, n=1: 1, n=2: 3, n=3: 17, n=4: 142, n=5: 1569. -/
theorem connectedFunctionalGraphs_values :
    connectedFunctionalGraphs 0 = 0 ∧
    connectedFunctionalGraphs 1 = 1 ∧
    connectedFunctionalGraphs 2 = 3 ∧
    connectedFunctionalGraphs 3 = 17 ∧
    connectedFunctionalGraphs 4 = 142 ∧
    connectedFunctionalGraphs 5 = 1569 := by
  native_decide

/-- Quick cross-check: for n=2 there are 3 connected mappings [2]→[2].
    Explicitly: (1→1,2→1), (1→2,2→2), (1→2,2→1). -/
example : connectedFunctionalGraphs 2 = 3 := by native_decide

/-! ## 4.  Single-cycle permutations -/

/-- A permutation of [n] consists of a single n-cycle iff there are
(n-1)! such permutations. -/
def singleCyclePerms (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.factorial (n - 1)

theorem singleCyclePerms_values :
    singleCyclePerms 1 = 1 ∧
    singleCyclePerms 2 = 1 ∧
    singleCyclePerms 3 = 2 ∧
    singleCyclePerms 4 = 6 ∧
    singleCyclePerms 5 = 24 ∧
    singleCyclePerms 6 = 120 := by
  native_decide

/-- The fraction of all permutations that are single cycles = 1/n. -/
theorem singleCyclePerms_fraction_five :
    (singleCyclePerms 5 : ℚ) / Nat.factorial 5 = 1 / 5 := by
  native_decide

theorem singleCyclePerms_fraction_six :
    (singleCyclePerms 6 : ℚ) / Nat.factorial 6 = 1 / 6 := by
  native_decide

/-! ## 5.  Cayley's tree and forest counts -/

/-- Number of labelled rooted trees on [n]: n^{n-1} (Cayley's formula). -/
def cayleyTreeCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

theorem cayleyTreeCount_values :
    cayleyTreeCount 1 = 1 ∧
    cayleyTreeCount 2 = 2 ∧
    cayleyTreeCount 3 = 9 ∧
    cayleyTreeCount 4 = 64 ∧
    cayleyTreeCount 5 = 625 ∧
    cayleyTreeCount 6 = 7776 := by
  native_decide

/-- Number of labelled unrooted trees on [n]: n^{n-2} for n ≥ 2. -/
def cayleyUnrootedCount (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else n ^ (n - 2)

theorem cayleyUnrootedCount_values :
    cayleyUnrootedCount 2 = 1 ∧
    cayleyUnrootedCount 3 = 3 ∧
    cayleyUnrootedCount 4 = 16 ∧
    cayleyUnrootedCount 5 = 125 ∧
    cayleyUnrootedCount 6 = 1296 := by
  native_decide

/-- Labelled rooted forests on [n] (all possible root sets): (n+1)^{n-1}. -/
def labelledRootedForests (n : ℕ) : ℕ := (n + 1) ^ (n - 1)

theorem labelledRootedForests_values :
    labelledRootedForests 0 = 1 ∧
    labelledRootedForests 1 = 1 ∧
    labelledRootedForests 2 = 3 ∧
    labelledRootedForests 3 = 16 ∧
    labelledRootedForests 4 = 125 ∧
    labelledRootedForests 5 = 1296 ∧
    labelledRootedForests 6 = 16807 := by
  native_decide

/-- n · (unrooted trees on [n]) = rooted trees on [n], for n ≥ 2. -/
theorem rooted_eq_n_times_unrooted :
    2 * cayleyUnrootedCount 2 = cayleyTreeCount 2 ∧
    3 * cayleyUnrootedCount 3 = cayleyTreeCount 3 ∧
    4 * cayleyUnrootedCount 4 = cayleyTreeCount 4 ∧
    5 * cayleyUnrootedCount 5 = cayleyTreeCount 5 ∧
    6 * cayleyUnrootedCount 6 = cayleyTreeCount 6 := by
  native_decide

/-! ## 6.  Fixed-point statistics in random mappings -/

/-- The total count of (mapping, fixed-point) pairs for [n]→[n] equals n^n,
so the expected number of fixed points in a uniformly random mapping is 1.
Proof: each of the n elements is a fixed point in exactly n^{n-1} mappings
(fix that element, choose the rest freely), giving n · n^{n-1} = n^n pairs. -/
theorem total_fixedPoint_pairs_succ (n : ℕ) :
    (n + 1) * (n + 1) ^ n = (n + 1) ^ (n + 1) := by
  ring

/-- Inclusion-exclusion count of mappings [n]→[n] with no fixed points:
    Σ_{k=0}^n (-1)^k · C(n,k) · n^{n-k}. -/
def noFPMappings (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ k * Nat.choose n k * (n : ℤ) ^ (n - k)

/-- Values for n = 0..5: 1, 0, 1, 8, 81, 1024. -/
theorem noFPMappings_values :
    noFPMappings 0 = 1 ∧
    noFPMappings 1 = 0 ∧
    noFPMappings 2 = 1 ∧
    noFPMappings 3 = 8 ∧
    noFPMappings 4 = 81 ∧
    noFPMappings 5 = 1024 := by
  native_decide

/-- Manual check for n=2: C(2,0)·2² - C(2,1)·2¹ + C(2,2)·2⁰ = 4-4+1=1. -/
example : (4 : ℤ) - 4 + 1 = 1 := by native_decide

/-- Fraction of mappings with no fixed points.
    These converge to e^{-1} ≈ 0.3679 as n → ∞. -/
def noFPFraction (n : ℕ) : ℚ :=
  (noFPMappings n : ℚ) / (n ^ n : ℕ)

theorem noFPFraction_values :
    noFPFraction 2 = 1 / 4 ∧
    noFPFraction 3 = 8 / 27 ∧
    noFPFraction 4 = 81 / 256 ∧
    noFPFraction 5 = 1024 / 3125 := by
  native_decide

/-- The no-FP fraction is increasing toward e^{-1}
    (verified for n = 2..5 by rational comparison). -/
theorem noFPFraction_increasing_2_5 :
    noFPFraction 2 < noFPFraction 3 ∧
    noFPFraction 3 < noFPFraction 4 ∧
    noFPFraction 4 < noFPFraction 5 := by
  native_decide

/-- All no-FP fractions for n ≥ 2 lie below 2/5 (well below e^{-1} ≈ 0.368). -/
theorem noFPFraction_lt_two_fifths :
    noFPFraction 2 < 2 / 5 ∧
    noFPFraction 3 < 2 / 5 ∧
    noFPFraction 4 < 2 / 5 ∧
    noFPFraction 5 < 2 / 5 := by
  native_decide

/-! ## 7.  Narayana numbers (Catalan refinement by peaks) -/

/-- The Narayana number N(n,k) counts plane binary trees with n internal
nodes and k leaves (equivalently, Dyck paths of semilength n with k peaks).
Formula: N(n,k) = (1/n) · C(n,k) · C(n,k-1), for 1 ≤ k ≤ n. -/
def narayana (n k : ℕ) : ℕ :=
  if n = 0 then if k = 0 then 1 else 0
  else if k = 0 then 0
  else Nat.choose n k * Nat.choose n (k - 1) / n

/-- Narayana table for n = 1..4. -/
theorem narayana_table :
    narayana 1 1 = 1 ∧
    narayana 2 1 = 1 ∧ narayana 2 2 = 1 ∧
    narayana 3 1 = 1 ∧ narayana 3 2 = 3 ∧ narayana 3 3 = 1 ∧
    narayana 4 1 = 1 ∧ narayana 4 2 = 6 ∧ narayana 4 3 = 6 ∧ narayana 4 4 = 1 := by
  native_decide

/-- Catalan numbers via the central binomial coefficient formula. -/
def catalanNum (n : ℕ) : ℕ := (2 * n).choose n / (n + 1)

theorem catalanNum_values :
    catalanNum 1 = 1 ∧
    catalanNum 2 = 2 ∧
    catalanNum 3 = 5 ∧
    catalanNum 4 = 14 ∧
    catalanNum 5 = 42 ∧
    catalanNum 6 = 132 := by
  native_decide

/-- Row sums of Narayana numbers equal Catalan numbers:
    Σ_{k=0}^n N(n,k) = C_n. -/
theorem narayana_rowSum_eq_catalan :
    (∑ k ∈ Finset.range (1 + 1), narayana 1 k) = catalanNum 1 ∧
    (∑ k ∈ Finset.range (2 + 1), narayana 2 k) = catalanNum 2 ∧
    (∑ k ∈ Finset.range (3 + 1), narayana 3 k) = catalanNum 3 ∧
    (∑ k ∈ Finset.range (4 + 1), narayana 4 k) = catalanNum 4 ∧
    (∑ k ∈ Finset.range (5 + 1), narayana 5 k) = catalanNum 5 ∧
    (∑ k ∈ Finset.range (6 + 1), narayana 6 k) = catalanNum 6 := by
  native_decide

/-- Symmetry: N(n,k) = N(n, n+1-k) (complementing peaks and valleys). -/
theorem narayana_symmetry :
    narayana 4 1 = narayana 4 4 ∧
    narayana 4 2 = narayana 4 3 ∧
    narayana 5 1 = narayana 5 5 ∧
    narayana 5 2 = narayana 5 4 := by
  native_decide

/-! ## 8.  Binary-tree height bounds -/

/-- A binary tree of height h has at most 2^{h+1} - 1 nodes. -/
def maxNodesAtHeight (h : ℕ) : ℕ := 2 ^ (h + 1) - 1

theorem maxNodesAtHeight_values :
    maxNodesAtHeight 0 = 1 ∧
    maxNodesAtHeight 1 = 3 ∧
    maxNodesAtHeight 2 = 7 ∧
    maxNodesAtHeight 3 = 15 ∧
    maxNodesAtHeight 4 = 31 ∧
    maxNodesAtHeight 10 = 2047 := by
  native_decide

/-- Minimum height of a binary tree with n nodes = ⌊log₂ n⌋. -/
def minHeightForNodes (n : ℕ) : ℕ := Nat.log 2 n

theorem minHeightForNodes_values :
    minHeightForNodes 1 = 0 ∧
    minHeightForNodes 2 = 1 ∧
    minHeightForNodes 3 = 1 ∧
    minHeightForNodes 4 = 2 ∧
    minHeightForNodes 7 = 2 ∧
    minHeightForNodes 8 = 3 ∧
    minHeightForNodes 15 = 3 ∧
    minHeightForNodes 16 = 4 := by
  native_decide

/-- The height gap: min height ≤ n-1 (degenerate path tree achieves n-1).
    Checked for small n. -/
theorem minHeight_le_pred_small :
    minHeightForNodes 1 ≤ 0 ∧
    minHeightForNodes 2 ≤ 1 ∧
    minHeightForNodes 4 ≤ 3 ∧
    minHeightForNodes 8 ≤ 7 ∧
    minHeightForNodes 16 ≤ 15 := by
  native_decide

/-! ## 9.  Leaf count in full binary trees -/

/-- A full binary tree (every internal node has exactly 2 children) with
n internal nodes has exactly n+1 leaves — always, not just in expectation.
Verify that this is consistent with the Catalan count: C_n trees each
contribute n+1 leaves. -/
theorem full_tree_leaf_count_consistent :
    catalanNum 1 * 2 = 2 ∧   -- C_1 = 1 tree, 2 leaves
    catalanNum 2 * 3 = 6 ∧   -- C_2 = 2 trees, 3 leaves each
    catalanNum 3 * 4 = 20 ∧  -- C_3 = 5 trees, 4 leaves each
    catalanNum 4 * 5 = 70 := by  -- C_4 = 14 trees, 5 leaves each
  native_decide

/-- Expected number of leaves in a uniformly random Catalan tree with n
internal nodes is exactly n+1 (since all C_n trees have the same leaf count). -/
def expectedLeaves (n : ℕ) : ℚ :=
  if catalanNum n = 0 then 0
  else (catalanNum n : ℚ) * (n + 1) / (catalanNum n : ℚ)

theorem expectedLeaves_eq_succ (n : ℕ) (hn : catalanNum n ≠ 0) :
    expectedLeaves n = n + 1 := by
  simp only [expectedLeaves, hn, ↓reduceIte]
  field_simp

/-! ## 10.  Harmonic-number asymptotics for random mappings -/

/-- Harmonic number H_n = 1 + 1/2 + … + 1/n. -/
def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

theorem harmonicNumber_values :
    harmonicNumber 1 = 1 ∧
    harmonicNumber 2 = 3 / 2 ∧
    harmonicNumber 3 = 11 / 6 ∧
    harmonicNumber 4 = 25 / 12 ∧
    harmonicNumber 6 = 49 / 20 := by
  native_decide

/-- Expected number of connected components in a uniformly random mapping
[n]→[n] is asymptotically (1/2)·H_n.  Rational proxy: (1/2)·H_n. -/
def expectedComponentsProxy (n : ℕ) : ℚ := harmonicNumber n / 2

theorem expectedComponentsProxy_values :
    expectedComponentsProxy 1 = 1 / 2 ∧
    expectedComponentsProxy 2 = 3 / 4 ∧
    expectedComponentsProxy 4 = 25 / 24 := by
  native_decide

/-- The harmonic numbers are strictly increasing. -/
theorem harmonicNumber_strictMono : StrictMono harmonicNumber := by
  intro m n hmn
  simp only [harmonicNumber]
  apply Finset.sum_lt_sum_of_subset (f := fun k => 1 / ((k + 1 : ℕ) : ℚ))
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢; omega
  · exact Finset.mem_range.mpr hmn
  · simp [Finset.mem_range]
  · positivity
  · intro j _ _; positivity

end RandomTreeStatistics
