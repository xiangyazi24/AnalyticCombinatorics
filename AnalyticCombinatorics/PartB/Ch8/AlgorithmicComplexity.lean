/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VIII/IX — Average-case analysis of algorithms.

  This file verifies classical results on average-case complexity:
  Quicksort comparisons, BST path lengths, merge sort, binary search trees,
  hash table probing, and comparison-based sorting lower bounds.
  All checks use native_decide on concrete numerical instances.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AlgorithmicComplexity

/-! ## 1. Quicksort average comparisons

  The average number of comparisons for Quicksort on n elements is
  2(n+1)·Hₙ − 4n, where Hₙ = Σ_{k=1}^{n} 1/k is the n-th harmonic number.
-/

/-- Harmonic number H_n as a rational. -/
def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

/-- Average number of comparisons for Quicksort on n elements. -/
def quicksortAvg (n : ℕ) : ℚ :=
  2 * (n + 1 : ℚ) * harmonicNumber n - 4 * n

-- H_1 = 1, H_2 = 3/2, H_3 = 11/6, H_7 = 363/140
example : harmonicNumber 1 = 1 := by native_decide
example : harmonicNumber 2 = 3/2 := by native_decide
example : harmonicNumber 3 = 11/6 := by native_decide
example : harmonicNumber 7 = 363/140 := by native_decide

-- Quicksort: n=1 → 0, n=2 → 1, n=3 → 8/3
example : quicksortAvg 1 = 0 := by native_decide
example : quicksortAvg 2 = 1 := by native_decide
example : quicksortAvg 3 = 8/3 := by native_decide

-- Direct computation check for n=3
example : 2 * (3 + 1 : ℚ) * (11/6) - 4 * 3 = 8/3 := by native_decide

/-! ## 2. Binary search tree — Internal path length

  The internal path length (IPL) of a complete binary tree with n = 2^k − 1
  internal nodes satisfies IPL = (k−2)·2^k + 2.
  The sum of depths: for k=3 (7 nodes): 0+1+1+2+2+2+2 = 10.
-/

-- IPL of complete binary trees
example : 0 + 1 + 1 + 2 + 2 + 2 + 2 = 10 := by native_decide
example : (3 - 2) * 2^3 + 2 = 10 := by native_decide
example : (4 - 2) * 2^4 + 2 = 34 := by native_decide  -- 15-node tree
example : (5 - 2) * 2^5 + 2 = 98 := by native_decide  -- 31-node tree

/-! ## 3. BST average path length

  Average internal path length of a random BST on n nodes equals
  2(n+1)·Hₙ − 4n — the same formula as Quicksort!
  This reflects the correspondence between Quicksort partitioning and BST insertion.
-/

/-- Average IPL of random BST = Quicksort average comparisons. -/
def bstAvgIPL (n : ℕ) : ℚ := quicksortAvg n

-- For n=7: 2*8*(363/140) - 28 = 472/35
example : quicksortAvg 7 = 472/35 := by native_decide
example : 2 * (7 + 1 : ℚ) * (363/140) - 4 * 7 = 472/35 := by native_decide

-- Average depth ≈ IPL/n; for n=7: (472/35)/7 = 472/245
example : (472 : ℚ)/35 / 7 = 472/245 := by native_decide

/-! ## 4. Merge sort comparisons

  For n = 2^k, the merge sort comparison count satisfies
  C(n) = n·k − 2^k + 1 = n·log₂(n) − n + 1.
-/

example : 8 * 3 - 8 + 1 = 17 := by native_decide
example : 16 * 4 - 16 + 1 = 49 := by native_decide
example : 32 * 5 - 32 + 1 = 129 := by native_decide
example : 64 * 6 - 64 + 1 = 321 := by native_decide

/-- Merge sort comparisons for n = 2^k. -/
def mergeSortComparisons (k : ℕ) : ℕ := 2^k * k - 2^k + 1

example : mergeSortComparisons 3 = 17 := by native_decide
example : mergeSortComparisons 4 = 49 := by native_decide
example : mergeSortComparisons 5 = 129 := by native_decide
example : mergeSortComparisons 6 = 321 := by native_decide

/-! ## 5. Hash table — Linear probing expected probes

  For a hash table with load factor α, the expected number of probes
  for a successful search under linear probing is (1/2)(1 + 1/(1−α)).
-/

/-- Expected probes for successful search, linear probing. -/
def linearProbingSuccessful (α : ℚ) : ℚ := (1 : ℚ)/2 * (1 + 1/(1 - α))

-- α = 1/2: expected 3/2 probes
example : linearProbingSuccessful (1/2) = 3/2 := by native_decide
-- α = 2/3: expected 2 probes
example : linearProbingSuccessful (2/3) = 2 := by native_decide
-- α = 3/4: expected 5/2 probes
example : linearProbingSuccessful (3/4) = 5/2 := by native_decide

-- Direct computation checks
example : (1 : ℚ)/2 * (1 + 1/(1 - 1/2)) = 3/2 := by native_decide
example : (1 : ℚ)/2 * (1 + 1/(1 - 2/3)) = 2 := by native_decide
example : (1 : ℚ)/2 * (1 + 1/(1 - 3/4)) = 5/2 := by native_decide

/-! ## 6. Comparison-based sorting lower bound

  Any comparison-based sorting algorithm requires at least ⌊log₂(n!)⌋
  comparisons in the worst case. We verify Nat.log 2 (n!) for small n
  and show merge sort is close to optimal.
-/

-- Floor of log₂(n!) for various n
example : Nat.log 2 (Nat.factorial 4) = 4 := by native_decide   -- log₂(24) = 4
example : Nat.log 2 (Nat.factorial 5) = 6 := by native_decide   -- log₂(120) = 6
example : Nat.log 2 (Nat.factorial 8) = 15 := by native_decide  -- log₂(40320) = 15
example : Nat.log 2 (Nat.factorial 10) = 21 := by native_decide -- log₂(3628800) = 21

-- Merge sort (upper bound) ≥ information-theoretic lower bound
example : 17 ≥ Nat.log 2 (Nat.factorial 8) := by native_decide
example : 49 ≥ Nat.log 2 (Nat.factorial 16) := by native_decide

end AlgorithmicComplexity
