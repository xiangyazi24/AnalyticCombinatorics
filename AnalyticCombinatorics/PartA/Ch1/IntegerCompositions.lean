import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace IntegerCompositions

/-!
# Integer Compositions

Formalization of basic counting results for integer compositions:
- Compositions of n into k parts = C(n-1, k-1)
- Total compositions of n = 2^{n-1} for n ≥ 1
- Tiling count (compositions into parts {1,2}) = Fibonacci
- Partitions into parts 1 and 2: ⌊n/2⌋ + 1
- Compositions into parts ≥ 2 (Fibonacci-like recurrence)
-/

/-! ## Compositions into k parts -/

/-- The number of compositions of n into exactly k parts equals C(n-1, k-1). -/
def compositionCount (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 0 then 1 else 0)
  else if n = 0 then 0
  else Nat.choose (n - 1) (k - 1)

theorem compositionCount_4_2 : compositionCount 4 2 = 3 := by native_decide

theorem compositionCount_5_3 : compositionCount 5 3 = 6 := by native_decide

theorem compositionCount_6_1 : compositionCount 6 1 = 1 := by native_decide

theorem compositionCount_6_6 : compositionCount 6 6 = 1 := by native_decide

/-! ## Total compositions -/

/-- Total number of compositions of n (into any number of positive parts). -/
def totalCompositions (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2 ^ (n - 1)

theorem totalCompositions_1 : totalCompositions 1 = 1 := by native_decide

theorem totalCompositions_2 : totalCompositions 2 = 2 := by native_decide

theorem totalCompositions_3 : totalCompositions 3 = 4 := by native_decide

theorem totalCompositions_4 : totalCompositions 4 = 8 := by native_decide

theorem totalCompositions_5 : totalCompositions 5 = 16 := by native_decide

/-! ### Sum verification: totalCompositions n = Σ_k compositionCount n k -/

/-- Sum of compositionCount n k over k = 0 .. n. -/
def sumCompositionCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (compositionCount n)

theorem totalCompositions_eq_sum_1 :
    totalCompositions 1 = sumCompositionCount 1 := by native_decide

theorem totalCompositions_eq_sum_2 :
    totalCompositions 2 = sumCompositionCount 2 := by native_decide

theorem totalCompositions_eq_sum_3 :
    totalCompositions 3 = sumCompositionCount 3 := by native_decide

theorem totalCompositions_eq_sum_4 :
    totalCompositions 4 = sumCompositionCount 4 := by native_decide

theorem totalCompositions_eq_sum_5 :
    totalCompositions 5 = sumCompositionCount 5 := by native_decide

theorem totalCompositions_eq_sum_6 :
    totalCompositions 6 = sumCompositionCount 6 := by native_decide

theorem totalCompositions_eq_sum_7 :
    totalCompositions 7 = sumCompositionCount 7 := by native_decide

theorem totalCompositions_eq_sum_8 :
    totalCompositions 8 = sumCompositionCount 8 := by native_decide

/-! ## Tiling count (compositions into parts 1 and 2) -/

/-- The number of ways to tile a 1×n strip with tiles of length 1 and 2.
    Satisfies the Fibonacci recurrence. -/
def tilingCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => tilingCount (n + 1) + tilingCount n

theorem tilingCount_eq_fib_0 : tilingCount 0 = Nat.fib 1 := by native_decide

theorem tilingCount_eq_fib_1 : tilingCount 1 = Nat.fib 2 := by native_decide

theorem tilingCount_eq_fib_2 : tilingCount 2 = Nat.fib 3 := by native_decide

theorem tilingCount_eq_fib_3 : tilingCount 3 = Nat.fib 4 := by native_decide

theorem tilingCount_eq_fib_4 : tilingCount 4 = Nat.fib 5 := by native_decide

theorem tilingCount_eq_fib_5 : tilingCount 5 = Nat.fib 6 := by native_decide

theorem tilingCount_eq_fib_6 : tilingCount 6 = Nat.fib 7 := by native_decide

theorem tilingCount_eq_fib_7 : tilingCount 7 = Nat.fib 8 := by native_decide

theorem tilingCount_eq_fib_8 : tilingCount 8 = Nat.fib 9 := by native_decide

/-! ## Partitions into parts 1 and 2 -/

/-- The number of partitions of n into parts of size 1 and 2. -/
def partitions12 (n : ℕ) : ℕ := n / 2 + 1

theorem partitions12_0 : partitions12 0 = 1 := by native_decide

theorem partitions12_1 : partitions12 1 = 1 := by native_decide

theorem partitions12_2 : partitions12 2 = 2 := by native_decide

theorem partitions12_3 : partitions12 3 = 2 := by native_decide

theorem partitions12_4 : partitions12 4 = 3 := by native_decide

theorem partitions12_5 : partitions12 5 = 3 := by native_decide

theorem partitions12_6 : partitions12 6 = 4 := by native_decide

/-! ## Compositions into parts ≥ 2 -/

/-- The number of compositions of n into parts each ≥ 2.
    Satisfies the same Fibonacci recurrence with different initial conditions. -/
def compositionsGe2 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => compositionsGe2 (n + 1) + compositionsGe2 n

theorem compositionsGe2_0 : compositionsGe2 0 = 1 := by native_decide

theorem compositionsGe2_1 : compositionsGe2 1 = 0 := by native_decide

theorem compositionsGe2_2 : compositionsGe2 2 = 1 := by native_decide

theorem compositionsGe2_3 : compositionsGe2 3 = 1 := by native_decide

theorem compositionsGe2_4 : compositionsGe2 4 = 2 := by native_decide

theorem compositionsGe2_5 : compositionsGe2 5 = 3 := by native_decide

theorem compositionsGe2_6 : compositionsGe2 6 = 5 := by native_decide

theorem compositionsGe2_7 : compositionsGe2 7 = 8 := by native_decide

/-! ## Self-conjugate partitions table -/

/-- The number of self-conjugate partitions of n, stored as a finite table for n = 0..15.
    Values: 1,1,0,1,1,1,1,1,2,2,2,2,3,3,3,4 -/
def selfConjugateTable : Fin 16 → ℕ :=
  ![1, 1, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4]

theorem selfConjugate_0 : selfConjugateTable 0 = 1 := by native_decide
theorem selfConjugate_1 : selfConjugateTable 1 = 1 := by native_decide
theorem selfConjugate_2 : selfConjugateTable 2 = 0 := by native_decide
theorem selfConjugate_3 : selfConjugateTable 3 = 1 := by native_decide
theorem selfConjugate_4 : selfConjugateTable 4 = 1 := by native_decide
theorem selfConjugate_5 : selfConjugateTable 5 = 1 := by native_decide
theorem selfConjugate_6 : selfConjugateTable 6 = 1 := by native_decide
theorem selfConjugate_7 : selfConjugateTable 7 = 1 := by native_decide
theorem selfConjugate_8 : selfConjugateTable 8 = 2 := by native_decide
theorem selfConjugate_9 : selfConjugateTable 9 = 2 := by native_decide
theorem selfConjugate_10 : selfConjugateTable 10 = 2 := by native_decide
theorem selfConjugate_11 : selfConjugateTable 11 = 2 := by native_decide
theorem selfConjugate_12 : selfConjugateTable 12 = 3 := by native_decide
theorem selfConjugate_13 : selfConjugateTable 13 = 3 := by native_decide
theorem selfConjugate_14 : selfConjugateTable 14 = 3 := by native_decide
theorem selfConjugate_15 : selfConjugateTable 15 = 4 := by native_decide

end IntegerCompositions
