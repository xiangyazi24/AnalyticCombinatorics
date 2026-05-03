import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SaddlePointPartitions

/-!
Computable checks around the partition examples from the saddle-point chapter.
The analytic Hardy-Ramanujan formula is recorded as symbolic syntax; the
finite coefficient and ratio checks are executable.
-/

/-! ## Integer partitions -/

/-- The ordinary partition number `p(n)`, tabulated for `n = 0, ..., 15`. -/
def partitionCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 22
  | 9 => 30
  | 10 => 42
  | 11 => 56
  | 12 => 77
  | 13 => 101
  | 14 => 135
  | 15 => 176
  | _ => 0

/-- The table `p(0), ..., p(15)`. -/
def partitionTable : List Nat :=
  (List.range 16).map partitionCount

/-- Partition numbers `p(n)` for `n = 0, ..., 15`. -/
theorem partitionTable_values :
    partitionTable =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176] := by
  native_decide

theorem partitionCount_values_0_15 :
    partitionCount 0 = 1 ∧
    partitionCount 1 = 1 ∧
    partitionCount 2 = 2 ∧
    partitionCount 3 = 3 ∧
    partitionCount 4 = 5 ∧
    partitionCount 5 = 7 ∧
    partitionCount 6 = 11 ∧
    partitionCount 7 = 15 ∧
    partitionCount 8 = 22 ∧
    partitionCount 9 = 30 ∧
    partitionCount 10 = 42 ∧
    partitionCount 11 = 56 ∧
    partitionCount 12 = 77 ∧
    partitionCount 13 = 101 ∧
    partitionCount 14 = 135 ∧
    partitionCount 15 = 176 := by
  native_decide

/-! ## Hardy-Ramanujan saddle-point shape -/

/-- Symbolic expressions sufficient to record the Hardy-Ramanujan main term. -/
inductive AsymptoticTerm where
  | partitionP
  | n
  | nat (m : Nat)
  | pi
  | sqrt (t : AsymptoticTerm)
  | exp (t : AsymptoticTerm)
  | mul (a b : AsymptoticTerm)
  | div (a b : AsymptoticTerm)
  deriving DecidableEq, Repr

inductive AsymptoticRelation where
  | equivalent
  deriving DecidableEq, Repr

/-- A symbolic asymptotic equivalence. -/
structure AsymptoticStatement where
  lhs : AsymptoticTerm
  relation : AsymptoticRelation
  rhs : AsymptoticTerm
  deriving DecidableEq, Repr

/-- The main term `(1 / (4 n sqrt 3)) * exp (pi * sqrt (2 n / 3))`. -/
def hardyRamanujanMainTerm : AsymptoticTerm :=
  .mul
    (.div
      (.nat 1)
      (.mul (.mul (.nat 4) .n) (.sqrt (.nat 3))))
    (.exp
      (.mul
        .pi
        (.sqrt (.div (.mul (.nat 2) .n) (.nat 3)))))

/-- Symbolic record of `p(n) ~ (1/(4n sqrt 3)) * exp(pi sqrt(2n/3))`. -/
def hardyRamanujanAsymptotic : AsymptoticStatement where
  lhs := .partitionP
  relation := .equivalent
  rhs := hardyRamanujanMainTerm

theorem hardyRamanujanAsymptotic_shape :
    hardyRamanujanAsymptotic =
      { lhs := .partitionP
        relation := .equivalent
        rhs :=
          .mul
            (.div
              (.nat 1)
              (.mul (.mul (.nat 4) .n) (.sqrt (.nat 3))))
            (.exp
              (.mul
                .pi
                (.sqrt (.div (.mul (.nat 2) .n) (.nat 3))))) } := by
  native_decide

/-- Consecutive partition-number ratio `p(n+1) / p(n)`, as a rational number. -/
def partitionRatio (n : Nat) : Rat :=
  (partitionCount (n + 1) : Rat) / (partitionCount n : Rat)

/-- Exact small ratios `p(n+1)/p(n)`. -/
theorem partitionRatio_values_0_14 :
    partitionRatio 0 = 1 ∧
    partitionRatio 1 = 2 ∧
    partitionRatio 2 = 3 / 2 ∧
    partitionRatio 3 = 5 / 3 ∧
    partitionRatio 4 = 7 / 5 ∧
    partitionRatio 5 = 11 / 7 ∧
    partitionRatio 6 = 15 / 11 ∧
    partitionRatio 7 = 22 / 15 ∧
    partitionRatio 8 = 15 / 11 ∧
    partitionRatio 9 = 7 / 5 ∧
    partitionRatio 10 = 4 / 3 ∧
    partitionRatio 11 = 11 / 8 ∧
    partitionRatio 12 = 101 / 77 ∧
    partitionRatio 13 = 135 / 101 ∧
    partitionRatio 14 = 176 / 135 := by
  native_decide

/-- Finite growth checks for the tabulated ratios. -/
theorem partitionRatio_growth_checks :
    partitionRatio 0 = 1 ∧
    1 < partitionRatio 1 ∧ partitionRatio 1 ≤ 2 ∧
    1 < partitionRatio 2 ∧ partitionRatio 2 ≤ 2 ∧
    1 < partitionRatio 3 ∧ partitionRatio 3 ≤ 2 ∧
    1 < partitionRatio 4 ∧ partitionRatio 4 ≤ 2 ∧
    1 < partitionRatio 5 ∧ partitionRatio 5 ≤ 2 ∧
    1 < partitionRatio 6 ∧ partitionRatio 6 ≤ 2 ∧
    1 < partitionRatio 7 ∧ partitionRatio 7 ≤ 2 ∧
    1 < partitionRatio 8 ∧ partitionRatio 8 ≤ 2 ∧
    1 < partitionRatio 9 ∧ partitionRatio 9 ≤ 2 ∧
    1 < partitionRatio 10 ∧ partitionRatio 10 ≤ 2 ∧
    1 < partitionRatio 11 ∧ partitionRatio 11 ≤ 2 ∧
    1 < partitionRatio 12 ∧ partitionRatio 12 ≤ 2 ∧
    1 < partitionRatio 13 ∧ partitionRatio 13 ≤ 2 ∧
    1 < partitionRatio 14 ∧ partitionRatio 14 ≤ 2 := by
  native_decide

/-! ## Restricted partitions -/

/-- Number of partitions of `n` using only parts at most `k`, for the
small Chapter VIII checks `k = 2, 3, 4` and `n = 0, ..., 10`. -/
def restrictedPartitionCount : Nat → Nat → Nat
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 2
  | 2, 3 => 2
  | 2, 4 => 3
  | 2, 5 => 3
  | 2, 6 => 4
  | 2, 7 => 4
  | 2, 8 => 5
  | 2, 9 => 5
  | 2, 10 => 6
  | 3, 0 => 1
  | 3, 1 => 1
  | 3, 2 => 2
  | 3, 3 => 3
  | 3, 4 => 4
  | 3, 5 => 5
  | 3, 6 => 7
  | 3, 7 => 8
  | 3, 8 => 10
  | 3, 9 => 12
  | 3, 10 => 14
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 4, 4 => 5
  | 4, 5 => 6
  | 4, 6 => 9
  | 4, 7 => 11
  | 4, 8 => 15
  | 4, 9 => 18
  | 4, 10 => 23
  | _, _ => 0

/-- Partitions using only parts at most `2`, for `n = 0, ..., 10`. -/
theorem restrictedParts_le_two_values :
    restrictedPartitionCount 2 0 = 1 ∧
    restrictedPartitionCount 2 1 = 1 ∧
    restrictedPartitionCount 2 2 = 2 ∧
    restrictedPartitionCount 2 3 = 2 ∧
    restrictedPartitionCount 2 4 = 3 ∧
    restrictedPartitionCount 2 5 = 3 ∧
    restrictedPartitionCount 2 6 = 4 ∧
    restrictedPartitionCount 2 7 = 4 ∧
    restrictedPartitionCount 2 8 = 5 ∧
    restrictedPartitionCount 2 9 = 5 ∧
    restrictedPartitionCount 2 10 = 6 := by
  native_decide

/-- Partitions using only parts at most `3`, for `n = 0, ..., 10`. -/
theorem restrictedParts_le_three_values :
    restrictedPartitionCount 3 0 = 1 ∧
    restrictedPartitionCount 3 1 = 1 ∧
    restrictedPartitionCount 3 2 = 2 ∧
    restrictedPartitionCount 3 3 = 3 ∧
    restrictedPartitionCount 3 4 = 4 ∧
    restrictedPartitionCount 3 5 = 5 ∧
    restrictedPartitionCount 3 6 = 7 ∧
    restrictedPartitionCount 3 7 = 8 ∧
    restrictedPartitionCount 3 8 = 10 ∧
    restrictedPartitionCount 3 9 = 12 ∧
    restrictedPartitionCount 3 10 = 14 := by
  native_decide

/-- Partitions using only parts at most `4`, for `n = 0, ..., 10`. -/
theorem restrictedParts_le_four_values :
    restrictedPartitionCount 4 0 = 1 ∧
    restrictedPartitionCount 4 1 = 1 ∧
    restrictedPartitionCount 4 2 = 2 ∧
    restrictedPartitionCount 4 3 = 3 ∧
    restrictedPartitionCount 4 4 = 5 ∧
    restrictedPartitionCount 4 5 = 6 ∧
    restrictedPartitionCount 4 6 = 9 ∧
    restrictedPartitionCount 4 7 = 11 ∧
    restrictedPartitionCount 4 8 = 15 ∧
    restrictedPartitionCount 4 9 = 18 ∧
    restrictedPartitionCount 4 10 = 23 := by
  native_decide

/-! ## Distinct parts -/

/-- Number of partitions of `n` into distinct parts, tabulated initially. -/
def distinctPartitionCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | _ => 0

theorem distinctPartitionCount_values_0_6 :
    distinctPartitionCount 0 = 1 ∧
    distinctPartitionCount 1 = 1 ∧
    distinctPartitionCount 2 = 1 ∧
    distinctPartitionCount 3 = 2 ∧
    distinctPartitionCount 4 = 2 ∧
    distinctPartitionCount 5 = 3 ∧
    distinctPartitionCount 6 = 4 := by
  native_decide

/-! ## Plane partitions -/

/-- Initial plane-partition numbers `pp(n)`. -/
def planePartitionCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 6
  | 4 => 13
  | 5 => 24
  | _ => 0

theorem planePartitionCount_values_0_5 :
    planePartitionCount 0 = 1 ∧
    planePartitionCount 1 = 1 ∧
    planePartitionCount 2 = 3 ∧
    planePartitionCount 3 = 6 ∧
    planePartitionCount 4 = 13 ∧
    planePartitionCount 5 = 24 := by
  native_decide

/-! ## Self-conjugate partitions -/

/-- Number of partitions of `n` into distinct odd parts, tabulated initially. -/
def distinctOddPartsPartitionCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 3
  | _ => 0

/-- Number of self-conjugate partitions of `n`. -/
def selfConjugatePartitionCount (n : Nat) : Nat :=
  distinctOddPartsPartitionCount n

theorem selfConjugate_eq_distinctOddParts_values_0_12 :
    selfConjugatePartitionCount 0 = distinctOddPartsPartitionCount 0 ∧
    selfConjugatePartitionCount 1 = distinctOddPartsPartitionCount 1 ∧
    selfConjugatePartitionCount 2 = distinctOddPartsPartitionCount 2 ∧
    selfConjugatePartitionCount 3 = distinctOddPartsPartitionCount 3 ∧
    selfConjugatePartitionCount 4 = distinctOddPartsPartitionCount 4 ∧
    selfConjugatePartitionCount 5 = distinctOddPartsPartitionCount 5 ∧
    selfConjugatePartitionCount 6 = distinctOddPartsPartitionCount 6 ∧
    selfConjugatePartitionCount 7 = distinctOddPartsPartitionCount 7 ∧
    selfConjugatePartitionCount 8 = distinctOddPartsPartitionCount 8 ∧
    selfConjugatePartitionCount 9 = distinctOddPartsPartitionCount 9 ∧
    selfConjugatePartitionCount 10 = distinctOddPartsPartitionCount 10 ∧
    selfConjugatePartitionCount 11 = distinctOddPartsPartitionCount 11 ∧
    selfConjugatePartitionCount 12 = distinctOddPartsPartitionCount 12 := by
  native_decide

theorem selfConjugatePartitionCount_values_0_12 :
    selfConjugatePartitionCount 0 = 1 ∧
    selfConjugatePartitionCount 1 = 1 ∧
    selfConjugatePartitionCount 2 = 0 ∧
    selfConjugatePartitionCount 3 = 1 ∧
    selfConjugatePartitionCount 4 = 1 ∧
    selfConjugatePartitionCount 5 = 1 ∧
    selfConjugatePartitionCount 6 = 1 ∧
    selfConjugatePartitionCount 7 = 1 ∧
    selfConjugatePartitionCount 8 = 2 ∧
    selfConjugatePartitionCount 9 = 2 ∧
    selfConjugatePartitionCount 10 = 2 ∧
    selfConjugatePartitionCount 11 = 2 ∧
    selfConjugatePartitionCount 12 = 3 := by
  native_decide

end SaddlePointPartitions
