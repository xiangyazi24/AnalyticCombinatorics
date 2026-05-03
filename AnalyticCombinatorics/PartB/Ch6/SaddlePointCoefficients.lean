import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace SaddlePointCoefficients

/-!
# Saddle-point coefficient asymptotics

Computable checks around the saddle-point method for labelled structures,
following the Bell-number examples in Chapter VI of Analytic Combinatorics.
-/

/-- Bell numbers through their Stirling-number decomposition. -/
def stirling2 : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

/-- The Bell number `B(n)`. -/
def bellCount (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

/--
Bell saddle-point asymptotic schema:
`B(n) / ((n! / lambda^n) * exp(exp(lambda) - 1)) -> 1`,
where `lambda * exp(lambda) = n`.
-/
def bellSaddlePointAsymptotic : String :=
  "B(n) / ((n! / lambda^n) * exp(exp(lambda) - 1)) -> 1, where lambda * exp(lambda) = n"

/-- Exact Bell numbers `B(0), ..., B(10)`. -/
def bellNumbersExact : Fin 11 → Nat :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]

theorem bellNumbersExact_correct :
    ∀ n : Fin 11, bellCount n.val = bellNumbersExact n := by native_decide

/-- Right hand side of the Bell recurrence `B(n+1) = sum_k choose(n,k) B(k)`. -/
def bellRecurrenceRhs (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bellCount k

theorem bellRecurrence_verified_0_to_9 :
    ∀ n : Fin 10, bellCount (n.val + 1) = bellRecurrenceRhs n.val := by native_decide

/--
Stirling numbers for set partitions into blocks of size at least two.
The recurrence separates the block containing the last atom according to
whether it has size exactly two or larger.
-/
def stirling2NoSingletons : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, _ => 0
  | _ + 2, 0 => 0
  | n + 2, k + 1 =>
      (k + 1) * stirling2NoSingletons (n + 1) (k + 1) +
        (n + 1) * stirling2NoSingletons n k

/-- Number of set partitions of `n` labelled atoms with all blocks of size at least two. -/
def setPartitionsNoSingletons (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), stirling2NoSingletons n k

/-- The values for `n = 2, 3, 4`. -/
def setPartitionsNoSingletonsTwoToFour : Fin 3 → Nat :=
  ![1, 1, 4]

theorem setPartitionsNoSingletons_verified_2_to_4 :
    ∀ n : Fin 3, setPartitionsNoSingletons (n.val + 2) = setPartitionsNoSingletonsTwoToFour n :=
  by native_decide

/--
The four set partitions of `{1,2,3,4}` with all blocks of size at least two:
the three pair-partitions and the single block.
-/
def setPartitionsNoSingletonsOfFour : Fin 4 → List (List Nat) :=
  ![
    [[1, 2], [3, 4]],
    [[1, 3], [2, 4]],
    [[1, 4], [2, 3]],
    [[1, 2, 3, 4]]
  ]

/-- Number of perfect matchings on `2k` labelled atoms. -/
def perfectMatchingCount (k : Nat) : Nat :=
  (2 * k).factorial / (2 ^ k * k.factorial)

/-- Perfect matching values for `k = 1, 2, 3, 4`. -/
def perfectMatchingCountsOneToFour : Fin 4 → Nat :=
  ![1, 3, 15, 105]

theorem perfectMatchingCounts_verified_1_to_4 :
    ∀ k : Fin 4, perfectMatchingCount (k.val + 1) = perfectMatchingCountsOneToFour k :=
  by native_decide

theorem perfectMatching_two_atoms :
    (2 : Nat).factorial / (2 * 1) = 1 := by native_decide

theorem perfectMatching_four_atoms :
    (4 : Nat).factorial / (4 * 2) = 3 := by native_decide

theorem perfectMatching_six_atoms :
    (6 : Nat).factorial / (8 * 6) = 15 := by native_decide

theorem perfectMatching_eight_atoms :
    (8 : Nat).factorial / (16 * 24) = 105 := by native_decide

/-- Involutions: labelled partitions into one-cycles and two-cycles. -/
def involutionCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionCount (n + 1) + (n + 1) * involutionCount n

/-- Exact involution numbers `I(0), ..., I(10)`. -/
def involutionNumbersExact : Fin 11 → Nat :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496]

theorem involutionNumbersExact_correct :
    ∀ n : Fin 11, involutionCount n.val = involutionNumbersExact n := by native_decide

def involutionNumbersZeroToEight : Fin 9 → Nat :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764]

theorem involutionNumbers_verified_0_to_8 :
    ∀ n : Fin 9, involutionCount n.val = involutionNumbersZeroToEight n := by native_decide

end SaddlePointCoefficients
