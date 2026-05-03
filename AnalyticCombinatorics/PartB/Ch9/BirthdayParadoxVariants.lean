import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace BirthdayParadoxVariants

/-!
# Birthday paradox variants and occupancy tables

Finite, exact checks for small birthday-paradox and occupancy identities from
Flajolet--Sedgewick, Chapter IX.  All computations are bounded and discharged
by `native_decide`.
-/

open Finset

/-! ## Birthday collision counts -/

/-- Falling factorial `m * (m - 1) * ... * (m - n + 1)`. -/
def fallingFactorial (m n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (m - i)

/-- Total number of labelled birthday assignments for `n` people and `m` days. -/
def birthdayAssignmentCount (m n : ℕ) : ℕ :=
  m ^ n

/-- Number of birthday assignments with no collision. -/
def birthdayNoCollisionCount (m n : ℕ) : ℕ :=
  fallingFactorial m n

/-- Number of birthday assignments with at least one collision. -/
def birthdayCollisionCount (m n : ℕ) : ℕ :=
  birthdayAssignmentCount m n - birthdayNoCollisionCount m n

/-- Exact collision probability for `n` people and `m` possible birthdays. -/
def birthdayCollisionProbability (m n : ℕ) : ℚ :=
  (birthdayCollisionCount m n : ℚ) / (birthdayAssignmentCount m n : ℚ)

/-- Collision counts for `m = 8` days and `n = 0..7` people. -/
def collisionCountEightDayTable : Fin 8 → ℕ :=
  ![0, 0, 8, 176, 2416, 26048, 241984, 2056832]

theorem collision_counts_for_eight_days :
    collisionCountEightDayTable =
      ![birthdayCollisionCount 8 0,
        birthdayCollisionCount 8 1,
        birthdayCollisionCount 8 2,
        birthdayCollisionCount 8 3,
        birthdayCollisionCount 8 4,
        birthdayCollisionCount 8 5,
        birthdayCollisionCount 8 6,
        birthdayCollisionCount 8 7] := by
  native_decide

theorem collision_probabilities_for_eight_days :
    birthdayCollisionProbability 8 0 = 0 ∧
    birthdayCollisionProbability 8 1 = 0 ∧
    birthdayCollisionProbability 8 2 = 1 / 8 ∧
    birthdayCollisionProbability 8 3 = 11 / 32 ∧
    birthdayCollisionProbability 8 4 = 151 / 256 ∧
    birthdayCollisionProbability 8 5 = 407 / 512 := by
  native_decide

/-! ## First collision waiting time -/

/--
Expected number of draws up to and including the first repeated birthday:
`E[T] = sum_{k=0}^m (m)_k / m^k`.
-/
def expectedTrialsToFirstCollision (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1),
    (birthdayNoCollisionCount m k : ℚ) / (birthdayAssignmentCount m k : ℚ)

/-- Expected first-collision waiting times for `m = 1..6`. -/
def firstCollisionExpectationTable : Fin 6 → ℚ :=
  ![2, 5 / 2, 26 / 9, 103 / 32, 2194 / 625, 1223 / 324]

theorem first_collision_expectation_values :
    firstCollisionExpectationTable =
      ![expectedTrialsToFirstCollision 1,
        expectedTrialsToFirstCollision 2,
        expectedTrialsToFirstCollision 3,
        expectedTrialsToFirstCollision 4,
        expectedTrialsToFirstCollision 5,
        expectedTrialsToFirstCollision 6] := by
  native_decide

/-! ## Coupon collector partial completion -/

/-- Expected time to collect `r` distinct coupons from `m` equally likely types. -/
def partialCouponCollectorExpectedTime (m r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, (m : ℚ) / ((m - i : ℕ) : ℚ)

/-- Values of `10 * E[T_{6,r}]` for `r = 0..6`. -/
def partialCouponCollectorSixScaledTable : Fin 7 → ℕ :=
  ![0, 10, 22, 37, 57, 87, 147]

theorem partial_coupon_collector_six_values :
    partialCouponCollectorSixScaledTable =
      ![(10 * partialCouponCollectorExpectedTime 6 0 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 1 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 2 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 3 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 4 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 5 : ℚ).num.natAbs,
        (10 * partialCouponCollectorExpectedTime 6 6 : ℚ).num.natAbs] := by
  native_decide

theorem partial_coupon_collector_six_exact :
    partialCouponCollectorExpectedTime 6 0 = 0 ∧
    partialCouponCollectorExpectedTime 6 1 = 1 ∧
    partialCouponCollectorExpectedTime 6 2 = 11 / 5 ∧
    partialCouponCollectorExpectedTime 6 3 = 37 / 10 ∧
    partialCouponCollectorExpectedTime 6 4 = 57 / 10 ∧
    partialCouponCollectorExpectedTime 6 5 = 87 / 10 ∧
    partialCouponCollectorExpectedTime 6 6 = 147 / 10 := by
  native_decide

/-! ## Matching birthday pair counts -/

/-- Number of unordered pairs among `n` people. -/
def matchingBirthdayPairCount (n : ℕ) : ℕ :=
  Nat.choose n 2

/-- Expected number of matching birthday pairs among `n` people and `m` days. -/
def expectedMatchingBirthdayPairs (m n : ℕ) : ℚ :=
  (matchingBirthdayPairCount n : ℚ) / (m : ℚ)

/-- Pair counts for `n = 1..10`. -/
def matchingBirthdayPairTable : Fin 10 → ℕ :=
  ![0, 1, 3, 6, 10, 15, 21, 28, 36, 45]

theorem matching_birthday_pair_table_values :
    matchingBirthdayPairTable =
      ![matchingBirthdayPairCount 1,
        matchingBirthdayPairCount 2,
        matchingBirthdayPairCount 3,
        matchingBirthdayPairCount 4,
        matchingBirthdayPairCount 5,
        matchingBirthdayPairCount 6,
        matchingBirthdayPairCount 7,
        matchingBirthdayPairCount 8,
        matchingBirthdayPairCount 9,
        matchingBirthdayPairCount 10] := by
  native_decide

theorem expected_matching_pair_values :
    expectedMatchingBirthdayPairs 8 4 = 3 / 4 ∧
    expectedMatchingBirthdayPairs 8 5 = 5 / 4 ∧
    expectedMatchingBirthdayPairs 12 6 = 5 / 4 ∧
    expectedMatchingBirthdayPairs 365 10 = 9 / 73 := by
  native_decide

/-! ## Stirling subset sums for occupancy -/

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of surjections from an `n`-set onto a `k`-set. -/
def surjectionCount (n k : ℕ) : ℕ :=
  stirling2 n k * Nat.factorial k

/-- Assignments of `n` balls into `m` bins with exactly `k` occupied bins. -/
def exactOccupiedBinCount (n m k : ℕ) : ℕ :=
  Nat.choose m k * surjectionCount n k

/-- Exact-occupancy counts for `n = 5` balls into `m = 4` bins and `k = 0..4`. -/
def occupancyFiveIntoFourTable : Fin 5 → ℕ :=
  ![0, 4, 180, 600, 240]

theorem occupancy_five_into_four_table_values :
    occupancyFiveIntoFourTable =
      ![exactOccupiedBinCount 5 4 0,
        exactOccupiedBinCount 5 4 1,
        exactOccupiedBinCount 5 4 2,
        exactOccupiedBinCount 5 4 3,
        exactOccupiedBinCount 5 4 4] := by
  native_decide

theorem stirling_subset_sum_occupancy_values :
    (∑ k ∈ Finset.range 5, exactOccupiedBinCount 5 4 k) = 4 ^ 5 ∧
    (∑ k ∈ Finset.range 4, exactOccupiedBinCount 4 3 k) = 3 ^ 4 ∧
    (∑ k ∈ Finset.range 7, exactOccupiedBinCount 6 6 k) = 6 ^ 6 := by
  native_decide

end BirthdayParadoxVariants
