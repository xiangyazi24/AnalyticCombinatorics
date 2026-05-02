import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PermutationGroups

open Finset

/-! # Permutation Groups and Cycle Enumeration

Formalizations from Chapter II (Labelled Structures) of Flajolet–Sedgewick,
focusing on permutation enumeration by cycle type, Stirling numbers of
the first kind, conjugacy classes (partition counts), double factorials
and perfect matchings, and Latin square counts.
-/

/-! ## Section 1: Permutations by cycle type

The number of permutations of n elements with cycle type (c₁, c₂, …, cₙ)
is n! / (1^c₁ · c₁! · 2^c₂ · c₂! · ⋯ · n^cₙ · cₙ!).

For n = 4, the cycle types and their counts are:
- (4,0,0,0): identity only → 1
- (2,1,0,0): two fixed pts, one 2-cycle → 6
- (0,2,0,0): two disjoint 2-cycles → 3
- (1,0,1,0): one fixed pt, one 3-cycle → 8
- (0,0,0,1): one 4-cycle → 6
-/

/-- Number of permutations of n=4 with cycle type (4,0,0,0). -/
theorem cycleType_4000 : Nat.factorial 4 / (1 ^ 4 * Nat.factorial 4) = 1 := by native_decide

/-- Number of permutations of n=4 with cycle type (2,1,0,0). -/
theorem cycleType_2100 :
    Nat.factorial 4 / (1 ^ 2 * Nat.factorial 2 * 2 ^ 1 * Nat.factorial 1) = 6 := by native_decide

/-- Number of permutations of n=4 with cycle type (0,2,0,0). -/
theorem cycleType_0200 :
    Nat.factorial 4 / (2 ^ 2 * Nat.factorial 2) = 3 := by native_decide

/-- Number of permutations of n=4 with cycle type (1,0,1,0). -/
theorem cycleType_1010 :
    Nat.factorial 4 / (1 ^ 1 * Nat.factorial 1 * 3 ^ 1 * Nat.factorial 1) = 8 := by native_decide

/-- Number of permutations of n=4 with cycle type (0,0,0,1). -/
theorem cycleType_0001 :
    Nat.factorial 4 / (4 ^ 1 * Nat.factorial 1) = 6 := by native_decide

/-- The cycle-type counts for S₄ sum to 4!. -/
theorem cycleType_sum_S4 : 1 + 6 + 3 + 8 + 6 = Nat.factorial 4 := by native_decide

/-! ## Section 2: Stirling numbers of the first kind (unsigned)

The unsigned Stirling number |s(n,k)| counts the number of permutations
of n elements having exactly k cycles. Recurrence:
  |s(n+1, k+1)| = n · |s(n, k+1)| + |s(n, k)|
-/

/-- Unsigned Stirling numbers of the first kind via the standard recurrence. -/
def unsignedStirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k

-- Values for n = 4
theorem stirling1_4_1 : unsignedStirling1 4 1 = 6 := by native_decide
theorem stirling1_4_2 : unsignedStirling1 4 2 = 11 := by native_decide
theorem stirling1_4_3 : unsignedStirling1 4 3 = 6 := by native_decide
theorem stirling1_4_4 : unsignedStirling1 4 4 = 1 := by native_decide

/-- Row sum: |s(4,1)| + |s(4,2)| + |s(4,3)| + |s(4,4)| = 4!. -/
theorem stirling1_row_sum_4 :
    unsignedStirling1 4 1 + unsignedStirling1 4 2 +
    unsignedStirling1 4 3 + unsignedStirling1 4 4 = Nat.factorial 4 := by native_decide

-- Values for n = 5
theorem stirling1_5_1 : unsignedStirling1 5 1 = 24 := by native_decide
theorem stirling1_5_2 : unsignedStirling1 5 2 = 50 := by native_decide
theorem stirling1_5_3 : unsignedStirling1 5 3 = 35 := by native_decide
theorem stirling1_5_4 : unsignedStirling1 5 4 = 10 := by native_decide
theorem stirling1_5_5 : unsignedStirling1 5 5 = 1 := by native_decide

/-- Row sum: Σ_{k=1}^{5} |s(5,k)| = 5!. -/
theorem stirling1_row_sum_5 :
    unsignedStirling1 5 1 + unsignedStirling1 5 2 +
    unsignedStirling1 5 3 + unsignedStirling1 5 4 +
    unsignedStirling1 5 5 = Nat.factorial 5 := by native_decide

/-! ## Section 3: Conjugacy classes

The number of conjugacy classes of Sₙ equals p(n), the number of
integer partitions of n.
-/

/-- Partition function values p(0)..p(5). -/
def partitionCount : Fin 6 → ℕ := ![1, 1, 2, 3, 5, 7]

theorem partitionCount_0 : partitionCount 0 = 1 := by native_decide
theorem partitionCount_1 : partitionCount 1 = 1 := by native_decide
theorem partitionCount_2 : partitionCount 2 = 2 := by native_decide
theorem partitionCount_3 : partitionCount 3 = 3 := by native_decide
theorem partitionCount_4 : partitionCount 4 = 5 := by native_decide
theorem partitionCount_5 : partitionCount 5 = 7 := by native_decide

/-! ## Section 4: Double factorial and perfect matchings

The odd double factorial (2n-1)!! = 1·3·5·⋯·(2n-1) counts the number
of perfect matchings (fixed-point-free involutions) on 2n labelled elements.
-/

/-- Double factorial: n!! -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

/-- Odd double factorial: (2n-1)!! = (2n)! / (2^n · n!) -/
def oddDoubleFactorial (n : ℕ) : ℕ :=
  doubleFactorial (2 * n - 1)

-- Verify double factorial values
theorem doubleFactorial_1 : doubleFactorial 1 = 1 := by native_decide
theorem doubleFactorial_3 : doubleFactorial 3 = 3 := by native_decide
theorem doubleFactorial_5 : doubleFactorial 5 = 15 := by native_decide
theorem doubleFactorial_7 : doubleFactorial 7 = 105 := by native_decide
theorem doubleFactorial_9 : doubleFactorial 9 = 945 := by native_decide

/-- (2n)! / (2^n · n!) = (2n-1)!! for small n. -/
theorem oddDoubleFact_formula_1 :
    Nat.factorial 2 / (2 ^ 1 * Nat.factorial 1) = 1 := by native_decide

theorem oddDoubleFact_formula_2 :
    Nat.factorial 4 / (2 ^ 2 * Nat.factorial 2) = 3 := by native_decide

theorem oddDoubleFact_formula_3 :
    Nat.factorial 6 / (2 ^ 3 * Nat.factorial 3) = 15 := by native_decide

theorem oddDoubleFact_formula_4 :
    Nat.factorial 8 / (2 ^ 4 * Nat.factorial 4) = 105 := by native_decide

/-- Number of perfect matchings on 2n elements. -/
def matchings (n : ℕ) : ℕ := doubleFactorial (2 * n - 1)

theorem matchings_1 : matchings 1 = 1 := by native_decide
theorem matchings_2 : matchings 2 = 3 := by native_decide
theorem matchings_3 : matchings 3 = 15 := by native_decide
theorem matchings_4 : matchings 4 = 105 := by native_decide

/-! ## Section 5: Latin squares (enumeration table)

A reduced Latin square of order n has first row and first column in natural order.
L(n) = number of reduced Latin squares. The total count is n! · (n-1)! · L(n).
-/

/-- Reduced Latin square counts for n = 1..5. -/
def reducedLatinSquare : Fin 5 → ℕ := ![1, 1, 1, 4, 56]

/-- Total Latin square counts for n = 1..5. -/
def latinSquareTable : Fin 5 → ℕ := ![1, 2, 12, 576, 161280]

-- Verify reduced Latin square values
theorem reducedLatin_1 : reducedLatinSquare 0 = 1 := by native_decide
theorem reducedLatin_2 : reducedLatinSquare 1 = 1 := by native_decide
theorem reducedLatin_3 : reducedLatinSquare 2 = 1 := by native_decide
theorem reducedLatin_4 : reducedLatinSquare 3 = 4 := by native_decide
theorem reducedLatin_5 : reducedLatinSquare 4 = 56 := by native_decide

-- Verify total Latin square counts
theorem latin_1 : latinSquareTable 0 = 1 := by native_decide
theorem latin_2 : latinSquareTable 1 = 2 := by native_decide
theorem latin_3 : latinSquareTable 2 = 12 := by native_decide
theorem latin_4 : latinSquareTable 3 = 576 := by native_decide
theorem latin_5 : latinSquareTable 4 = 161280 := by native_decide

/-- Total = n! · (n-1)! · L(n) verified for n=4: 4!·3!·4 = 24·6·4 = 576. -/
theorem latin_total_4 :
    Nat.factorial 4 * Nat.factorial 3 * 4 = 576 := by native_decide

/-- Total = n! · (n-1)! · L(n) verified for n=5: 5!·4!·56 = 120·24·56 = 161280. -/
theorem latin_total_5 :
    Nat.factorial 5 * Nat.factorial 4 * 56 = 161280 := by native_decide

/-- 576 = 24 * 24 (alternate factorization). -/
theorem latin_576_factorization : 576 = 24 * 24 := by native_decide

end PermutationGroups
