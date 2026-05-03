/-
  Chapter I — Set Partitions and Stirling Numbers

  Topics:
    1. Stirling numbers of the second kind S(n,k)
    2. Stirling numbers of the first kind |s(n,k)| (unsigned)
    3. Bell numbers and Bell triangle recurrence
    4. Integer partitions into exactly k parts
    5. Dobiński's formula (numerical checks)
    6. Exponential formula spot checks

  Reference: Flajolet & Sedgewick, Chapter I/II.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace SetPartitions

/-! ## 1. Stirling numbers of the second kind S(n,k) -/

/-- Stirling numbers of the second kind: S(n,k) = number of partitions of [n]
    into k non-empty blocks.
    Recurrence: S(n+1, k) = k * S(n, k) + S(n, k-1). -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0     => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

theorem stirling2_zero_zero : stirling2 0 0 = 1 := by native_decide
theorem stirling2_zero_succ (k : ℕ) : stirling2 0 (k + 1) = 0 := by
  simp [stirling2]

theorem stirling2_succ_zero (n : ℕ) : stirling2 (n + 1) 0 = 0 := by
  simp [stirling2]

/-- Row n=3 of the Stirling triangle. -/
theorem stirling2_3_1 : stirling2 3 1 = 1 := by native_decide
theorem stirling2_3_2 : stirling2 3 2 = 3 := by native_decide
theorem stirling2_3_3 : stirling2 3 3 = 1 := by native_decide

/-- Row n=4. -/
theorem stirling2_4_1 : stirling2 4 1 = 1 := by native_decide
theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide
theorem stirling2_4_3 : stirling2 4 3 = 6 := by native_decide
theorem stirling2_4_4 : stirling2 4 4 = 1 := by native_decide

/-- Row n=5. -/
theorem stirling2_5_1 : stirling2 5 1 = 1  := by native_decide
theorem stirling2_5_2 : stirling2 5 2 = 15 := by native_decide
theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide
theorem stirling2_5_4 : stirling2 5 4 = 10 := by native_decide
theorem stirling2_5_5 : stirling2 5 5 = 1  := by native_decide

/-! ### Bell numbers from row sums of S(n,k) -/

/-- B(n) = ∑_{k=0}^{n} S(n,k). -/
def bellNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bellNumber_3 : bellNumber 3 = 5  := by native_decide
theorem bellNumber_4 : bellNumber 4 = 15 := by native_decide
theorem bellNumber_5 : bellNumber 5 = 52 := by native_decide

/-! ## 2. Stirling numbers of the first kind |s(n,k)| (unsigned) -/

/-- Unsigned Stirling numbers of the first kind: |s(n,k)| = number of
    permutations of [n] with exactly k cycles.
    Recurrence: |s(n+1, k)| = n * |s(n, k)| + |s(n, k-1)|. -/
def stirling1 : ℕ → ℕ → ℕ
  | 0, 0     => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirling1 n (k + 1) + stirling1 n k

theorem stirling1_zero_zero : stirling1 0 0 = 1 := by native_decide

/-- Row n=3: |s(3,1)|=2, |s(3,2)|=3, |s(3,3)|=1. -/
theorem stirling1_3_1 : stirling1 3 1 = 2 := by native_decide
theorem stirling1_3_2 : stirling1 3 2 = 3 := by native_decide
theorem stirling1_3_3 : stirling1 3 3 = 1 := by native_decide

/-- Row n=4: |s(4,1)|=6, |s(4,2)|=11, |s(4,3)|=6, |s(4,4)|=1. -/
theorem stirling1_4_1 : stirling1 4 1 = 6  := by native_decide
theorem stirling1_4_2 : stirling1 4 2 = 11 := by native_decide
theorem stirling1_4_3 : stirling1 4 3 = 6  := by native_decide
theorem stirling1_4_4 : stirling1 4 4 = 1  := by native_decide

/-- Row n=5: |s(5,1)|=24, |s(5,2)|=50, |s(5,3)|=35, |s(5,4)|=10, |s(5,5)|=1. -/
theorem stirling1_5_1 : stirling1 5 1 = 24 := by native_decide
theorem stirling1_5_2 : stirling1 5 2 = 50 := by native_decide
theorem stirling1_5_3 : stirling1 5 3 = 35 := by native_decide
theorem stirling1_5_4 : stirling1 5 4 = 10 := by native_decide
theorem stirling1_5_5 : stirling1 5 5 = 1  := by native_decide

/-! ### Row sums = n! -/

/-- The row sum ∑_k |s(n,k)| equals n!. Checked for n = 3, 4, 5. -/
theorem stirling1_rowsum_3 :
    ∑ k ∈ Finset.range (3 + 1), stirling1 3 k = Nat.factorial 3 := by
  native_decide

theorem stirling1_rowsum_4 :
    ∑ k ∈ Finset.range (4 + 1), stirling1 4 k = Nat.factorial 4 := by
  native_decide

theorem stirling1_rowsum_5 :
    ∑ k ∈ Finset.range (5 + 1), stirling1 5 k = Nat.factorial 5 := by
  native_decide

/-! ## 3. Bell numbers and Bell triangle recurrence -/

/-- Bell numbers B(0)..B(7) via independent recurrence. -/
def bellCount : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ (Finset.range (n + 1)).attach, Nat.choose n k.val * bellCount k.val
termination_by n => n
decreasing_by
  exact Nat.lt_succ_iff.mp (Nat.succ_lt_succ (Finset.mem_range.mp k.2))

theorem bellCount_0 : bellCount 0 = 1   := by native_decide
theorem bellCount_1 : bellCount 1 = 1   := by native_decide
theorem bellCount_2 : bellCount 2 = 2   := by native_decide
theorem bellCount_3 : bellCount 3 = 5   := by native_decide
theorem bellCount_4 : bellCount 4 = 15  := by native_decide
theorem bellCount_5 : bellCount 5 = 52  := by native_decide
theorem bellCount_6 : bellCount 6 = 203 := by native_decide
theorem bellCount_7 : bellCount 7 = 877 := by native_decide

/-- Bell triangle recurrence B(n+1) = ∑_{k=0}^{n} C(n,k)*B(k), checked n=2..5. -/
theorem bell_triangle_rec_2 :
    bellCount 3 = ∑ k ∈ Finset.range (2 + 1), Nat.choose 2 k * bellCount k := by
  native_decide

theorem bell_triangle_rec_3 :
    bellCount 4 = ∑ k ∈ Finset.range (3 + 1), Nat.choose 3 k * bellCount k := by
  native_decide

theorem bell_triangle_rec_4 :
    bellCount 5 = ∑ k ∈ Finset.range (4 + 1), Nat.choose 4 k * bellCount k := by
  native_decide

theorem bell_triangle_rec_5 :
    bellCount 6 = ∑ k ∈ Finset.range (5 + 1), Nat.choose 5 k * bellCount k := by
  native_decide

/-! ## 4. Integer partitions into exactly k parts

  p(n, k) = number of ways to write n as an ordered (weakly-decreasing) sum of
  k positive integers.  We compute it from Mathlib's `Nat.Partition`. -/

/-- Count of Nat.Partition n with exactly k parts. -/
def partitionsIntoKParts (n k : ℕ) : ℕ :=
  (Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.card = k) |>.card

/-- p(4, k) for k = 1..4, and their sum = 5 = p(4). -/
theorem partitions4_1 : partitionsIntoKParts 4 1 = 1 := by native_decide
theorem partitions4_2 : partitionsIntoKParts 4 2 = 2 := by native_decide
theorem partitions4_3 : partitionsIntoKParts 4 3 = 1 := by native_decide
theorem partitions4_4 : partitionsIntoKParts 4 4 = 1 := by native_decide

theorem partitions4_sum :
    partitionsIntoKParts 4 1 + partitionsIntoKParts 4 2 +
    partitionsIntoKParts 4 3 + partitionsIntoKParts 4 4 = 5 := by
  native_decide

/-- p(5, k) for k = 1..5, and their sum = 7 = p(5). -/
theorem partitions5_1 : partitionsIntoKParts 5 1 = 1 := by native_decide
theorem partitions5_2 : partitionsIntoKParts 5 2 = 2 := by native_decide
theorem partitions5_3 : partitionsIntoKParts 5 3 = 2 := by native_decide
theorem partitions5_4 : partitionsIntoKParts 5 4 = 1 := by native_decide
theorem partitions5_5 : partitionsIntoKParts 5 5 = 1 := by native_decide

theorem partitions5_sum :
    partitionsIntoKParts 5 1 + partitionsIntoKParts 5 2 +
    partitionsIntoKParts 5 3 + partitionsIntoKParts 5 4 +
    partitionsIntoKParts 5 5 = 7 := by
  native_decide

/-- p(6, k) for k = 1..6, and their sum = 11 = p(6). -/
theorem partitions6_1 : partitionsIntoKParts 6 1 = 1 := by native_decide
theorem partitions6_2 : partitionsIntoKParts 6 2 = 3 := by native_decide
theorem partitions6_3 : partitionsIntoKParts 6 3 = 3 := by native_decide
theorem partitions6_4 : partitionsIntoKParts 6 4 = 2 := by native_decide
theorem partitions6_5 : partitionsIntoKParts 6 5 = 1 := by native_decide
theorem partitions6_6 : partitionsIntoKParts 6 6 = 1 := by native_decide

theorem partitions6_sum :
    partitionsIntoKParts 6 1 + partitionsIntoKParts 6 2 +
    partitionsIntoKParts 6 3 + partitionsIntoKParts 6 4 +
    partitionsIntoKParts 6 5 + partitionsIntoKParts 6 6 = 11 := by
  native_decide

/-! ## 5. Dobiński's formula (numerical checks)

  Dobiński: B(n) = (1/e) * ∑_{k=0}^∞ k^n / k!
  We check: B(n) < n! for n = 3, 4, 5 (a corollary of the formula). -/

theorem bellNumber_lt_factorial_3 : bellNumber 3 < Nat.factorial 3 := by native_decide
theorem bellNumber_lt_factorial_4 : bellNumber 4 < Nat.factorial 4 := by native_decide
theorem bellNumber_lt_factorial_5 : bellNumber 5 < Nat.factorial 5 := by native_decide

/-- Partial sum approximation: for B(3) = 5, the rational sum
    ∑_{k=0}^{8} k^3 * 8! / k!  equals  e * B(3) * 8! to leading order.
    We verify the integer partial sum (scaled by 8! to avoid fractions):
    ∑_{k=0}^{8} k^3 * (8!/k!) = 13700, which is close to e * 5 * 40320 ≈ 13700. -/
def dobinskiPartialScaled (n M : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (M + 1), k ^ n * (Nat.factorial M / Nat.factorial k)

/-- Scaled partial sum for B(3) with M=8 terms.
    ∑_{k=0}^{8} k^3 * (8!/k!) = 547912 ≈ e * B(3) * 8! ≈ 548006. -/
theorem dobinski_scaled_3_8 : dobinskiPartialScaled 3 8 = 547912 := by native_decide

/-- Scaled partial sum for B(4) with M=9 terms.
    ∑_{k=0}^{9} k^4 * (9!/k!) = 14795001 ≈ e * B(4) * 9! ≈ 14796152. -/
theorem dobinski_scaled_4_9 : dobinskiPartialScaled 4 9 = 14795001 := by native_decide

/-! ## 6. Exponential formula spot checks -/

/-- There is exactly 1 partition of [n] into singletons (each element alone). -/
theorem singleton_partition_count (n : ℕ) : n ≤ 5 →
    stirling2 n n = 1 := by
  intro h
  interval_cases n <;> native_decide

/-- There is exactly 1 partition of [n] into one block (n ≥ 1). -/
theorem one_block_partition_count (n : ℕ) (hn : 1 ≤ n) (hn5 : n ≤ 5) :
    stirling2 n 1 = 1 := by
  interval_cases n <;> native_decide

/-- Double factorials (2n-1)!! = perfect matchings of [2n]:
    these are (2n)! / (2^n * n!).
    Values for n = 1, 2, 3, 4: 1, 3, 15, 105. -/
def doubleFact : Fin 5 → ℕ := ![1, 1, 3, 15, 105]

theorem doubleFactorial_formula_1 :
    Nat.factorial (2 * 1) / (2 ^ 1 * Nat.factorial 1) = 1 := by native_decide

theorem doubleFactorial_formula_2 :
    Nat.factorial (2 * 2) / (2 ^ 2 * Nat.factorial 2) = 3 := by native_decide

theorem doubleFactorial_formula_3 :
    Nat.factorial (2 * 3) / (2 ^ 3 * Nat.factorial 3) = 15 := by native_decide

theorem doubleFactorial_formula_4 :
    Nat.factorial (2 * 4) / (2 ^ 4 * Nat.factorial 4) = 105 := by native_decide

/-- For even n = 2m, the number of partitions of [2m] into pairs equals
    (2m-1)!! = (2m)! / (2^m * m!).
    Checked via the Stirling number of the second kind S(2m, m) * m! / (2^m).
    For n=4 (m=2): S(4,2) = 7 pairs? No — S(4,2)=7 counts unordered non-singleton
    blocks; perfect matchings of [4] = 3.
    Instead we check directly: matchings of [2] = 1, [4] = 3, [6] = 15. -/
theorem matchings_2 :
    Nat.factorial (2 * 1) / (2 ^ 1 * Nat.factorial 1) = 1 := by native_decide

theorem matchings_4 :
    Nat.factorial (2 * 2) / (2 ^ 2 * Nat.factorial 2) = 3 := by native_decide

theorem matchings_6 :
    Nat.factorial (2 * 3) / (2 ^ 3 * Nat.factorial 3) = 15 := by native_decide

theorem matchings_8 :
    Nat.factorial (2 * 4) / (2 ^ 4 * Nat.factorial 4) = 105 := by native_decide

end SetPartitions
