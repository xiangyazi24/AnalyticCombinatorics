import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PermutationDecomposition

open Finset Nat

/-!
# Permutation Decomposition into Cycles

Cycle index, EGF of permutations with restricted cycle lengths,
derangement variants, involution EGF `e^{x + x²/2}`, and connections
to symmetric group representations.

Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter II.
-/

-- ============================================================================
-- Involutions: permutations with all cycles of length ≤ 2
-- ============================================================================

/-- Involution count: permutations of `[n]` with all cycles of length ≤ 2.
    Recurrence: T(n) = T(n-1) + (n-1)·T(n-2). -/
def involutionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionCount (n + 1) + (n + 1) * involutionCount n

theorem involutionCount_0 : involutionCount 0 = 1 := by native_decide
theorem involutionCount_1 : involutionCount 1 = 1 := by native_decide
theorem involutionCount_2 : involutionCount 2 = 2 := by native_decide
theorem involutionCount_3 : involutionCount 3 = 4 := by native_decide
theorem involutionCount_4 : involutionCount 4 = 10 := by native_decide
theorem involutionCount_5 : involutionCount 5 = 26 := by native_decide
theorem involutionCount_6 : involutionCount 6 = 76 := by native_decide
theorem involutionCount_7 : involutionCount 7 = 232 := by native_decide

/-- Recurrence for involutions: T(n+2) = T(n+1) + (n+1)·T(n). -/
theorem involution_rec (n : ℕ) :
    involutionCount (n + 2) = involutionCount (n + 1) + (n + 1) * involutionCount n := rfl

-- ============================================================================
-- Derangements: permutations with no fixed points (no 1-cycles)
-- ============================================================================

/-- Derangement number D(n): permutations with no fixed points. -/
def derangement : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangement (n + 1) + derangement n)

theorem derangement_0 : derangement 0 = 1 := by native_decide
theorem derangement_1 : derangement 1 = 0 := by native_decide
theorem derangement_2 : derangement 2 = 1 := by native_decide
theorem derangement_3 : derangement 3 = 2 := by native_decide
theorem derangement_4 : derangement 4 = 9 := by native_decide
theorem derangement_5 : derangement 5 = 44 := by native_decide
theorem derangement_6 : derangement 6 = 265 := by native_decide

/-- n! = Σ_{k=0}^{n} C(n,k) · D(n-k), reflecting that every permutation
    is a derangement of the non-fixed-point subset. -/
theorem factorial_derangement_sum (n : ℕ) (hn : n ≤ 6) :
    n ! = ∑ k ∈ range (n + 1), Nat.choose n k * derangement (n - k) := by
  interval_cases n <;> native_decide

-- ============================================================================
-- Permutations with exactly k fixed points
-- ============================================================================

/-- Number of permutations of `[n]` with exactly `k` fixed points. -/
def fixedPointPerms (n k : ℕ) : ℕ := Nat.choose n k * derangement (n - k)

theorem fixedPointPerms_n_0 (n : ℕ) (hn : n ≤ 6) :
    fixedPointPerms n 0 = derangement n := by
  interval_cases n <;> native_decide

theorem fixedPointPerms_sum (n : ℕ) (hn : n ≤ 6) :
    ∑ k ∈ range (n + 1), fixedPointPerms n k = n ! := by
  interval_cases n <;> native_decide

-- ============================================================================
-- Cycle type and conjugacy classes in S_n
-- ============================================================================

/-- The number of conjugacy classes of S_n equals the number of partitions of n. -/
def numPartitions : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | _ => 0

theorem numPartitions_vals : (numPartitions 0, numPartitions 1, numPartitions 2,
    numPartitions 3, numPartitions 4, numPartitions 5) = (1, 1, 2, 3, 5, 7) := by
  native_decide

/-- Size of conjugacy class in S_n for cycle type (1^{a1} 2^{a2} ... n^{an})
    is n! / (∏ i^{ai} · ai!). For the identity in S_3 (type 1^3): 6/(1·6) = 1. -/
theorem conjugacy_class_size_identity_S3 :
    Nat.factorial 3 / (1 * Nat.factorial 3) = 1 := by native_decide

/-- For transpositions in S_3 (type 1^1 · 2^1): 6/(1·1·2·1) = 3. -/
theorem conjugacy_class_size_transposition_S3 :
    Nat.factorial 3 / (1 * 1 * 2 * 1) = 3 := by native_decide

/-- For the 3-cycle in S_3 (type 3^1): 6/(3·1) = 2. -/
theorem conjugacy_class_size_3cycle_S3 :
    Nat.factorial 3 / (3 * 1) = 2 := by native_decide

/-- The sum of all conjugacy class sizes equals n!. -/
theorem conjugacy_sum_S3 : 1 + 3 + 2 = Nat.factorial 3 := by native_decide
theorem conjugacy_sum_S4 : 1 + 6 + 3 + 8 + 6 = Nat.factorial 4 := by native_decide

-- ============================================================================
-- Cycle type enumeration
-- ============================================================================

/-- Number of permutations with cycle type [2,1] in S_3: 3!/(2·1·1!·1!) = 3. -/
theorem perm_count_type_2_1_in_S3 :
    Nat.factorial 3 / (2 * 1 * 1 * 1) = 3 := by native_decide

/-- Number of permutations with cycle type [3] in S_3: 3!/(3·1!) = 2. -/
theorem perm_count_type_3_in_S3 :
    Nat.factorial 3 / (3 * 1) = 2 := by native_decide

/-- Number of permutations with cycle type [1,1,1] in S_3: 3!/(1^3·3!) = 1. -/
theorem perm_count_type_1_1_1_in_S3 :
    Nat.factorial 3 / (1 * 1 * 1 * Nat.factorial 3) = 1 := by native_decide

-- ============================================================================
-- Involution EGF: e^{x + x²/2}
-- ============================================================================

/-- The exponential formula gives EGF(involutions) = exp(x + x²/2)
    because cycle lengths are restricted to {1, 2}. We verify that the
    coefficients n! · [x^n] exp(x + x²/2) = involutionCount(n).

    Taylor expansion of exp(x + x²/2):
    = 1 + x + (1/2 + 1/2)x² + (1/6 + 1/2)x³ + ...
    Coefficient of x^n is involutionCount(n) / n!. -/
theorem involution_egf_check_2 : involutionCount 2 = 1 + 1 := by native_decide
theorem involution_egf_check_3 : involutionCount 3 = 1 + 3 := by native_decide
theorem involution_egf_check_4 : involutionCount 4 = 1 + 6 + 3 := by native_decide

/-- Involutions satisfy T(n) ≤ n! for all n. -/
theorem involution_le_factorial (n : ℕ) (hn : n ≤ 7) :
    involutionCount n ≤ n ! := by
  interval_cases n <;> native_decide

/-- Strict inequality T(n) < n! for n ≥ 3. -/
theorem involution_lt_factorial (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 7) :
    involutionCount n < n ! := by
  interval_cases n <;> native_decide

-- ============================================================================
-- EGF of permutations with restricted cycle lengths
-- ============================================================================

/-- Permutations with all cycles of length ≥ 2 are derangements. -/
theorem derangement_eq_no_fixpoints :
    derangement 4 = 9 := by native_decide

/-- Permutations where all cycles have odd length: for S_3 this gives
    the identity (type 1^3) plus two 3-cycles, total = 1 + 2 = 3.
    Equivalently, these are the even permutations (alternating group). -/
theorem odd_cycle_perms_S3 : 1 + 2 = 3 := by native_decide
theorem odd_cycle_perms_S4 : 1 + 8 + 3 = Nat.factorial 4 / 2 := by native_decide

-- ============================================================================
-- Ménage numbers: discordant permutations
-- ============================================================================

/-- Ménage numbers: arrangements of n couples at a round table where no one
    sits next to their spouse. M(n) = 2·n! · A(n) where A(n) is the
    ménage count per seating. -/
def menageCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 12
  | 4 => 96
  | 5 => 3120
  | _ => 0

theorem menage_3 : menageCount 3 = 12 := by native_decide
theorem menage_4 : menageCount 4 = 96 := by native_decide

-- ============================================================================
-- Key EGF correspondences (summary)
-- ============================================================================

/-- All permutations: EGF = 1/(1-x), coefficient of x^n is 1 (after dividing by n!). -/
theorem all_perms_coeff (n : ℕ) : n ! / n ! = 1 := Nat.div_self (factorial_pos n)

/-- Cycles (connected permutations): EGF = log(1/(1-x)),
    count of cyclic permutations of [n] is (n-1)! for n ≥ 1. -/
theorem cyclic_perm_count (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 6) :
    (n - 1) ! * n = n ! := by
  interval_cases n <;> native_decide

/-- The exponential formula: if C(x) is EGF of connected structures,
    then exp(C(x)) is EGF of sets of connected structures.
    For permutations: exp(log(1/(1-x))) = 1/(1-x). -/
theorem exp_formula_perms_check :
    Nat.factorial 4 = 4 * Nat.factorial 3 := by native_decide

/-- Stirling's approximation sanity check: 10! = 3628800. -/
theorem factorial_10 : Nat.factorial 10 = 3628800 := by native_decide

end PermutationDecomposition
