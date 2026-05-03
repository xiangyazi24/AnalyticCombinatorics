import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace InvolutionStatistics

/-! Involution statistics: fixed-point and 2-cycle distributions for self-inverse
permutations. The involution count satisfies a(n) = a(n-1) + (n-1)*a(n-2) with
a(0) = a(1) = 1, and its EGF is exp(z + z²/2). Flajolet & Sedgewick, Chapter 2. -/

/-- Number of involutions (self-inverse permutations) on n elements. -/
def invCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => invCount (n + 1) + (n + 1) * invCount n

theorem invCount_rec (n : ℕ) :
    invCount (n + 2) = invCount (n + 1) + (n + 1) * invCount n := rfl

theorem invCount_zero : invCount 0 = 1 := by native_decide
theorem invCount_one : invCount 1 = 1 := by native_decide
theorem invCount_two : invCount 2 = 2 := by native_decide
theorem invCount_three : invCount 3 = 4 := by native_decide
theorem invCount_four : invCount 4 = 10 := by native_decide
theorem invCount_five : invCount 5 = 26 := by native_decide
theorem invCount_six : invCount 6 = 76 := by native_decide
theorem invCount_seven : invCount 7 = 232 := by native_decide
theorem invCount_eight : invCount 8 = 764 := by native_decide

/-- Double factorial: n!! = n·(n-2)·(n-4)·…·1 (odd) or ·2 (even), with 0!! = 1. -/
def doubleFact : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFact n

theorem doubleFact_zero : doubleFact 0 = 1 := by native_decide
theorem doubleFact_one : doubleFact 1 = 1 := by native_decide
theorem doubleFact_three : doubleFact 3 = 3 := by native_decide
theorem doubleFact_five : doubleFact 5 = 15 := by native_decide
theorem doubleFact_seven : doubleFact 7 = 105 := by native_decide

/-- Number of perfect matchings on 2m elements, equal to (2m-1)!!. -/
def perfectMatchings : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1) * perfectMatchings m

theorem perfectMatchings_zero : perfectMatchings 0 = 1 := by native_decide
theorem perfectMatchings_one : perfectMatchings 1 = 1 := by native_decide
theorem perfectMatchings_two : perfectMatchings 2 = 3 := by native_decide
theorem perfectMatchings_three : perfectMatchings 3 = 15 := by native_decide
theorem perfectMatchings_four : perfectMatchings 4 = 105 := by native_decide

theorem perfectMatchings_eq_doubleFact (m : ℕ) (hm : 1 ≤ m) :
    perfectMatchings m = doubleFact (2 * m - 1) := by
  sorry

/-- Number of involutions on [n] with exactly k fixed points.
    Equals C(n,k) · (n-k-1)!! when n ≡ k (mod 2) and k ≤ n, else 0. -/
def invWithFixedPts (n k : ℕ) : ℕ :=
  if k ≤ n ∧ (n - k) % 2 = 0 then
    n.choose k * perfectMatchings ((n - k) / 2)
  else 0

theorem invWithFixedPts_4_0 : invWithFixedPts 4 0 = 3 := by native_decide
theorem invWithFixedPts_4_1 : invWithFixedPts 4 1 = 0 := by native_decide
theorem invWithFixedPts_4_2 : invWithFixedPts 4 2 = 6 := by native_decide
theorem invWithFixedPts_4_3 : invWithFixedPts 4 3 = 0 := by native_decide
theorem invWithFixedPts_4_4 : invWithFixedPts 4 4 = 1 := by native_decide

theorem invWithFixedPts_5_1 : invWithFixedPts 5 1 = 15 := by native_decide
theorem invWithFixedPts_5_3 : invWithFixedPts 5 3 = 10 := by native_decide
theorem invWithFixedPts_5_5 : invWithFixedPts 5 5 = 1 := by native_decide

/-- Involutions with no fixed points on 2m elements are perfect matchings. -/
theorem invWithFixedPts_zero_eq (m : ℕ) :
    invWithFixedPts (2 * m) 0 = perfectMatchings m := by
  sorry

/-- Sum over all fixed-point counts recovers the total involution count. -/
def sumFixedPtCounts (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (invWithFixedPts n)

theorem sumFixedPtCounts_eq_0 : sumFixedPtCounts 0 = invCount 0 := by native_decide
theorem sumFixedPtCounts_eq_1 : sumFixedPtCounts 1 = invCount 1 := by native_decide
theorem sumFixedPtCounts_eq_2 : sumFixedPtCounts 2 = invCount 2 := by native_decide
theorem sumFixedPtCounts_eq_3 : sumFixedPtCounts 3 = invCount 3 := by native_decide
theorem sumFixedPtCounts_eq_4 : sumFixedPtCounts 4 = invCount 4 := by native_decide
theorem sumFixedPtCounts_eq_5 : sumFixedPtCounts 5 = invCount 5 := by native_decide

theorem sumFixedPtCounts_eq_invCount (n : ℕ) :
    sumFixedPtCounts n = invCount n := by
  sorry

/-- Total number of fixed points summed over all involutions of [n]. -/
def totalFixedPts (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => k * invWithFixedPts n k)

/-- Each element is a fixed point in exactly invCount(n-1) involutions,
    so the total fixed-point count is n · invCount(n-1). -/
theorem totalFixedPts_eq_1 : totalFixedPts 1 = 1 * invCount 0 := by native_decide
theorem totalFixedPts_eq_2 : totalFixedPts 2 = 2 * invCount 1 := by native_decide
theorem totalFixedPts_eq_3 : totalFixedPts 3 = 3 * invCount 2 := by native_decide
theorem totalFixedPts_eq_4 : totalFixedPts 4 = 4 * invCount 3 := by native_decide
theorem totalFixedPts_eq_5 : totalFixedPts 5 = 5 * invCount 4 := by native_decide

theorem totalFixedPts_identity (n : ℕ) (hn : 1 ≤ n) :
    totalFixedPts n = n * invCount (n - 1) := by
  sorry

/-- Total number of 2-cycles summed over all involutions of [n]. -/
def totalTwoCycles (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => ((n - k) / 2) * invWithFixedPts n k)

/-- Each pair {i,j} forms a 2-cycle in exactly invCount(n-2) involutions,
    so the total 2-cycle count is C(n,2) · invCount(n-2). -/
theorem totalTwoCycles_eq_2 : totalTwoCycles 2 = (2).choose 2 * invCount 0 := by native_decide
theorem totalTwoCycles_eq_3 : totalTwoCycles 3 = (3).choose 2 * invCount 1 := by native_decide
theorem totalTwoCycles_eq_4 : totalTwoCycles 4 = (4).choose 2 * invCount 2 := by native_decide
theorem totalTwoCycles_eq_5 : totalTwoCycles 5 = (5).choose 2 * invCount 3 := by native_decide

theorem totalTwoCycles_identity (n : ℕ) (hn : 2 ≤ n) :
    totalTwoCycles n = n.choose 2 * invCount (n - 2) := by
  sorry

/-- Fixed points plus twice the 2-cycles accounts for all n elements
    in each involution, so summing gives n · invCount(n). -/
theorem fixedPts_plus_twoCycles (n : ℕ) :
    totalFixedPts n + 2 * totalTwoCycles n = n * invCount n := by
  sorry

theorem fixedPts_plus_twoCycles_3 :
    totalFixedPts 3 + 2 * totalTwoCycles 3 = 3 * invCount 3 := by native_decide

theorem fixedPts_plus_twoCycles_4 :
    totalFixedPts 4 + 2 * totalTwoCycles 4 = 4 * invCount 4 := by native_decide

theorem fixedPts_plus_twoCycles_5 :
    totalFixedPts 5 + 2 * totalTwoCycles 5 = 5 * invCount 5 := by native_decide

/-- Involution count is strictly increasing for n ≥ 1. -/
theorem invCount_strictMono (n : ℕ) (hn : 1 ≤ n) :
    invCount n < invCount (n + 1) := by
  sorry

theorem invCount_strictMono_check_1 : invCount 1 < invCount 2 := by native_decide
theorem invCount_strictMono_check_4 : invCount 4 < invCount 5 := by native_decide

/-- Every set has at least one involution (the identity). -/
theorem one_le_invCount (n : ℕ) : 1 ≤ invCount n := by
  sorry

theorem one_le_invCount_check : ∀ k ∈ Finset.range 9, 1 ≤ invCount k := by native_decide

/-- The involution count exceeds the number of fixed-point-free involutions. -/
theorem invCount_ge_perfectMatchings (m : ℕ) :
    perfectMatchings m ≤ invCount (2 * m) := by
  sorry

theorem invCount_ge_perfectMatchings_check :
    ∀ k ∈ Finset.range 5, perfectMatchings k ≤ invCount (2 * k) := by native_decide

end InvolutionStatistics
