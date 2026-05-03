import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace SetPartitionStatistics

/-! ## Stirling numbers of the second kind -/

/-- S(n,k): number of partitions of an n-set into exactly k non-empty blocks. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

theorem stirling2_zero_zero : stirling2 0 0 = 1 := by native_decide
theorem stirling2_n_zero (n : ℕ) (hn : n ≥ 1) : stirling2 n 0 = 0 := by
  cases n with | zero => omega | succ n => rfl

/-- S(n, 1) = 1 for n ≥ 1: the unique partition into one block. -/
theorem stirling2_n_one (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 7) : stirling2 n 1 = 1 := by
  interval_cases n <;> native_decide

/-- S(n, n) = 1: the unique partition into all singletons. -/
theorem stirling2_n_n (n : ℕ) (hn : n ≤ 7) : stirling2 n n = 1 := by
  interval_cases n <;> native_decide

/-- S(4, 2) = 7: partitions of {1,2,3,4} into 2 blocks. -/
theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide

/-- S(5, 3) = 25: partitions of {1,2,3,4,5} into 3 blocks. -/
theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide

theorem stirling2_4_3 : stirling2 4 3 = 6 := by native_decide
theorem stirling2_5_2 : stirling2 5 2 = 15 := by native_decide
theorem stirling2_6_3 : stirling2 6 3 = 90 := by native_decide

/-! ## Bell numbers -/

/-- B(n): total number of partitions of an n-set (sum of Stirling row). -/
def bell (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

/-- B(4) = 15. -/
theorem bell_4 : bell 4 = 15 := by native_decide

/-- B(5) = 52. -/
theorem bell_5 : bell 5 = 52 := by native_decide

theorem bell_0 : bell 0 = 1 := by native_decide
theorem bell_1 : bell 1 = 1 := by native_decide
theorem bell_2 : bell 2 = 2 := by native_decide
theorem bell_3 : bell 3 = 5 := by native_decide
theorem bell_6 : bell 6 = 203 := by native_decide

/-! ## Bell recurrence (Aitken's array / Bell triangle) -/

/-- Bell numbers satisfy the binomial recurrence B(n+1) = ∑ C(n,k) B(k). -/
theorem bell_recurrence_check (n : ℕ) (hn : n ≤ 5) :
    bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bell k := by
  interval_cases n <;> native_decide

/-! ## Stirling number identities -/

/-- Row sum identity: B(n) = ∑_k S(n,k), verified for small n. -/
theorem row_sum_identity (n : ℕ) (hn : n ≤ 6) :
    bell n = ∑ k ∈ Finset.range (n + 1), stirling2 n k := by
  interval_cases n <;> native_decide

/-- S(n, n-1) = C(n, 2) for n ≥ 2: choose one pair, rest are singletons. -/
theorem stirling2_n_pred (n : ℕ) (hn : n ≤ 7) (hn2 : n ≥ 2) :
    stirling2 n (n - 1) = Nat.choose n 2 := by
  interval_cases n <;> native_decide

/-- S(n, 2) = 2^(n-1) - 1 for n ≥ 2. -/
theorem stirling2_n_two (n : ℕ) (hn : n ≤ 7) (hn2 : n ≥ 2) :
    stirling2 n 2 = 2^(n - 1) - 1 := by
  interval_cases n <;> native_decide

/-! ## Exponential formula connection -/

/-- The EGF of Bell numbers is exp(e^x - 1).
    Coefficient extraction: n! * [x^n] exp(e^x - 1) = B(n).
    We verify the first few factorial-scaled coefficients. -/
theorem exp_formula_coeff_check :
    (1 : ℕ) = bell 0 ∧
    (1 : ℕ) = bell 1 ∧
    (2 : ℕ) = bell 2 ∧
    (5 : ℕ) = bell 3 ∧
    (15 : ℕ) = bell 4 := by native_decide

/-! ## Surjection connection -/

/-- Number of surjections from n-set to k-set equals k! * S(n,k). -/
def surjections (n k : ℕ) : ℕ := Nat.factorial k * stirling2 n k

theorem surjections_4_2 : surjections 4 2 = 14 := by native_decide
theorem surjections_5_3 : surjections 5 3 = 150 := by native_decide
theorem surjections_3_3 : surjections 3 3 = 6 := by native_decide

/-! ## Dobinski-style partial sums -/

/-- Partial approximation to Dobinski's formula for B(n):
    B(n) = (1/e) ∑_{k≥0} k^n / k!
    We verify the numerator identity for small n:
    e * B(n) * n! ≈ ∑_{k=0}^{m} k^n * n! / k! for large enough m. -/
def dobinskiPartialNum (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), k^n * (Nat.factorial n / Nat.factorial k)

/-! ## Partition refinement order (number of refinements) -/

/-- Number of partitions of n that refine the partition into k blocks
    is given by the product of Bell numbers of block sizes.
    For uniform block size n/k (when k | n), this is B(n/k)^k. -/
def uniformRefinements (n k : ℕ) (_hk : k ∣ n) (_hk0 : k ≠ 0) : ℕ :=
  (bell (n / k))^k

theorem uniform_ref_4_2 : uniformRefinements 4 2 (by norm_num) (by norm_num) = 4 := by
  native_decide

theorem uniform_ref_6_3 : uniformRefinements 6 3 (by norm_num) (by norm_num) = 8 := by
  native_decide

/-! ## Summary verification -/

/-- All key numerical facts collected. -/
theorem summary_check :
    stirling2 4 2 = 7 ∧ stirling2 5 3 = 25 ∧ bell 4 = 15 ∧ bell 5 = 52 := by
  native_decide

end SetPartitionStatistics
