import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace PermutationCycles

open Finset

/-! ## Unsigned Stirling numbers of the first kind

`stirling1 n k` counts the number of permutations of `[n]` with exactly `k` cycles.
The recurrence reflects the two ways to insert the element `n+1` into a permutation of `[n]`:
- place it in one of the `n` existing cycle positions (multiplies by `n`), keeping `k+1` cycles, or
- make it a new fixed-point cycle (adds 1 cycle, from `k` to `k+1`).
-/

/-- Unsigned Stirling numbers of the first kind: `|s(n,k)|` = number of permutations
    of `[n]` with exactly `k` cycles. -/
def stirling1 : ℕ → ℕ → ℕ
  | 0, 0       => 1
  | 0, _ + 1   => 0
  | _ + 1, 0   => 0
  | n + 1, k + 1 => n * stirling1 n (k + 1) + stirling1 n k

/-! ### Small values -/

theorem stirling1_1_1 : stirling1 1 1 = 1 := by native_decide
theorem stirling1_2_1 : stirling1 2 1 = 1 := by native_decide
theorem stirling1_2_2 : stirling1 2 2 = 1 := by native_decide
theorem stirling1_3_1 : stirling1 3 1 = 2 := by native_decide
theorem stirling1_3_2 : stirling1 3 2 = 3 := by native_decide
theorem stirling1_3_3 : stirling1 3 3 = 1 := by native_decide

/-! ### Row n = 4: |s(4,k)| = 6, 11, 6, 1 -/

theorem stirling1_4_1 : stirling1 4 1 = 6  := by native_decide
theorem stirling1_4_2 : stirling1 4 2 = 11 := by native_decide
theorem stirling1_4_3 : stirling1 4 3 = 6  := by native_decide
theorem stirling1_4_4 : stirling1 4 4 = 1  := by native_decide

/-! ### Row n = 5: |s(5,k)| = 24, 50, 35, 10, 1 -/

theorem stirling1_5_1 : stirling1 5 1 = 24 := by native_decide
theorem stirling1_5_2 : stirling1 5 2 = 50 := by native_decide
theorem stirling1_5_3 : stirling1 5 3 = 35 := by native_decide
theorem stirling1_5_4 : stirling1 5 4 = 10 := by native_decide
theorem stirling1_5_5 : stirling1 5 5 = 1  := by native_decide

/-! ## Row sums equal n!

The row sum `∑_k |s(n,k)| = n!` because the Stirling numbers partition all permutations
of `[n]` by cycle count.
-/

theorem stirling1_rowsum_1 :
    ∑ k ∈ Finset.range 2, stirling1 1 k = Nat.factorial 1 := by native_decide

theorem stirling1_rowsum_2 :
    ∑ k ∈ Finset.range 3, stirling1 2 k = Nat.factorial 2 := by native_decide

theorem stirling1_rowsum_3 :
    ∑ k ∈ Finset.range 4, stirling1 3 k = Nat.factorial 3 := by native_decide

theorem stirling1_rowsum_4 :
    ∑ k ∈ Finset.range 5, stirling1 4 k = Nat.factorial 4 := by native_decide

theorem stirling1_rowsum_5 :
    ∑ k ∈ Finset.range 6, stirling1 5 k = Nat.factorial 5 := by native_decide

theorem stirling1_rowsum_6 :
    ∑ k ∈ Finset.range 7, stirling1 6 k = Nat.factorial 6 := by native_decide

/-- For `n ≤ 6`, the unsigned Stirling numbers sum to `n!`. -/
theorem stirling1_rowsum_upto_six (n : ℕ) (hn : n ≤ 6) :
    ∑ k ∈ Finset.range (n + 1), stirling1 n k = Nat.factorial n := by
  interval_cases n <;> native_decide

/-! ## Single-cycle permutations: |s(n,1)| = (n-1)!

A permutation of `[n]` that forms a single cycle is an `n`-cycle, and there are `(n-1)!` of them.
-/

theorem stirling1_single_cycle_4 : stirling1 4 1 = Nat.factorial 3 := by native_decide
theorem stirling1_single_cycle_5 : stirling1 5 1 = Nat.factorial 4 := by native_decide
theorem stirling1_single_cycle_6 : stirling1 6 1 = Nat.factorial 5 := by native_decide

/-- For `2 ≤ n ≤ 7`, the number of single-cycle permutations is `(n-1)!`. -/
theorem stirling1_single_cycle (n : ℕ) (hn : 2 ≤ n) (hn' : n ≤ 7) :
    stirling1 n 1 = Nat.factorial (n - 1) := by
  interval_cases n <;> native_decide

/-! ## Total cycle count across all permutations

The expected number of cycles in a uniform random permutation of `[n]` is the harmonic number
`H_n = 1 + 1/2 + … + 1/n`. Equivalently, the total cycle count (summed over all permutations)
is `n! · H_n`. In integer arithmetic this equals `∑_k k · |s(n,k)|`.

Verification table:
- n = 3: 1·2 + 2·3 + 3·1 = 11;  3!·H_3 = 6·(11/6) = 11  ✓
- n = 4: 1·6 + 2·11 + 3·6 + 4·1 = 50;  4!·H_4 = 24·(25/12) = 50  ✓
- n = 5: 1·24 + 2·50 + 3·35 + 4·10 + 5·1 = 274;  5!·H_5 = 120·(137/60) = 274  ✓
-/

theorem total_cycles_3 :
    ∑ k ∈ Finset.range 3, (k + 1) * stirling1 3 (k + 1) = 11 := by native_decide

theorem total_cycles_4 :
    ∑ k ∈ Finset.range 4, (k + 1) * stirling1 4 (k + 1) = 50 := by native_decide

theorem total_cycles_5 :
    ∑ k ∈ Finset.range 5, (k + 1) * stirling1 5 (k + 1) = 274 := by native_decide

theorem total_cycles_6 :
    ∑ k ∈ Finset.range 6, (k + 1) * stirling1 6 (k + 1) = 1764 := by native_decide

/-! ## Stirling numbers of the second kind S(n,k)

`stirling2PC n k` counts the number of ways to partition a set of `n` elements into `k`
non-empty subsets.  (We use the suffix `PC` to avoid a name clash with the `stirling2`
defined in `BellNumbers.lean`.)
-/

/-- Stirling numbers of the second kind: `S(n,k)` = set partitions of `[n]` into `k` blocks. -/
def stirling2PC : ℕ → ℕ → ℕ
  | 0, 0       => 1
  | 0, _ + 1   => 0
  | _ + 1, 0   => 0
  | n + 1, k + 1 => (k + 1) * stirling2PC n (k + 1) + stirling2PC n k

/-! ### Selected values -/

theorem stirling2PC_4_2 : stirling2PC 4 2 = 7  := by native_decide
theorem stirling2PC_5_2 : stirling2PC 5 2 = 15 := by native_decide
theorem stirling2PC_5_3 : stirling2PC 5 3 = 25 := by native_decide

/-! ### Bell numbers as row sums of S(n,k)

`B_n = ∑_k S(n,k)`.  Checked for `n = 0, …, 5`.
-/

theorem bell_4 : ∑ k ∈ Finset.range 5, stirling2PC 4 k = 15 := by native_decide
theorem bell_5 : ∑ k ∈ Finset.range 6, stirling2PC 5 k = 52 := by native_decide

/-- Bell numbers via `stirling2PC` row sums, for `n ≤ 5`. -/
def bellPC (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), stirling2PC n k

theorem bellPC_0 : bellPC 0 = 1  := by native_decide
theorem bellPC_1 : bellPC 1 = 1  := by native_decide
theorem bellPC_2 : bellPC 2 = 2  := by native_decide
theorem bellPC_3 : bellPC 3 = 5  := by native_decide
theorem bellPC_4 : bellPC 4 = 15 := by native_decide
theorem bellPC_5 : bellPC 5 = 52 := by native_decide

/-! ### Cross-checks between |s(n,k)| and S(n,k)

We verify the two tables agree with known values and that their row sums are consistent.
-/

/-- `∑_k stirling1 n k = n!` for `n ≤ 6`, verified numerically. -/
theorem stirling1_rowsum_check (n : ℕ) (hn : n ≤ 6) :
    ∑ k ∈ Finset.range (n + 1), stirling1 n k = Nat.factorial n := by
  interval_cases n <;> native_decide

/-- `stirling2PC n n = 1` for `n ≤ 6` (only one partition of `[n]` into `n` singletons). -/
theorem stirling2PC_diag (n : ℕ) (hn : n ≤ 6) :
    stirling2PC n n = 1 := by
  interval_cases n <;> native_decide

/-- `stirling2PC n 1 = 1` for `1 ≤ n ≤ 6` (only one way to put all elements in one block). -/
theorem stirling2PC_one_block (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 6) :
    stirling2PC n 1 = 1 := by
  interval_cases n <;> native_decide

/-- `stirling1 n n = 1` for `n ≤ 6` (only the identity permutation has `n` singleton cycles). -/
theorem stirling1_diag (n : ℕ) (hn : n ≤ 6) :
    stirling1 n n = 1 := by
  interval_cases n <;> native_decide

end PermutationCycles
