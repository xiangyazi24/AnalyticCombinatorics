import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.PartitionLattice


/-!
# Partition lattice and Möbius function on set partitions

Small computable checks for the set-partition lattice appearing in Chapter II of
*Analytic Combinatorics*.  The convention is that `[n]` denotes an `n`-element
labelled set.
-/

/-- Bell numbers `B(0), ..., B(7)`. -/
def bellTable : Fin 8 → ℕ := ![1, 1, 2, 5, 15, 52, 203, 877]

/-- A table-backed Bell-number function for the small checks in this file. -/
def bellNumber (n : ℕ) : ℕ :=
  if h : n < 8 then bellTable ⟨n, h⟩ else 0

theorem bell_zero : bellNumber 0 = 1 := by native_decide

theorem bell_one : bellNumber 1 = 1 := by native_decide

theorem bell_two : bellNumber 2 = 2 := by native_decide

theorem bell_three : bellNumber 3 = 5 := by native_decide

theorem bell_four : bellNumber 4 = 15 := by native_decide

theorem bell_five : bellNumber 5 = 52 := by native_decide

theorem bell_six : bellNumber 6 = 203 := by native_decide

theorem bell_seven : bellNumber 7 = 877 := by native_decide

/-- Checked Bell recurrence `B(n+1) = ∑_{k=0}^n binom(n,k) B(k)`, for `n ≤ 6`. -/
theorem bell_recurrence_upto_six :
    ∀ n : Fin 7,
      bellNumber (n.val + 1) =
        ∑ k ∈ Finset.range (n.val + 1), Nat.choose n.val k * bellNumber k := by native_decide

/-- Stirling numbers of the second kind, by the standard recurrence. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)

/-- Small table of `S(n,k)` for `0 ≤ n,k ≤ 7`. -/
def stirling2Table : Fin 8 → Fin 8 → ℕ :=
  ![
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 3, 1, 0, 0, 0, 0],
    ![0, 1, 7, 6, 1, 0, 0, 0],
    ![0, 1, 15, 25, 10, 1, 0, 0],
    ![0, 1, 31, 90, 65, 15, 1, 0],
    ![0, 1, 63, 301, 350, 140, 21, 1]
  ]

theorem stirling2_table_matches_recurrence :
    ∀ n : Fin 8, ∀ k : Fin 8, stirling2Table n k = stirling2 n.val k.val := by native_decide

theorem stirling2_one_block_upto_seven :
    ∀ n : Fin 8, 1 ≤ n.val → stirling2 n.val 1 = 1 := by native_decide

theorem stirling2_diagonal_upto_seven :
    ∀ n : Fin 8, stirling2 n.val n.val = 1 := by native_decide

theorem stirling2_two_blocks_upto_seven :
    ∀ n : Fin 8, stirling2 n.val 2 = 2 ^ (n.val - 1) - 1 := by native_decide

/-- The number of partitions of `[n]` into exactly `k` blocks. -/
def partitionLatticeRankCount (n k : ℕ) : ℕ :=
  stirling2 n k

theorem partition_lattice_rank_count_eq_stirling2_upto_seven :
    ∀ n : Fin 8, ∀ k : Fin 8,
      partitionLatticeRankCount n.val k.val = stirling2 n.val k.val := by native_decide

theorem bell_eq_sum_stirling2_one :
    (∑ k ∈ Finset.range (1 + 1), stirling2 1 k) = bellNumber 1 := by native_decide

theorem bell_eq_sum_stirling2_two :
    (∑ k ∈ Finset.range (2 + 1), stirling2 2 k) = bellNumber 2 := by native_decide

theorem bell_eq_sum_stirling2_three :
    (∑ k ∈ Finset.range (3 + 1), stirling2 3 k) = bellNumber 3 := by native_decide

theorem bell_eq_sum_stirling2_four :
    (∑ k ∈ Finset.range (4 + 1), stirling2 4 k) = bellNumber 4 := by native_decide

theorem bell_eq_sum_stirling2_five :
    (∑ k ∈ Finset.range (5 + 1), stirling2 5 k) = bellNumber 5 := by native_decide

theorem bell_eq_sum_stirling2_six :
    (∑ k ∈ Finset.range (6 + 1), stirling2 6 k) = bellNumber 6 := by native_decide

theorem bell_eq_sum_stirling2_upto_six :
    ∀ n : Fin 6,
      (∑ k ∈ Finset.range (n.val + 1 + 1), stirling2 (n.val + 1) k) =
        bellNumber (n.val + 1) := by native_decide

/-- Ordered set partitions, also called Fubini or ordered Bell numbers. -/
def fubiniNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.factorial k * stirling2 n k

/-- Fubini numbers `a(0), ..., a(5)`. -/
def fubiniTable : Fin 6 → ℕ := ![1, 1, 3, 13, 75, 541]

theorem fubini_table_matches_formula :
    ∀ n : Fin 6, fubiniTable n = fubiniNumber n.val := by native_decide

theorem fubini_zero : fubiniNumber 0 = 1 := by native_decide

theorem fubini_one : fubiniNumber 1 = 1 := by native_decide

theorem fubini_two : fubiniNumber 2 = 3 := by native_decide

theorem fubini_three : fubiniNumber 3 = 13 := by native_decide

theorem fubini_four : fubiniNumber 4 = 75 := by native_decide

theorem fubini_five : fubiniNumber 5 = 541 := by native_decide

/-- Möbius factor for a block of size `m` in an interval of the partition lattice. -/
def mobiusBlockFactor (m : ℕ) : ℤ :=
  if m = 0 then 0 else (-1 : ℤ) ^ (m - 1) * (Nat.factorial (m - 1) : ℤ)

/-- Bottom-to-top Möbius value of the partition lattice on an `n`-element set. -/
def mobiusBottomTop (n : ℕ) : ℤ :=
  mobiusBlockFactor n

/-- Product formula over block sizes for the Möbius function from bottom to a partition. -/
def mobiusByBlockSizes (sizes : List ℕ) : ℤ :=
  (sizes.map mobiusBlockFactor).prod

theorem mobius_bottom_top_one : mobiusBottomTop 1 = 1 := by native_decide

theorem mobius_bottom_top_two : mobiusBottomTop 2 = -1 := by native_decide

theorem mobius_bottom_top_three : mobiusBottomTop 3 = 2 := by native_decide

theorem mobius_bottom_top_four : mobiusBottomTop 4 = -6 := by native_decide

theorem mobius_block_sizes_example : mobiusByBlockSizes [2, 3] = -2 := by native_decide



structure PartitionLatticeBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartitionLatticeBudgetCertificate.controlled
    (c : PartitionLatticeBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PartitionLatticeBudgetCertificate.budgetControlled
    (c : PartitionLatticeBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PartitionLatticeBudgetCertificate.Ready
    (c : PartitionLatticeBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PartitionLatticeBudgetCertificate.size
    (c : PartitionLatticeBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem partitionLattice_budgetCertificate_le_size
    (c : PartitionLatticeBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePartitionLatticeBudgetCertificate :
    PartitionLatticeBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePartitionLatticeBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionLatticeBudgetCertificate.controlled,
      samplePartitionLatticeBudgetCertificate]
  · norm_num [PartitionLatticeBudgetCertificate.budgetControlled,
      samplePartitionLatticeBudgetCertificate]

example :
    samplePartitionLatticeBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionLatticeBudgetCertificate.size := by
  apply partitionLattice_budgetCertificate_le_size
  constructor
  · norm_num [PartitionLatticeBudgetCertificate.controlled,
      samplePartitionLatticeBudgetCertificate]
  · norm_num [PartitionLatticeBudgetCertificate.budgetControlled,
      samplePartitionLatticeBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePartitionLatticeBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionLatticeBudgetCertificate.controlled,
      samplePartitionLatticeBudgetCertificate]
  · norm_num [PartitionLatticeBudgetCertificate.budgetControlled,
      samplePartitionLatticeBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePartitionLatticeBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionLatticeBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PartitionLatticeBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePartitionLatticeBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePartitionLatticeBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.PartitionLattice
