import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.TableauxPartitions


open Finset

/-!
Finite-table checks for standard Young tableaux and small partition counts.
All tables are represented as functions out of `Fin n`.
-/

/-! ## Standard Young tableaux via hook lengths -/

/-- Number of boxes in a Young diagram represented by its row lengths. -/
def shapeSize {h : ℕ} (rows : Fin h → ℕ) : ℕ :=
  ∑ i : Fin h, rows i

/-- Number of boxes below `(i,j)` in the same column. -/
def legLength {h : ℕ} (rows : Fin h → ℕ) (i : Fin h) (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin h)).filter fun r => i.val < r.val ∧ j < rows r).card

/-- Hook length at zero-indexed cell `(i,j)`. -/
def hookLength {h : ℕ} (rows : Fin h → ℕ) (i : Fin h) (j : ℕ) : ℕ :=
  rows i - j + legLength rows i j

/-- Hook product over all cells of the diagram. -/
def hookProduct {h : ℕ} (rows : Fin h → ℕ) : ℕ :=
  ∏ i : Fin h, ∏ j ∈ Finset.range (rows i), hookLength rows i j

/-- Standard Young tableaux count from the hook-length formula. -/
def sytByHook {h : ℕ} (rows : Fin h → ℕ) : ℕ :=
  Nat.factorial (shapeSize rows) / hookProduct rows

def shape21 : Fin 2 → ℕ := ![2, 1]
def shape22 : Fin 2 → ℕ := ![2, 2]
def shape31 : Fin 2 → ℕ := ![3, 1]
def shape32 : Fin 2 → ℕ := ![3, 2]
def shape41 : Fin 2 → ℕ := ![4, 1]

def sytHookTable : Fin 5 → ℕ :=
  ![sytByHook shape21, sytByHook shape22, sytByHook shape31,
    sytByHook shape32, sytByHook shape41]

def sytExpectedTable : Fin 5 → ℕ :=
  ![2, 2, 3, 5, 4]

theorem syt_hook_table_verified :
    ∀ i : Fin 5, sytHookTable i = sytExpectedTable i := by
  native_decide

/-! ## Integer partitions -/

/-- Partitions of `n` with every part at most `k`. -/
def partsAtMostCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      partsAtMostCount (n + 1) k +
        if k + 1 ≤ n + 1 then
          partsAtMostCount (n + 1 - (k + 1)) (k + 1)
        else
          0
termination_by n k => (n, k)
decreasing_by
  all_goals omega

/-- The ordinary partition function, computed by bounding part sizes by `n`. -/
def partitionCount (n : ℕ) : ℕ :=
  partsAtMostCount n n

def partitionTable : Fin 11 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42]

theorem partition_table_verified :
    ∀ i : Fin 11, partitionCount i.val = partitionTable i := by
  native_decide

theorem partitionCount_monotone_one_to_ten :
    ∀ i : Fin 10, partitionCount i.val ≤ partitionCount (i.val + 1) := by
  native_decide

/-! ## Distinct parts -/

/-- Partitions of `n` into distinct parts, each at most `k`. -/
def distinctPartsAtMostCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      distinctPartsAtMostCount (n + 1) k +
        if k + 1 ≤ n + 1 then
          distinctPartsAtMostCount (n + 1 - (k + 1)) k
        else
          0
termination_by n k => (n, k)
decreasing_by
  all_goals omega

/-- Partitions of `n` into distinct parts. -/
def distinctPartitionCount (n : ℕ) : ℕ :=
  distinctPartsAtMostCount n n

def distinctPartsTable : Fin 11 → ℕ :=
  ![1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10]

theorem distinct_parts_table_verified :
    ∀ i : Fin 11, distinctPartitionCount i.val = distinctPartsTable i := by
  native_decide

theorem distinct_parts_le_partitions :
    ∀ i : Fin 11, distinctPartitionCount i.val ≤ partitionCount i.val := by
  native_decide

/-! ## Part-size restrictions -/

def partsAtMostTwoTable : Fin 11 → ℕ :=
  ![1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6]

theorem parts_at_most_two_table_verified :
    ∀ i : Fin 11, partsAtMostCount i.val 2 = partsAtMostTwoTable i := by
  native_decide

theorem parts_at_most_two_closed_form :
    ∀ i : Fin 11, partsAtMostCount i.val 2 = i.val / 2 + 1 := by
  native_decide

def partsAtMostThreeTable : Fin 9 → ℕ :=
  ![1, 1, 2, 3, 4, 5, 7, 8, 10]

theorem parts_at_most_three_table_verified :
    ∀ i : Fin 9, partsAtMostCount i.val 3 = partsAtMostThreeTable i := by
  native_decide



structure TableauxPartitionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TableauxPartitionsBudgetCertificate.controlled
    (c : TableauxPartitionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TableauxPartitionsBudgetCertificate.budgetControlled
    (c : TableauxPartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TableauxPartitionsBudgetCertificate.Ready
    (c : TableauxPartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TableauxPartitionsBudgetCertificate.size
    (c : TableauxPartitionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem tableauxPartitions_budgetCertificate_le_size
    (c : TableauxPartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTableauxPartitionsBudgetCertificate :
    TableauxPartitionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTableauxPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [TableauxPartitionsBudgetCertificate.controlled,
      sampleTableauxPartitionsBudgetCertificate]
  · norm_num [TableauxPartitionsBudgetCertificate.budgetControlled,
      sampleTableauxPartitionsBudgetCertificate]

example :
    sampleTableauxPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleTableauxPartitionsBudgetCertificate.size := by
  apply tableauxPartitions_budgetCertificate_le_size
  constructor
  · norm_num [TableauxPartitionsBudgetCertificate.controlled,
      sampleTableauxPartitionsBudgetCertificate]
  · norm_num [TableauxPartitionsBudgetCertificate.budgetControlled,
      sampleTableauxPartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTableauxPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [TableauxPartitionsBudgetCertificate.controlled,
      sampleTableauxPartitionsBudgetCertificate]
  · norm_num [TableauxPartitionsBudgetCertificate.budgetControlled,
      sampleTableauxPartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTableauxPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleTableauxPartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List TableauxPartitionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTableauxPartitionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleTableauxPartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.TableauxPartitions
