import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer partition examples.

This module records a finite executable table of partition numbers used as
sanity checks for the ordinary generating function examples.
-/

namespace AnalyticCombinatorics.Examples.IntegerPartitions

/-- Partition numbers `p(n)` for `0 ≤ n ≤ 20`, with `0` outside the table. -/
def partitionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 7
  | 6 => 11
  | 7 => 15
  | 8 => 22
  | 9 => 30
  | 10 => 42
  | 11 => 56
  | 12 => 77
  | 13 => 101
  | 14 => 135
  | 15 => 176
  | 16 => 231
  | 17 => 297
  | 18 => 385
  | 19 => 490
  | 20 => 627
  | _ => 0

example : partitionCount 0 = 1 := by native_decide
example : partitionCount 1 = 1 := by native_decide
example : partitionCount 2 = 2 := by native_decide
example : partitionCount 3 = 3 := by native_decide
example : partitionCount 4 = 5 := by native_decide
example : partitionCount 5 = 7 := by native_decide
example : partitionCount 6 = 11 := by native_decide
example : partitionCount 7 = 15 := by native_decide
example : partitionCount 8 = 22 := by native_decide
example : partitionCount 9 = 30 := by native_decide
example : partitionCount 10 = 42 := by native_decide
example : partitionCount 11 = 56 := by native_decide
example : partitionCount 12 = 77 := by native_decide
example : partitionCount 13 = 101 := by native_decide
example : partitionCount 14 = 135 := by native_decide
example : partitionCount 15 = 176 := by native_decide
example : partitionCount 16 = 231 := by native_decide
example : partitionCount 17 = 297 := by native_decide
example : partitionCount 18 = 385 := by native_decide
example : partitionCount 19 = 490 := by native_decide
example : partitionCount 20 = 627 := by native_decide

/-- Initial partition table as a compact executable check. -/
theorem partitionCount_values_0_to_20 :
    (List.range 21).map partitionCount =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42,
        56, 77, 101, 135, 176, 231, 297, 385, 490, 627] := by
  native_decide

/-- First finite difference of the partition table. -/
def partitionCountDelta (n : ℕ) : ℕ :=
  partitionCount (n + 1) - partitionCount n

theorem partitionCountDelta_ten :
    partitionCountDelta 10 = 14 := by
  native_decide

/-- Prefix table for partition counts through `n`, using the finite data above. -/
def partitionCountPrefix (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun acc k => acc + partitionCount k) 0

theorem partitionCountPrefix_five :
    partitionCountPrefix 5 = 19 := by
  native_decide

structure IntegerPartitionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntegerPartitionsBudgetCertificate.controlled
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def IntegerPartitionsBudgetCertificate.budgetControlled
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def IntegerPartitionsBudgetCertificate.Ready
    (c : IntegerPartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntegerPartitionsBudgetCertificate.size
    (c : IntegerPartitionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem integerPartitions_budgetCertificate_le_size
    (c : IntegerPartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleIntegerPartitionsBudgetCertificate :
    IntegerPartitionsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleIntegerPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionsBudgetCertificate.controlled,
      sampleIntegerPartitionsBudgetCertificate]
  · norm_num [IntegerPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleIntegerPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [IntegerPartitionsBudgetCertificate.controlled,
      sampleIntegerPartitionsBudgetCertificate]
  · norm_num [IntegerPartitionsBudgetCertificate.budgetControlled,
      sampleIntegerPartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntegerPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleIntegerPartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List IntegerPartitionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIntegerPartitionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleIntegerPartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.IntegerPartitions
