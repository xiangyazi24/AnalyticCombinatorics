import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Set partition examples.

Bell numbers count set partitions.  This module records the initial Bell table
and a finite Stirling row check.
-/

namespace AnalyticCombinatorics.Examples.SetPartitions

def bellCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 15
  | 5 => 52
  | 6 => 203
  | 7 => 877
  | 8 => 4140
  | 9 => 21147
  | 10 => 115975
  | _ => 0

/-- Small Stirling numbers of the second kind. -/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

example : bellCount 0 = 1 := by native_decide
example : bellCount 1 = 1 := by native_decide
example : bellCount 2 = 2 := by native_decide
example : bellCount 3 = 5 := by native_decide
example : bellCount 4 = 15 := by native_decide
example : bellCount 5 = 52 := by native_decide
example : bellCount 10 = 115975 := by native_decide

theorem bellCount_values_0_to_10 :
    (List.range 11).map bellCount =
      [1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975] := by
  native_decide

theorem bellCount_eq_stirling_sum_upto_8 :
    (List.range 9).all
      (fun n =>
        bellCount n ==
          (List.range (n + 1)).foldl
            (fun acc k => acc + stirlingSecond n k) 0) = true := by
  native_decide

def bellPrefixSum (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + bellCount n) 0

theorem bellPrefix_window :
    bellPrefixSum 5 = 76 := by
  unfold bellPrefixSum bellCount
  native_decide

structure SetPartitionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SetPartitionsBudgetCertificate.controlled
    (c : SetPartitionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SetPartitionsBudgetCertificate.budgetControlled
    (c : SetPartitionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SetPartitionsBudgetCertificate.Ready
    (c : SetPartitionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SetPartitionsBudgetCertificate.size
    (c : SetPartitionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem setPartitions_budgetCertificate_le_size
    (c : SetPartitionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSetPartitionsBudgetCertificate : SetPartitionsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleSetPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SetPartitionsBudgetCertificate.controlled,
      sampleSetPartitionsBudgetCertificate]
  · norm_num [SetPartitionsBudgetCertificate.budgetControlled,
      sampleSetPartitionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSetPartitionsBudgetCertificate.Ready := by
  constructor
  · norm_num [SetPartitionsBudgetCertificate.controlled,
      sampleSetPartitionsBudgetCertificate]
  · norm_num [SetPartitionsBudgetCertificate.budgetControlled,
      sampleSetPartitionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSetPartitionsBudgetCertificate.certificateBudgetWindow ≤
      sampleSetPartitionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SetPartitionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSetPartitionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSetPartitionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.SetPartitions
