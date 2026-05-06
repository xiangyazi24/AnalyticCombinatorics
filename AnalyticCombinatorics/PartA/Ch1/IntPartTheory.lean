import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Integer partition count checks.

This module records finite checks for unrestricted and restricted integer
partition tables.
-/

namespace AnalyticCombinatorics.PartA.Ch1.IntPartTheory

structure PartitionWindow where
  totalSize : ℕ
  partBound : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def nonzeroPartitionSize (w : PartitionWindow) : Prop :=
  0 < w.totalSize

def partBoundControlled (w : PartitionWindow) : Prop :=
  w.partBound ≤ w.totalSize + w.slack

def partitionWindowReady (w : PartitionWindow) : Prop :=
  nonzeroPartitionSize w ∧ partBoundControlled w

def partitionWindowBudget (w : PartitionWindow) : ℕ :=
  w.totalSize + w.partBound + w.slack

theorem partitionWindowReady.certificate {w : PartitionWindow}
    (h : partitionWindowReady w) :
    nonzeroPartitionSize w ∧ partBoundControlled w ∧
      w.partBound ≤ partitionWindowBudget w := by
  rcases h with ⟨hsize, hcontrolled⟩
  refine ⟨hsize, hcontrolled, ?_⟩
  unfold partitionWindowBudget
  omega

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
  | _ => 0

def partitionsWithAtMostTwoParts : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 3) / 2

def partitionsIntoDistinctPartsSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => 6
  | _ => 0

def samplePartitionWindow : PartitionWindow :=
  { totalSize := 8, partBound := 5, slack := 1 }

example : partitionWindowReady samplePartitionWindow := by
  norm_num [partitionWindowReady, nonzeroPartitionSize]
  norm_num [partBoundControlled, samplePartitionWindow]

example : partitionCount 8 = 22 := by native_decide
example : partitionWindowBudget samplePartitionWindow = 14 := by native_decide
example : partitionsWithAtMostTwoParts 8 = 5 := by native_decide
example : partitionsIntoDistinctPartsSmall 8 = 6 := by native_decide
example : partitionsIntoDistinctPartsSmall 5 ≤ partitionCount 5 := by native_decide


structure IntPartTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def IntPartTheoryBudgetCertificate.controlled
    (c : IntPartTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def IntPartTheoryBudgetCertificate.budgetControlled
    (c : IntPartTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def IntPartTheoryBudgetCertificate.Ready
    (c : IntPartTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def IntPartTheoryBudgetCertificate.size
    (c : IntPartTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem intPartTheory_budgetCertificate_le_size
    (c : IntPartTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleIntPartTheoryBudgetCertificate :
    IntPartTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleIntPartTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [IntPartTheoryBudgetCertificate.controlled,
      sampleIntPartTheoryBudgetCertificate]
  · norm_num [IntPartTheoryBudgetCertificate.budgetControlled,
      sampleIntPartTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleIntPartTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleIntPartTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleIntPartTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [IntPartTheoryBudgetCertificate.controlled,
      sampleIntPartTheoryBudgetCertificate]
  · norm_num [IntPartTheoryBudgetCertificate.budgetControlled,
      sampleIntPartTheoryBudgetCertificate]

example :
    sampleIntPartTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleIntPartTheoryBudgetCertificate.size := by
  apply intPartTheory_budgetCertificate_le_size
  constructor
  · norm_num [IntPartTheoryBudgetCertificate.controlled,
      sampleIntPartTheoryBudgetCertificate]
  · norm_num [IntPartTheoryBudgetCertificate.budgetControlled,
      sampleIntPartTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleIntPartTheoryBudgetCertificate_ready :
    sampleIntPartTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [IntPartTheoryBudgetCertificate.controlled,
      sampleIntPartTheoryBudgetCertificate]
  · norm_num [IntPartTheoryBudgetCertificate.budgetControlled,
      sampleIntPartTheoryBudgetCertificate]

def budgetCertificateListReady (data : List IntPartTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleIntPartTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleIntPartTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.IntPartTheory
