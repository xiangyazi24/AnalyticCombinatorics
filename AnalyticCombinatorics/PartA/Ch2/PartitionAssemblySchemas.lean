import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Partition assembly schemas.

The record stores block count, label count, and slack data for finite
partition assemblies.
-/

namespace AnalyticCombinatorics.PartA.Ch2.PartitionAssemblySchemas

structure PartitionAssemblyData where
  blockCount : ℕ
  labelCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def blocksNonempty (d : PartitionAssemblyData) : Prop :=
  0 < d.blockCount

def blocksControlledByLabels (d : PartitionAssemblyData) : Prop :=
  d.blockCount ≤ d.labelCount + d.slack

def partitionAssemblyReady (d : PartitionAssemblyData) : Prop :=
  blocksNonempty d ∧ blocksControlledByLabels d

def partitionAssemblyBudget (d : PartitionAssemblyData) : ℕ :=
  d.blockCount + d.labelCount + d.slack

theorem partitionAssemblyReady.blocks {d : PartitionAssemblyData}
    (h : partitionAssemblyReady d) :
    blocksNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem labelCount_le_partitionAssemblyBudget (d : PartitionAssemblyData) :
    d.labelCount ≤ partitionAssemblyBudget d := by
  unfold partitionAssemblyBudget
  omega

def samplePartitionAssemblyData : PartitionAssemblyData :=
  { blockCount := 5, labelCount := 7, slack := 1 }

example : partitionAssemblyReady samplePartitionAssemblyData := by
  norm_num [partitionAssemblyReady, blocksNonempty]
  norm_num [blocksControlledByLabels, samplePartitionAssemblyData]

example : partitionAssemblyBudget samplePartitionAssemblyData = 13 := by
  native_decide

structure PartitionAssemblyWindow where
  blockCount : ℕ
  labelCount : ℕ
  assemblySlack : ℕ
  refinementBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartitionAssemblyWindow.blocksControlled (w : PartitionAssemblyWindow) : Prop :=
  w.blockCount ≤ w.labelCount + w.assemblySlack + w.slack

def PartitionAssemblyWindow.refinementControlled (w : PartitionAssemblyWindow) : Prop :=
  w.refinementBudget ≤ w.blockCount + w.labelCount + w.assemblySlack + w.slack

def partitionAssemblyWindowReady (w : PartitionAssemblyWindow) : Prop :=
  0 < w.blockCount ∧
    w.blocksControlled ∧
    w.refinementControlled

def PartitionAssemblyWindow.certificate (w : PartitionAssemblyWindow) : ℕ :=
  w.blockCount + w.labelCount + w.assemblySlack + w.slack

theorem partitionAssembly_refinementBudget_le_certificate {w : PartitionAssemblyWindow}
    (h : partitionAssemblyWindowReady w) :
    w.refinementBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrefine⟩
  exact hrefine

def samplePartitionAssemblyWindow : PartitionAssemblyWindow :=
  { blockCount := 5, labelCount := 7, assemblySlack := 1, refinementBudget := 12, slack := 0 }

example : partitionAssemblyWindowReady samplePartitionAssemblyWindow := by
  norm_num [partitionAssemblyWindowReady, PartitionAssemblyWindow.blocksControlled,
    PartitionAssemblyWindow.refinementControlled, samplePartitionAssemblyWindow]

example : samplePartitionAssemblyWindow.certificate = 13 := by
  native_decide


structure PartitionAssemblySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PartitionAssemblySchemasBudgetCertificate.controlled
    (c : PartitionAssemblySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PartitionAssemblySchemasBudgetCertificate.budgetControlled
    (c : PartitionAssemblySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PartitionAssemblySchemasBudgetCertificate.Ready
    (c : PartitionAssemblySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PartitionAssemblySchemasBudgetCertificate.size
    (c : PartitionAssemblySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem partitionAssemblySchemas_budgetCertificate_le_size
    (c : PartitionAssemblySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePartitionAssemblySchemasBudgetCertificate :
    PartitionAssemblySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePartitionAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionAssemblySchemasBudgetCertificate.controlled,
      samplePartitionAssemblySchemasBudgetCertificate]
  · norm_num [PartitionAssemblySchemasBudgetCertificate.budgetControlled,
      samplePartitionAssemblySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePartitionAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionAssemblySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePartitionAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PartitionAssemblySchemasBudgetCertificate.controlled,
      samplePartitionAssemblySchemasBudgetCertificate]
  · norm_num [PartitionAssemblySchemasBudgetCertificate.budgetControlled,
      samplePartitionAssemblySchemasBudgetCertificate]

example :
    samplePartitionAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePartitionAssemblySchemasBudgetCertificate.size := by
  apply partitionAssemblySchemas_budgetCertificate_le_size
  constructor
  · norm_num [PartitionAssemblySchemasBudgetCertificate.controlled,
      samplePartitionAssemblySchemasBudgetCertificate]
  · norm_num [PartitionAssemblySchemasBudgetCertificate.budgetControlled,
      samplePartitionAssemblySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PartitionAssemblySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePartitionAssemblySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePartitionAssemblySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.PartitionAssemblySchemas
