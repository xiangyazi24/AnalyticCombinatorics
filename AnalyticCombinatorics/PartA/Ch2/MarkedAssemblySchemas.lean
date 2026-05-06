import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Marked assembly schemas.

This module records finite bookkeeping for marked labelled assemblies.
-/

namespace AnalyticCombinatorics.PartA.Ch2.MarkedAssemblySchemas

structure MarkedAssemblyData where
  assemblySize : ℕ
  markedBlocks : ℕ
  markingSlack : ℕ
deriving DecidableEq, Repr

def hasAssemblySize (d : MarkedAssemblyData) : Prop :=
  0 < d.assemblySize

def markedBlocksControlled (d : MarkedAssemblyData) : Prop :=
  d.markedBlocks ≤ d.assemblySize + d.markingSlack

def markedAssemblyReady (d : MarkedAssemblyData) : Prop :=
  hasAssemblySize d ∧ markedBlocksControlled d

def markedAssemblyBudget (d : MarkedAssemblyData) : ℕ :=
  d.assemblySize + d.markedBlocks + d.markingSlack

theorem markedAssemblyReady.hasAssemblySize {d : MarkedAssemblyData}
    (h : markedAssemblyReady d) :
    hasAssemblySize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem markedBlocks_le_budget (d : MarkedAssemblyData) :
    d.markedBlocks ≤ markedAssemblyBudget d := by
  unfold markedAssemblyBudget
  omega

def sampleMarkedAssemblyData : MarkedAssemblyData :=
  { assemblySize := 6, markedBlocks := 8, markingSlack := 3 }

example : markedAssemblyReady sampleMarkedAssemblyData := by
  norm_num [markedAssemblyReady, hasAssemblySize]
  norm_num [markedBlocksControlled, sampleMarkedAssemblyData]

example : markedAssemblyBudget sampleMarkedAssemblyData = 17 := by
  native_decide

structure MarkedAssemblyWindow where
  assemblySize : ℕ
  markedBlocks : ℕ
  markingSlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MarkedAssemblyWindow.blocksControlled (w : MarkedAssemblyWindow) : Prop :=
  w.markedBlocks ≤ w.assemblySize + w.markingSlack + w.slack

def MarkedAssemblyWindow.transportControlled (w : MarkedAssemblyWindow) : Prop :=
  w.transportBudget ≤ w.assemblySize + w.markedBlocks + w.markingSlack + w.slack

def markedAssemblyWindowReady (w : MarkedAssemblyWindow) : Prop :=
  0 < w.assemblySize ∧
    w.blocksControlled ∧
    w.transportControlled

def MarkedAssemblyWindow.certificate (w : MarkedAssemblyWindow) : ℕ :=
  w.assemblySize + w.markedBlocks + w.markingSlack + w.slack

theorem markedAssembly_transportBudget_le_certificate {w : MarkedAssemblyWindow}
    (h : markedAssemblyWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def sampleMarkedAssemblyWindow : MarkedAssemblyWindow :=
  { assemblySize := 6, markedBlocks := 8, markingSlack := 3, transportBudget := 16, slack := 0 }

example : markedAssemblyWindowReady sampleMarkedAssemblyWindow := by
  norm_num [markedAssemblyWindowReady, MarkedAssemblyWindow.blocksControlled,
    MarkedAssemblyWindow.transportControlled, sampleMarkedAssemblyWindow]

example : sampleMarkedAssemblyWindow.certificate = 17 := by
  native_decide


structure MarkedAssemblySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MarkedAssemblySchemasBudgetCertificate.controlled
    (c : MarkedAssemblySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MarkedAssemblySchemasBudgetCertificate.budgetControlled
    (c : MarkedAssemblySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MarkedAssemblySchemasBudgetCertificate.Ready
    (c : MarkedAssemblySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MarkedAssemblySchemasBudgetCertificate.size
    (c : MarkedAssemblySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem markedAssemblySchemas_budgetCertificate_le_size
    (c : MarkedAssemblySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMarkedAssemblySchemasBudgetCertificate :
    MarkedAssemblySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMarkedAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MarkedAssemblySchemasBudgetCertificate.controlled,
      sampleMarkedAssemblySchemasBudgetCertificate]
  · norm_num [MarkedAssemblySchemasBudgetCertificate.budgetControlled,
      sampleMarkedAssemblySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMarkedAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMarkedAssemblySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleMarkedAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MarkedAssemblySchemasBudgetCertificate.controlled,
      sampleMarkedAssemblySchemasBudgetCertificate]
  · norm_num [MarkedAssemblySchemasBudgetCertificate.budgetControlled,
      sampleMarkedAssemblySchemasBudgetCertificate]

example :
    sampleMarkedAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMarkedAssemblySchemasBudgetCertificate.size := by
  apply markedAssemblySchemas_budgetCertificate_le_size
  constructor
  · norm_num [MarkedAssemblySchemasBudgetCertificate.controlled,
      sampleMarkedAssemblySchemasBudgetCertificate]
  · norm_num [MarkedAssemblySchemasBudgetCertificate.budgetControlled,
      sampleMarkedAssemblySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List MarkedAssemblySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMarkedAssemblySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMarkedAssemblySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.MarkedAssemblySchemas
