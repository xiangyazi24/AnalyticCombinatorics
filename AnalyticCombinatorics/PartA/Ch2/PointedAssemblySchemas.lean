import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pointed assembly schemas.

This module records finite bookkeeping for pointed labelled assemblies.
-/

namespace AnalyticCombinatorics.PartA.Ch2.PointedAssemblySchemas

structure PointedAssemblyData where
  assemblyBlocks : ℕ
  pointChoices : ℕ
  assemblySlack : ℕ
deriving DecidableEq, Repr

def hasAssemblyBlocks (d : PointedAssemblyData) : Prop :=
  0 < d.assemblyBlocks

def pointChoicesControlled (d : PointedAssemblyData) : Prop :=
  d.pointChoices ≤ d.assemblyBlocks + d.assemblySlack

def pointedAssemblyReady (d : PointedAssemblyData) : Prop :=
  hasAssemblyBlocks d ∧ pointChoicesControlled d

def pointedAssemblyBudget (d : PointedAssemblyData) : ℕ :=
  d.assemblyBlocks + d.pointChoices + d.assemblySlack

theorem pointedAssemblyReady.hasAssemblyBlocks {d : PointedAssemblyData}
    (h : pointedAssemblyReady d) :
    hasAssemblyBlocks d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointChoices_le_budget (d : PointedAssemblyData) :
    d.pointChoices ≤ pointedAssemblyBudget d := by
  unfold pointedAssemblyBudget
  omega

def samplePointedAssemblyData : PointedAssemblyData :=
  { assemblyBlocks := 6, pointChoices := 8, assemblySlack := 3 }

example : pointedAssemblyReady samplePointedAssemblyData := by
  norm_num [pointedAssemblyReady, hasAssemblyBlocks]
  norm_num [pointChoicesControlled, samplePointedAssemblyData]

example : pointedAssemblyBudget samplePointedAssemblyData = 17 := by
  native_decide

structure PointedAssemblyWindow where
  assemblyBlocks : ℕ
  pointChoices : ℕ
  assemblySlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedAssemblyWindow.pointChoicesControlled (w : PointedAssemblyWindow) : Prop :=
  w.pointChoices ≤ w.assemblyBlocks + w.assemblySlack + w.slack

def PointedAssemblyWindow.transportControlled (w : PointedAssemblyWindow) : Prop :=
  w.transportBudget ≤ w.assemblyBlocks + w.pointChoices + w.assemblySlack + w.slack

def pointedAssemblyWindowReady (w : PointedAssemblyWindow) : Prop :=
  0 < w.assemblyBlocks ∧
    w.pointChoicesControlled ∧
    w.transportControlled

def PointedAssemblyWindow.certificate (w : PointedAssemblyWindow) : ℕ :=
  w.assemblyBlocks + w.pointChoices + w.assemblySlack + w.slack

theorem pointedAssembly_transportBudget_le_certificate {w : PointedAssemblyWindow}
    (h : pointedAssemblyWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def samplePointedAssemblyWindow : PointedAssemblyWindow :=
  { assemblyBlocks := 6, pointChoices := 8, assemblySlack := 3, transportBudget := 16,
    slack := 0 }

example : pointedAssemblyWindowReady samplePointedAssemblyWindow := by
  norm_num [pointedAssemblyWindowReady, PointedAssemblyWindow.pointChoicesControlled,
    PointedAssemblyWindow.transportControlled, samplePointedAssemblyWindow]

example : samplePointedAssemblyWindow.certificate = 17 := by
  native_decide


structure PointedAssemblySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedAssemblySchemasBudgetCertificate.controlled
    (c : PointedAssemblySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PointedAssemblySchemasBudgetCertificate.budgetControlled
    (c : PointedAssemblySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PointedAssemblySchemasBudgetCertificate.Ready
    (c : PointedAssemblySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PointedAssemblySchemasBudgetCertificate.size
    (c : PointedAssemblySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem pointedAssemblySchemas_budgetCertificate_le_size
    (c : PointedAssemblySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePointedAssemblySchemasBudgetCertificate :
    PointedAssemblySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePointedAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedAssemblySchemasBudgetCertificate.controlled,
      samplePointedAssemblySchemasBudgetCertificate]
  · norm_num [PointedAssemblySchemasBudgetCertificate.budgetControlled,
      samplePointedAssemblySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePointedAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedAssemblySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePointedAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedAssemblySchemasBudgetCertificate.controlled,
      samplePointedAssemblySchemasBudgetCertificate]
  · norm_num [PointedAssemblySchemasBudgetCertificate.budgetControlled,
      samplePointedAssemblySchemasBudgetCertificate]

example :
    samplePointedAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedAssemblySchemasBudgetCertificate.size := by
  apply pointedAssemblySchemas_budgetCertificate_le_size
  constructor
  · norm_num [PointedAssemblySchemasBudgetCertificate.controlled,
      samplePointedAssemblySchemasBudgetCertificate]
  · norm_num [PointedAssemblySchemasBudgetCertificate.budgetControlled,
      samplePointedAssemblySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PointedAssemblySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePointedAssemblySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePointedAssemblySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.PointedAssemblySchemas
