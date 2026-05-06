import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite composition schema models.

The finite record stores core size, component budget, and composition
slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteCompositionSchemaModels

structure CompositionSchemaData where
  coreSize : ℕ
  componentBudget : ℕ
  compositionSlack : ℕ
deriving DecidableEq, Repr

def coreSizePositive (d : CompositionSchemaData) : Prop :=
  0 < d.coreSize

def componentsControlled (d : CompositionSchemaData) : Prop :=
  d.componentBudget ≤ d.coreSize + d.compositionSlack

def compositionSchemaReady (d : CompositionSchemaData) : Prop :=
  coreSizePositive d ∧ componentsControlled d

def compositionSchemaBudget (d : CompositionSchemaData) : ℕ :=
  d.coreSize + d.componentBudget + d.compositionSlack

theorem compositionSchemaReady.core {d : CompositionSchemaData}
    (h : compositionSchemaReady d) :
    coreSizePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem componentBudget_le_compositionSchemaBudget
    (d : CompositionSchemaData) :
    d.componentBudget ≤ compositionSchemaBudget d := by
  unfold compositionSchemaBudget
  omega

def sampleCompositionSchemaData : CompositionSchemaData :=
  { coreSize := 7, componentBudget := 9, compositionSlack := 3 }

example : compositionSchemaReady sampleCompositionSchemaData := by
  norm_num [compositionSchemaReady, coreSizePositive]
  norm_num [componentsControlled, sampleCompositionSchemaData]

example : compositionSchemaBudget sampleCompositionSchemaData = 19 := by
  native_decide

structure CompositionSchemaWindow where
  coreSize : ℕ
  componentBudget : ℕ
  compositionSlack : ℕ
  expansionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionSchemaWindow.componentControlled (w : CompositionSchemaWindow) : Prop :=
  w.componentBudget ≤ w.coreSize + w.compositionSlack + w.slack

def CompositionSchemaWindow.expansionControlled (w : CompositionSchemaWindow) : Prop :=
  w.expansionBudget ≤ w.coreSize + w.componentBudget + w.compositionSlack + w.slack

def compositionSchemaWindowReady (w : CompositionSchemaWindow) : Prop :=
  0 < w.coreSize ∧
    w.componentControlled ∧
    w.expansionControlled

def CompositionSchemaWindow.certificate (w : CompositionSchemaWindow) : ℕ :=
  w.coreSize + w.componentBudget + w.compositionSlack + w.slack

theorem compositionSchema_expansionBudget_le_certificate {w : CompositionSchemaWindow}
    (h : compositionSchemaWindowReady w) :
    w.expansionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hexpansion⟩
  exact hexpansion

def sampleCompositionSchemaWindow : CompositionSchemaWindow :=
  { coreSize := 7, componentBudget := 9, compositionSlack := 3, expansionBudget := 18,
    slack := 0 }

example : compositionSchemaWindowReady sampleCompositionSchemaWindow := by
  norm_num [compositionSchemaWindowReady, CompositionSchemaWindow.componentControlled,
    CompositionSchemaWindow.expansionControlled, sampleCompositionSchemaWindow]

example : sampleCompositionSchemaWindow.certificate = 19 := by
  native_decide


structure FiniteCompositionSchemaModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCompositionSchemaModelsBudgetCertificate.controlled
    (c : FiniteCompositionSchemaModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCompositionSchemaModelsBudgetCertificate.budgetControlled
    (c : FiniteCompositionSchemaModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCompositionSchemaModelsBudgetCertificate.Ready
    (c : FiniteCompositionSchemaModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCompositionSchemaModelsBudgetCertificate.size
    (c : FiniteCompositionSchemaModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCompositionSchemaModels_budgetCertificate_le_size
    (c : FiniteCompositionSchemaModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCompositionSchemaModelsBudgetCertificate :
    FiniteCompositionSchemaModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCompositionSchemaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.controlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCompositionSchemaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCompositionSchemaModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCompositionSchemaModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.controlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]

example :
    sampleFiniteCompositionSchemaModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCompositionSchemaModelsBudgetCertificate.size := by
  apply finiteCompositionSchemaModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.controlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]
  · norm_num [FiniteCompositionSchemaModelsBudgetCertificate.budgetControlled,
      sampleFiniteCompositionSchemaModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteCompositionSchemaModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCompositionSchemaModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCompositionSchemaModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCompositionSchemaModels
