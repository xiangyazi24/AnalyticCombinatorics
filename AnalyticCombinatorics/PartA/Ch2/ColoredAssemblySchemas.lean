import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Colored assembly schemas.

The finite record stores component, color, and label budgets for colored
assemblies.
-/

namespace AnalyticCombinatorics.PartA.Ch2.ColoredAssemblySchemas

structure ColoredAssemblyData where
  componentCount : ℕ
  colorCount : ℕ
  labelBudget : ℕ
deriving DecidableEq, Repr

def colorsNonempty (d : ColoredAssemblyData) : Prop :=
  0 < d.colorCount

def componentsControlled (d : ColoredAssemblyData) : Prop :=
  d.componentCount ≤ d.colorCount + d.labelBudget

def coloredAssemblyReady (d : ColoredAssemblyData) : Prop :=
  colorsNonempty d ∧ componentsControlled d

def coloredAssemblyBudget (d : ColoredAssemblyData) : ℕ :=
  d.componentCount + d.colorCount + d.labelBudget

theorem coloredAssemblyReady.colors {d : ColoredAssemblyData}
    (h : coloredAssemblyReady d) :
    colorsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem colorCount_le_coloredAssemblyBudget (d : ColoredAssemblyData) :
    d.colorCount ≤ coloredAssemblyBudget d := by
  unfold coloredAssemblyBudget
  omega

def sampleColoredAssemblyData : ColoredAssemblyData :=
  { componentCount := 6, colorCount := 4, labelBudget := 3 }

example : coloredAssemblyReady sampleColoredAssemblyData := by
  norm_num [coloredAssemblyReady, colorsNonempty]
  norm_num [componentsControlled, sampleColoredAssemblyData]

example : coloredAssemblyBudget sampleColoredAssemblyData = 13 := by
  native_decide

structure ColoredAssemblyWindow where
  componentCount : ℕ
  colorCount : ℕ
  labelBudget : ℕ
  assemblyBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ColoredAssemblyWindow.componentsControlled (w : ColoredAssemblyWindow) : Prop :=
  w.componentCount ≤ w.colorCount + w.labelBudget + w.slack

def ColoredAssemblyWindow.assemblyControlled (w : ColoredAssemblyWindow) : Prop :=
  w.assemblyBudget ≤ w.componentCount + w.colorCount + w.labelBudget + w.slack

def coloredAssemblyWindowReady (w : ColoredAssemblyWindow) : Prop :=
  0 < w.colorCount ∧
    w.componentsControlled ∧
    w.assemblyControlled

def ColoredAssemblyWindow.certificate (w : ColoredAssemblyWindow) : ℕ :=
  w.componentCount + w.colorCount + w.labelBudget + w.slack

theorem coloredAssembly_assemblyBudget_le_certificate {w : ColoredAssemblyWindow}
    (h : coloredAssemblyWindowReady w) :
    w.assemblyBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hassembly⟩
  exact hassembly

def sampleColoredAssemblyWindow : ColoredAssemblyWindow :=
  { componentCount := 6, colorCount := 4, labelBudget := 3, assemblyBudget := 12, slack := 0 }

example : coloredAssemblyWindowReady sampleColoredAssemblyWindow := by
  norm_num [coloredAssemblyWindowReady, ColoredAssemblyWindow.componentsControlled,
    ColoredAssemblyWindow.assemblyControlled, sampleColoredAssemblyWindow]

example : sampleColoredAssemblyWindow.certificate = 13 := by
  native_decide


structure ColoredAssemblySchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ColoredAssemblySchemasBudgetCertificate.controlled
    (c : ColoredAssemblySchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ColoredAssemblySchemasBudgetCertificate.budgetControlled
    (c : ColoredAssemblySchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ColoredAssemblySchemasBudgetCertificate.Ready
    (c : ColoredAssemblySchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ColoredAssemblySchemasBudgetCertificate.size
    (c : ColoredAssemblySchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coloredAssemblySchemas_budgetCertificate_le_size
    (c : ColoredAssemblySchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleColoredAssemblySchemasBudgetCertificate :
    ColoredAssemblySchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleColoredAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ColoredAssemblySchemasBudgetCertificate.controlled,
      sampleColoredAssemblySchemasBudgetCertificate]
  · norm_num [ColoredAssemblySchemasBudgetCertificate.budgetControlled,
      sampleColoredAssemblySchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleColoredAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleColoredAssemblySchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleColoredAssemblySchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ColoredAssemblySchemasBudgetCertificate.controlled,
      sampleColoredAssemblySchemasBudgetCertificate]
  · norm_num [ColoredAssemblySchemasBudgetCertificate.budgetControlled,
      sampleColoredAssemblySchemasBudgetCertificate]

example :
    sampleColoredAssemblySchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleColoredAssemblySchemasBudgetCertificate.size := by
  apply coloredAssemblySchemas_budgetCertificate_le_size
  constructor
  · norm_num [ColoredAssemblySchemasBudgetCertificate.controlled,
      sampleColoredAssemblySchemasBudgetCertificate]
  · norm_num [ColoredAssemblySchemasBudgetCertificate.budgetControlled,
      sampleColoredAssemblySchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ColoredAssemblySchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleColoredAssemblySchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleColoredAssemblySchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.ColoredAssemblySchemas
