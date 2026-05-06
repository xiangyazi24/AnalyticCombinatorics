import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cycle construction schemas for labelled classes.

The file tracks cycle length, label count, and symmetry budget.
-/

namespace AnalyticCombinatorics.PartA.Ch2.CycleConstructionSchemas

structure CycleConstructionData where
  cycleLength : ℕ
  labelBudget : ℕ
  symmetryBudget : ℕ
deriving DecidableEq, Repr

def nonemptyCycle (d : CycleConstructionData) : Prop :=
  0 < d.cycleLength

def cycleLabelsControlled (d : CycleConstructionData) : Prop :=
  d.cycleLength ≤ d.labelBudget + d.symmetryBudget

def cycleConstructionReady (d : CycleConstructionData) : Prop :=
  nonemptyCycle d ∧ cycleLabelsControlled d

def cycleConstructionBudget (d : CycleConstructionData) : ℕ :=
  d.cycleLength + d.labelBudget + d.symmetryBudget

theorem cycleConstructionReady.nonempty {d : CycleConstructionData}
    (h : cycleConstructionReady d) :
    nonemptyCycle d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem cycleLength_le_budget (d : CycleConstructionData) :
    d.cycleLength ≤ cycleConstructionBudget d := by
  unfold cycleConstructionBudget
  omega

def sampleCycleConstruction : CycleConstructionData :=
  { cycleLength := 4, labelBudget := 5, symmetryBudget := 2 }

example : cycleConstructionReady sampleCycleConstruction := by
  norm_num [cycleConstructionReady, nonemptyCycle, cycleLabelsControlled, sampleCycleConstruction]

example : cycleConstructionBudget sampleCycleConstruction = 11 := by
  native_decide

structure CycleConstructionWindow where
  cycleLength : ℕ
  labelBudget : ℕ
  symmetryBudget : ℕ
  orbitCount : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleConstructionWindow.nonempty (w : CycleConstructionWindow) : Prop :=
  0 < w.cycleLength

def CycleConstructionWindow.labelsControlled (w : CycleConstructionWindow) : Prop :=
  w.cycleLength ≤ w.labelBudget + w.symmetryBudget + w.slack

def CycleConstructionWindow.orbitControlled (w : CycleConstructionWindow) : Prop :=
  w.orbitCount ≤ w.labelBudget + w.symmetryBudget + w.slack

def CycleConstructionWindow.ready (w : CycleConstructionWindow) : Prop :=
  w.nonempty ∧ w.labelsControlled ∧ w.orbitControlled

def CycleConstructionWindow.certificate (w : CycleConstructionWindow) : ℕ :=
  w.cycleLength + w.labelBudget + w.symmetryBudget + w.orbitCount + w.slack

theorem orbitCount_le_certificate (w : CycleConstructionWindow) :
    w.orbitCount ≤ w.certificate := by
  unfold CycleConstructionWindow.certificate
  omega

def sampleCycleConstructionWindow : CycleConstructionWindow :=
  { cycleLength := 4, labelBudget := 5, symmetryBudget := 2, orbitCount := 3, slack := 0 }

example : sampleCycleConstructionWindow.ready := by
  norm_num [sampleCycleConstructionWindow, CycleConstructionWindow.ready,
    CycleConstructionWindow.nonempty, CycleConstructionWindow.labelsControlled,
    CycleConstructionWindow.orbitControlled]


structure CycleConstructionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CycleConstructionSchemasBudgetCertificate.controlled
    (c : CycleConstructionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CycleConstructionSchemasBudgetCertificate.budgetControlled
    (c : CycleConstructionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CycleConstructionSchemasBudgetCertificate.Ready
    (c : CycleConstructionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CycleConstructionSchemasBudgetCertificate.size
    (c : CycleConstructionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cycleConstructionSchemas_budgetCertificate_le_size
    (c : CycleConstructionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCycleConstructionSchemasBudgetCertificate :
    CycleConstructionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCycleConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleConstructionSchemasBudgetCertificate.controlled,
      sampleCycleConstructionSchemasBudgetCertificate]
  · norm_num [CycleConstructionSchemasBudgetCertificate.budgetControlled,
      sampleCycleConstructionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCycleConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleConstructionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCycleConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CycleConstructionSchemasBudgetCertificate.controlled,
      sampleCycleConstructionSchemasBudgetCertificate]
  · norm_num [CycleConstructionSchemasBudgetCertificate.budgetControlled,
      sampleCycleConstructionSchemasBudgetCertificate]

example :
    sampleCycleConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCycleConstructionSchemasBudgetCertificate.size := by
  apply cycleConstructionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CycleConstructionSchemasBudgetCertificate.controlled,
      sampleCycleConstructionSchemasBudgetCertificate]
  · norm_num [CycleConstructionSchemasBudgetCertificate.budgetControlled,
      sampleCycleConstructionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CycleConstructionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCycleConstructionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCycleConstructionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CycleConstructionSchemas
