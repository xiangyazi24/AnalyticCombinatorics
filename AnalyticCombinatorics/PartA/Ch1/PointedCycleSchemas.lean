import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Pointed cycle schemas.

The finite schema records cycle length, pointing choices, and symmetry
slack for pointed cycle constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.PointedCycleSchemas

structure PointedCycleData where
  cycleLength : ℕ
  pointingChoices : ℕ
  symmetrySlack : ℕ
deriving DecidableEq, Repr

def cycleLengthPositive (d : PointedCycleData) : Prop :=
  0 < d.cycleLength

def pointingControlled (d : PointedCycleData) : Prop :=
  d.pointingChoices ≤ d.cycleLength + d.symmetrySlack

def pointedCycleReady (d : PointedCycleData) : Prop :=
  cycleLengthPositive d ∧ pointingControlled d

def pointedCycleBudget (d : PointedCycleData) : ℕ :=
  d.cycleLength + d.pointingChoices + d.symmetrySlack

theorem pointedCycleReady.length {d : PointedCycleData}
    (h : pointedCycleReady d) :
    cycleLengthPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointingChoices_le_pointedCycleBudget (d : PointedCycleData) :
    d.pointingChoices ≤ pointedCycleBudget d := by
  unfold pointedCycleBudget
  omega

def samplePointedCycleData : PointedCycleData :=
  { cycleLength := 6, pointingChoices := 8, symmetrySlack := 3 }

example : pointedCycleReady samplePointedCycleData := by
  norm_num [pointedCycleReady, cycleLengthPositive]
  norm_num [pointingControlled, samplePointedCycleData]

example : pointedCycleBudget samplePointedCycleData = 17 := by
  native_decide

structure PointedCycleWindow where
  cycleLength : ℕ
  pointingChoices : ℕ
  symmetrySlack : ℕ
  orbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedCycleWindow.pointingControlled (w : PointedCycleWindow) : Prop :=
  w.pointingChoices ≤ w.cycleLength + w.symmetrySlack + w.slack

def PointedCycleWindow.orbitControlled (w : PointedCycleWindow) : Prop :=
  w.orbitBudget ≤ w.cycleLength + w.pointingChoices + w.symmetrySlack + w.slack

def pointedCycleWindowReady (w : PointedCycleWindow) : Prop :=
  0 < w.cycleLength ∧
    w.pointingControlled ∧
    w.orbitControlled

def PointedCycleWindow.certificate (w : PointedCycleWindow) : ℕ :=
  w.cycleLength + w.pointingChoices + w.symmetrySlack + w.slack

theorem pointedCycle_orbitBudget_le_certificate {w : PointedCycleWindow}
    (h : pointedCycleWindowReady w) :
    w.orbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def samplePointedCycleWindow : PointedCycleWindow :=
  { cycleLength := 6, pointingChoices := 8, symmetrySlack := 3, orbitBudget := 16, slack := 0 }

example : pointedCycleWindowReady samplePointedCycleWindow := by
  norm_num [pointedCycleWindowReady, PointedCycleWindow.pointingControlled,
    PointedCycleWindow.orbitControlled, samplePointedCycleWindow]

example : samplePointedCycleWindow.certificate = 17 := by
  native_decide


structure PointedCycleSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedCycleSchemasBudgetCertificate.controlled
    (c : PointedCycleSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PointedCycleSchemasBudgetCertificate.budgetControlled
    (c : PointedCycleSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PointedCycleSchemasBudgetCertificate.Ready
    (c : PointedCycleSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PointedCycleSchemasBudgetCertificate.size
    (c : PointedCycleSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem pointedCycleSchemas_budgetCertificate_le_size
    (c : PointedCycleSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePointedCycleSchemasBudgetCertificate :
    PointedCycleSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePointedCycleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedCycleSchemasBudgetCertificate.controlled,
      samplePointedCycleSchemasBudgetCertificate]
  · norm_num [PointedCycleSchemasBudgetCertificate.budgetControlled,
      samplePointedCycleSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePointedCycleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedCycleSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePointedCycleSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PointedCycleSchemasBudgetCertificate.controlled,
      samplePointedCycleSchemasBudgetCertificate]
  · norm_num [PointedCycleSchemasBudgetCertificate.budgetControlled,
      samplePointedCycleSchemasBudgetCertificate]

example :
    samplePointedCycleSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePointedCycleSchemasBudgetCertificate.size := by
  apply pointedCycleSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PointedCycleSchemasBudgetCertificate.controlled,
      samplePointedCycleSchemasBudgetCertificate]
  · norm_num [PointedCycleSchemasBudgetCertificate.budgetControlled,
      samplePointedCycleSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PointedCycleSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePointedCycleSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePointedCycleSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.PointedCycleSchemas
