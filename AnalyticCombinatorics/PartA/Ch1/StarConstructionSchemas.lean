import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Star construction schemas.

The finite record tracks atom weights, repetition budgets, and a guard
used for symbolic star constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.StarConstructionSchemas

structure StarConstructionData where
  atomWeight : ℕ
  repetitionBudget : ℕ
  guard : ℕ
deriving DecidableEq, Repr

def positiveAtomWeight (d : StarConstructionData) : Prop :=
  0 < d.atomWeight

def repetitionControlled (d : StarConstructionData) : Prop :=
  d.repetitionBudget ≤ d.atomWeight + d.guard

def starConstructionReady (d : StarConstructionData) : Prop :=
  positiveAtomWeight d ∧ repetitionControlled d

def starConstructionBudget (d : StarConstructionData) : ℕ :=
  d.atomWeight + d.repetitionBudget + d.guard

theorem starConstructionReady.atom {d : StarConstructionData}
    (h : starConstructionReady d) :
    positiveAtomWeight d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem atomWeight_le_starBudget (d : StarConstructionData) :
    d.atomWeight ≤ starConstructionBudget d := by
  unfold starConstructionBudget
  omega

def sampleStarConstructionData : StarConstructionData :=
  { atomWeight := 4, repetitionBudget := 6, guard := 3 }

example : starConstructionReady sampleStarConstructionData := by
  norm_num [starConstructionReady, positiveAtomWeight]
  norm_num [repetitionControlled, sampleStarConstructionData]

example : starConstructionBudget sampleStarConstructionData = 13 := by
  native_decide

structure StarConstructionWindow where
  atomWeight : ℕ
  repetitionBudget : ℕ
  guard : ℕ
  closureBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StarConstructionWindow.repetitionControlled (w : StarConstructionWindow) : Prop :=
  w.repetitionBudget ≤ w.atomWeight + w.guard + w.slack

def StarConstructionWindow.closureControlled (w : StarConstructionWindow) : Prop :=
  w.closureBudget ≤ w.atomWeight + w.repetitionBudget + w.guard + w.slack

def starConstructionWindowReady (w : StarConstructionWindow) : Prop :=
  0 < w.atomWeight ∧
    w.repetitionControlled ∧
    w.closureControlled

def StarConstructionWindow.certificate (w : StarConstructionWindow) : ℕ :=
  w.atomWeight + w.repetitionBudget + w.guard + w.slack

theorem starConstruction_closureBudget_le_certificate {w : StarConstructionWindow}
    (h : starConstructionWindowReady w) :
    w.closureBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hclosure⟩
  exact hclosure

def sampleStarConstructionWindow : StarConstructionWindow :=
  { atomWeight := 4, repetitionBudget := 6, guard := 3, closureBudget := 12, slack := 0 }

example : starConstructionWindowReady sampleStarConstructionWindow := by
  norm_num [starConstructionWindowReady, StarConstructionWindow.repetitionControlled,
    StarConstructionWindow.closureControlled, sampleStarConstructionWindow]

example : sampleStarConstructionWindow.certificate = 13 := by
  native_decide


structure StarConstructionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StarConstructionSchemasBudgetCertificate.controlled
    (c : StarConstructionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StarConstructionSchemasBudgetCertificate.budgetControlled
    (c : StarConstructionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StarConstructionSchemasBudgetCertificate.Ready
    (c : StarConstructionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StarConstructionSchemasBudgetCertificate.size
    (c : StarConstructionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem starConstructionSchemas_budgetCertificate_le_size
    (c : StarConstructionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStarConstructionSchemasBudgetCertificate :
    StarConstructionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStarConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StarConstructionSchemasBudgetCertificate.controlled,
      sampleStarConstructionSchemasBudgetCertificate]
  · norm_num [StarConstructionSchemasBudgetCertificate.budgetControlled,
      sampleStarConstructionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStarConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStarConstructionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleStarConstructionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StarConstructionSchemasBudgetCertificate.controlled,
      sampleStarConstructionSchemasBudgetCertificate]
  · norm_num [StarConstructionSchemasBudgetCertificate.budgetControlled,
      sampleStarConstructionSchemasBudgetCertificate]

example :
    sampleStarConstructionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStarConstructionSchemasBudgetCertificate.size := by
  apply starConstructionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StarConstructionSchemasBudgetCertificate.controlled,
      sampleStarConstructionSchemasBudgetCertificate]
  · norm_num [StarConstructionSchemasBudgetCertificate.budgetControlled,
      sampleStarConstructionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List StarConstructionSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStarConstructionSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStarConstructionSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.StarConstructionSchemas
