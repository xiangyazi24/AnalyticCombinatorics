import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Concentration compactness schema bookkeeping.

The finite data records compact mass, escaping mass, and splitting budget.
-/

namespace AnalyticCombinatorics.AppC.ConcentrationCompactnessSchemas

structure ConcentrationData where
  compactMass : ℕ
  escapingMass : ℕ
  splittingBudget : ℕ
deriving DecidableEq, Repr

def massControlled (d : ConcentrationData) : Prop :=
  d.escapingMass ≤ d.compactMass + d.splittingBudget

def nonzeroCompactMass (d : ConcentrationData) : Prop :=
  0 < d.compactMass

def concentrationCompactnessReady (d : ConcentrationData) : Prop :=
  nonzeroCompactMass d ∧ massControlled d

def concentrationBudget (d : ConcentrationData) : ℕ :=
  d.compactMass + d.escapingMass + d.splittingBudget

theorem concentrationCompactnessReady.mass {d : ConcentrationData}
    (h : concentrationCompactnessReady d) :
    massControlled d := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem compactMass_le_concentrationBudget (d : ConcentrationData) :
    d.compactMass ≤ concentrationBudget d := by
  unfold concentrationBudget
  omega

def sampleConcentration : ConcentrationData :=
  { compactMass := 8, escapingMass := 3, splittingBudget := 2 }

example : concentrationCompactnessReady sampleConcentration := by
  norm_num [concentrationCompactnessReady, nonzeroCompactMass, massControlled, sampleConcentration]

example : concentrationBudget sampleConcentration = 13 := by
  native_decide

structure ConcentrationWindow where
  compactMass : ℕ
  escapingMass : ℕ
  splittingMass : ℕ
  concentrationSlack : ℕ
deriving DecidableEq, Repr

def ConcentrationWindow.compactReady (w : ConcentrationWindow) : Prop :=
  0 < w.compactMass

def ConcentrationWindow.escapeControlled (w : ConcentrationWindow) : Prop :=
  w.escapingMass ≤ w.compactMass + w.splittingMass + w.concentrationSlack

def ConcentrationWindow.ready (w : ConcentrationWindow) : Prop :=
  w.compactReady ∧ w.escapeControlled

def ConcentrationWindow.certificate (w : ConcentrationWindow) : ℕ :=
  w.compactMass + w.escapingMass + w.splittingMass + w.concentrationSlack

theorem escapingMass_le_certificate (w : ConcentrationWindow) :
    w.escapingMass ≤ w.certificate := by
  unfold ConcentrationWindow.certificate
  omega

def sampleConcentrationWindow : ConcentrationWindow :=
  { compactMass := 8, escapingMass := 3, splittingMass := 2, concentrationSlack := 0 }

example : sampleConcentrationWindow.ready := by
  norm_num [sampleConcentrationWindow, ConcentrationWindow.ready,
    ConcentrationWindow.compactReady, ConcentrationWindow.escapeControlled]

structure ConcentrationRefinementWindow where
  compactWindow : ℕ
  escapingWindow : ℕ
  splittingWindow : ℕ
  concentrationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConcentrationRefinementWindow.escapeControlled
    (w : ConcentrationRefinementWindow) : Prop :=
  w.escapingWindow ≤ w.compactWindow + w.splittingWindow + w.slack

def concentrationRefinementWindowReady
    (w : ConcentrationRefinementWindow) : Prop :=
  0 < w.compactWindow ∧ w.escapeControlled ∧
    w.concentrationBudget ≤ w.compactWindow + w.escapingWindow + w.splittingWindow + w.slack

def ConcentrationRefinementWindow.certificate
    (w : ConcentrationRefinementWindow) : ℕ :=
  w.compactWindow + w.escapingWindow + w.splittingWindow + w.concentrationBudget + w.slack

theorem concentrationRefinement_budget_le_certificate
    (w : ConcentrationRefinementWindow) :
    w.concentrationBudget ≤ w.certificate := by
  unfold ConcentrationRefinementWindow.certificate
  omega

def sampleConcentrationRefinementWindow : ConcentrationRefinementWindow :=
  { compactWindow := 8, escapingWindow := 3, splittingWindow := 2,
    concentrationBudget := 14, slack := 1 }

example : concentrationRefinementWindowReady
    sampleConcentrationRefinementWindow := by
  norm_num [concentrationRefinementWindowReady,
    ConcentrationRefinementWindow.escapeControlled, sampleConcentrationRefinementWindow]


structure ConcentrationCompactnessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConcentrationCompactnessSchemasBudgetCertificate.controlled
    (c : ConcentrationCompactnessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConcentrationCompactnessSchemasBudgetCertificate.budgetControlled
    (c : ConcentrationCompactnessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConcentrationCompactnessSchemasBudgetCertificate.Ready
    (c : ConcentrationCompactnessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConcentrationCompactnessSchemasBudgetCertificate.size
    (c : ConcentrationCompactnessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem concentrationCompactnessSchemas_budgetCertificate_le_size
    (c : ConcentrationCompactnessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConcentrationCompactnessSchemasBudgetCertificate :
    ConcentrationCompactnessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleConcentrationCompactnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.controlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.budgetControlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]

example :
    sampleConcentrationCompactnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConcentrationCompactnessSchemasBudgetCertificate.size := by
  apply concentrationCompactnessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.controlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.budgetControlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleConcentrationCompactnessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.controlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]
  · norm_num [ConcentrationCompactnessSchemasBudgetCertificate.budgetControlled,
      sampleConcentrationCompactnessSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConcentrationCompactnessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConcentrationCompactnessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ConcentrationCompactnessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConcentrationCompactnessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConcentrationCompactnessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ConcentrationCompactnessSchemas
