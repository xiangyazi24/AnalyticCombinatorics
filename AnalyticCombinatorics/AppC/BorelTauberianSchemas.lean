import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Borel Tauberian schema bookkeeping.

The finite data records Borel window size, positivity, and remainder budget.
-/

namespace AnalyticCombinatorics.AppC.BorelTauberianSchemas

structure BorelData where
  windowSize : ℕ
  positivityMargin : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def positiveWindow (d : BorelData) : Prop :=
  0 < d.windowSize

def positiveMargin (d : BorelData) : Prop :=
  0 < d.positivityMargin

def borelReady (d : BorelData) : Prop :=
  positiveWindow d ∧ positiveMargin d

def borelBudget (d : BorelData) : ℕ :=
  d.windowSize + d.positivityMargin + d.remainderBudget

theorem borelReady.window {d : BorelData}
    (h : borelReady d) :
    positiveWindow d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem windowSize_le_borelBudget (d : BorelData) :
    d.windowSize ≤ borelBudget d := by
  unfold borelBudget
  omega

def sampleBorel : BorelData :=
  { windowSize := 5, positivityMargin := 2, remainderBudget := 4 }

example : borelReady sampleBorel := by
  norm_num [borelReady, positiveWindow, positiveMargin, sampleBorel]

example : borelBudget sampleBorel = 11 := by
  native_decide

structure BorelWindow where
  windowSize : ℕ
  positivityMargin : ℕ
  transformedMass : ℕ
  remainderBudget : ℕ
deriving DecidableEq, Repr

def BorelWindow.windowReady (w : BorelWindow) : Prop :=
  0 < w.windowSize ∧ 0 < w.positivityMargin

def BorelWindow.remainderControlled (w : BorelWindow) : Prop :=
  w.transformedMass ≤ w.windowSize * w.positivityMargin + w.remainderBudget

def BorelWindow.ready (w : BorelWindow) : Prop :=
  w.windowReady ∧ w.remainderControlled

def BorelWindow.certificate (w : BorelWindow) : ℕ :=
  w.windowSize + w.positivityMargin + w.transformedMass + w.remainderBudget

theorem transformedMass_le_certificate (w : BorelWindow) :
    w.transformedMass ≤ w.certificate := by
  unfold BorelWindow.certificate
  omega

def sampleBorelWindow : BorelWindow :=
  { windowSize := 5, positivityMargin := 2, transformedMass := 9, remainderBudget := 4 }

example : sampleBorelWindow.ready := by
  norm_num [sampleBorelWindow, BorelWindow.ready, BorelWindow.windowReady,
    BorelWindow.remainderControlled]

structure BorelRefinementWindow where
  windowSize : ℕ
  positivityWindow : ℕ
  transformedWindow : ℕ
  borelBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BorelRefinementWindow.transformedControlled
    (w : BorelRefinementWindow) : Prop :=
  w.transformedWindow ≤ w.windowSize * w.positivityWindow + w.slack

def borelRefinementWindowReady (w : BorelRefinementWindow) : Prop :=
  0 < w.windowSize ∧ 0 < w.positivityWindow ∧ w.transformedControlled ∧
    w.borelBudget ≤ w.windowSize + w.transformedWindow + w.slack

def BorelRefinementWindow.certificate (w : BorelRefinementWindow) : ℕ :=
  w.windowSize + w.positivityWindow + w.transformedWindow + w.borelBudget + w.slack

theorem borelRefinement_budget_le_certificate
    (w : BorelRefinementWindow) :
    w.borelBudget ≤ w.certificate := by
  unfold BorelRefinementWindow.certificate
  omega

def sampleBorelRefinementWindow : BorelRefinementWindow :=
  { windowSize := 5, positivityWindow := 2, transformedWindow := 9,
    borelBudget := 14, slack := 1 }

example : borelRefinementWindowReady sampleBorelRefinementWindow := by
  norm_num [borelRefinementWindowReady,
    BorelRefinementWindow.transformedControlled, sampleBorelRefinementWindow]


structure BorelTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BorelTauberianSchemasBudgetCertificate.controlled
    (c : BorelTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BorelTauberianSchemasBudgetCertificate.budgetControlled
    (c : BorelTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BorelTauberianSchemasBudgetCertificate.Ready
    (c : BorelTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BorelTauberianSchemasBudgetCertificate.size
    (c : BorelTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem borelTauberianSchemas_budgetCertificate_le_size
    (c : BorelTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBorelTauberianSchemasBudgetCertificate :
    BorelTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBorelTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BorelTauberianSchemasBudgetCertificate.controlled,
      sampleBorelTauberianSchemasBudgetCertificate]
  · norm_num [BorelTauberianSchemasBudgetCertificate.budgetControlled,
      sampleBorelTauberianSchemasBudgetCertificate]

example :
    sampleBorelTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBorelTauberianSchemasBudgetCertificate.size := by
  apply borelTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BorelTauberianSchemasBudgetCertificate.controlled,
      sampleBorelTauberianSchemasBudgetCertificate]
  · norm_num [BorelTauberianSchemasBudgetCertificate.budgetControlled,
      sampleBorelTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBorelTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BorelTauberianSchemasBudgetCertificate.controlled,
      sampleBorelTauberianSchemasBudgetCertificate]
  · norm_num [BorelTauberianSchemasBudgetCertificate.budgetControlled,
      sampleBorelTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBorelTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBorelTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BorelTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBorelTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBorelTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BorelTauberianSchemas
