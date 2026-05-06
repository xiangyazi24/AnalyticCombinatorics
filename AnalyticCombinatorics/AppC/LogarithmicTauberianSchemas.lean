import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Logarithmic Tauberian schema bookkeeping.

The file stores finite log-scale, monotonicity, and remainder budgets used
by logarithmic Tauberian estimates.
-/

namespace AnalyticCombinatorics.AppC.LogarithmicTauberianSchemas

structure LogTauberianData where
  logScale : ℕ
  monotoneRemainder : Prop
  remainderBudget : ℕ
deriving Repr

def positiveLogScale (d : LogTauberianData) : Prop :=
  0 < d.logScale

def logarithmicTauberianReady (d : LogTauberianData) : Prop :=
  positiveLogScale d ∧ d.monotoneRemainder

def logRemainderScale (d : LogTauberianData) : ℕ :=
  d.logScale + d.remainderBudget

theorem logarithmicTauberianReady.scale {d : LogTauberianData}
    (h : logarithmicTauberianReady d) :
    positiveLogScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem logScale_le_remainderScale (d : LogTauberianData) :
    d.logScale ≤ logRemainderScale d := by
  unfold logRemainderScale
  omega

def sampleLogTauberian : LogTauberianData :=
  { logScale := 5, monotoneRemainder := 2 ≤ 5, remainderBudget := 2 }

example : logarithmicTauberianReady sampleLogTauberian := by
  norm_num [logarithmicTauberianReady, positiveLogScale, sampleLogTauberian]

example : logRemainderScale sampleLogTauberian = 7 := by
  native_decide

structure LogarithmicTauberianWindow where
  logScale : ℕ
  coefficientMass : ℕ
  remainderMass : ℕ
  tauberianSlack : ℕ
deriving DecidableEq, Repr

def LogarithmicTauberianWindow.scaleReady (w : LogarithmicTauberianWindow) : Prop :=
  0 < w.logScale

def LogarithmicTauberianWindow.remainderControlled (w : LogarithmicTauberianWindow) : Prop :=
  w.remainderMass ≤ w.logScale + w.tauberianSlack

def LogarithmicTauberianWindow.coefficientControlled (w : LogarithmicTauberianWindow) : Prop :=
  w.coefficientMass ≤ w.logScale * (w.remainderMass + 1) + w.tauberianSlack

def LogarithmicTauberianWindow.ready (w : LogarithmicTauberianWindow) : Prop :=
  w.scaleReady ∧ w.remainderControlled ∧ w.coefficientControlled

def LogarithmicTauberianWindow.certificate (w : LogarithmicTauberianWindow) : ℕ :=
  w.logScale + w.coefficientMass + w.remainderMass + w.tauberianSlack

theorem coefficientMass_le_certificate (w : LogarithmicTauberianWindow) :
    w.coefficientMass ≤ w.certificate := by
  unfold LogarithmicTauberianWindow.certificate
  omega

def sampleLogarithmicTauberianWindow : LogarithmicTauberianWindow :=
  { logScale := 5, coefficientMass := 12, remainderMass := 2, tauberianSlack := 0 }

example : sampleLogarithmicTauberianWindow.ready := by
  norm_num [sampleLogarithmicTauberianWindow, LogarithmicTauberianWindow.ready,
    LogarithmicTauberianWindow.scaleReady, LogarithmicTauberianWindow.remainderControlled,
    LogarithmicTauberianWindow.coefficientControlled]

structure LogarithmicTauberianRefinementWindow where
  logWindow : ℕ
  coefficientWindow : ℕ
  remainderWindow : ℕ
  logarithmicBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicTauberianRefinementWindow.coefficientControlled
    (w : LogarithmicTauberianRefinementWindow) : Prop :=
  w.coefficientWindow ≤ w.logWindow * (w.remainderWindow + 1) + w.slack

def logarithmicTauberianRefinementWindowReady
    (w : LogarithmicTauberianRefinementWindow) : Prop :=
  0 < w.logWindow ∧ w.coefficientControlled ∧
    w.logarithmicBudget ≤ w.logWindow + w.coefficientWindow + w.remainderWindow + w.slack

def LogarithmicTauberianRefinementWindow.certificate
    (w : LogarithmicTauberianRefinementWindow) : ℕ :=
  w.logWindow + w.coefficientWindow + w.remainderWindow + w.logarithmicBudget + w.slack

theorem logarithmicTauberianRefinement_budget_le_certificate
    (w : LogarithmicTauberianRefinementWindow) :
    w.logarithmicBudget ≤ w.certificate := by
  unfold LogarithmicTauberianRefinementWindow.certificate
  omega

def sampleLogarithmicTauberianRefinementWindow :
    LogarithmicTauberianRefinementWindow :=
  { logWindow := 5, coefficientWindow := 12, remainderWindow := 2,
    logarithmicBudget := 20, slack := 1 }

example : logarithmicTauberianRefinementWindowReady
    sampleLogarithmicTauberianRefinementWindow := by
  norm_num [logarithmicTauberianRefinementWindowReady,
    LogarithmicTauberianRefinementWindow.coefficientControlled,
    sampleLogarithmicTauberianRefinementWindow]


structure LogarithmicTauberianSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicTauberianSchemasBudgetCertificate.controlled
    (c : LogarithmicTauberianSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LogarithmicTauberianSchemasBudgetCertificate.budgetControlled
    (c : LogarithmicTauberianSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LogarithmicTauberianSchemasBudgetCertificate.Ready
    (c : LogarithmicTauberianSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicTauberianSchemasBudgetCertificate.size
    (c : LogarithmicTauberianSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem logarithmicTauberianSchemas_budgetCertificate_le_size
    (c : LogarithmicTauberianSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicTauberianSchemasBudgetCertificate :
    LogarithmicTauberianSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLogarithmicTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.controlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]

example :
    sampleLogarithmicTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicTauberianSchemasBudgetCertificate.size := by
  apply logarithmicTauberianSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.controlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogarithmicTauberianSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.controlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]
  · norm_num [LogarithmicTauberianSchemasBudgetCertificate.budgetControlled,
      sampleLogarithmicTauberianSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicTauberianSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicTauberianSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List LogarithmicTauberianSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicTauberianSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleLogarithmicTauberianSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.LogarithmicTauberianSchemas
