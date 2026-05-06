import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Logarithmic transfer windows.

The finite record stores logarithmic power, transfer radius, and
remainder slack.
-/

namespace AnalyticCombinatorics.Asymptotics.LogarithmicTransferWindows

structure LogarithmicTransferWindowData where
  logPower : ℕ
  transferRadius : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def transferRadiusPositive (d : LogarithmicTransferWindowData) : Prop :=
  0 < d.transferRadius

def logPowerControlled (d : LogarithmicTransferWindowData) : Prop :=
  d.logPower ≤ d.transferRadius + d.remainderSlack

def logarithmicTransferWindowReady
    (d : LogarithmicTransferWindowData) : Prop :=
  transferRadiusPositive d ∧ logPowerControlled d

def logarithmicTransferWindowBudget
    (d : LogarithmicTransferWindowData) : ℕ :=
  d.logPower + d.transferRadius + d.remainderSlack

theorem logarithmicTransferWindowReady.radius
    {d : LogarithmicTransferWindowData}
    (h : logarithmicTransferWindowReady d) :
    transferRadiusPositive d ∧ logPowerControlled d ∧
      d.logPower ≤ logarithmicTransferWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold logarithmicTransferWindowBudget
  omega

theorem logPower_le_logTransferBudget
    (d : LogarithmicTransferWindowData) :
    d.logPower ≤ logarithmicTransferWindowBudget d := by
  unfold logarithmicTransferWindowBudget
  omega

def sampleLogarithmicTransferWindowData :
    LogarithmicTransferWindowData :=
  { logPower := 6, transferRadius := 4, remainderSlack := 3 }

example :
    logarithmicTransferWindowReady sampleLogarithmicTransferWindowData := by
  norm_num [logarithmicTransferWindowReady, transferRadiusPositive]
  norm_num [logPowerControlled, sampleLogarithmicTransferWindowData]

example :
    logarithmicTransferWindowBudget sampleLogarithmicTransferWindowData = 13 := by
  native_decide

/-- Finite executable readiness audit for logarithmic transfer window data. -/
def logarithmicTransferWindowDataListReady
    (data : List LogarithmicTransferWindowData) : Bool :=
  data.all fun d =>
    0 < d.transferRadius && d.logPower ≤ d.transferRadius + d.remainderSlack

theorem logarithmicTransferWindowDataList_readyWindow :
    logarithmicTransferWindowDataListReady
      [{ logPower := 3, transferRadius := 4, remainderSlack := 0 },
       { logPower := 6, transferRadius := 4, remainderSlack := 3 }] = true := by
  unfold logarithmicTransferWindowDataListReady
  native_decide

/-- A certificate window for logarithmic transfer estimates. -/
structure LogarithmicTransferCertificateWindow where
  logWindow : ℕ
  radiusWindow : ℕ
  remainderSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The logarithmic power is controlled by radius and remainder slack. -/
def logarithmicTransferCertificateControlled
    (w : LogarithmicTransferCertificateWindow) : Prop :=
  w.logWindow ≤ w.radiusWindow + w.remainderSlack + w.slack

/-- Readiness for a logarithmic transfer certificate. -/
def logarithmicTransferCertificateReady
    (w : LogarithmicTransferCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    logarithmicTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.logWindow + w.radiusWindow + w.slack

/-- Total size of a logarithmic transfer certificate. -/
def logarithmicTransferCertificate
    (w : LogarithmicTransferCertificateWindow) : ℕ :=
  w.logWindow + w.radiusWindow + w.remainderSlack + w.certificateBudget + w.slack

theorem logarithmicTransferCertificate_budget_le_certificate
    (w : LogarithmicTransferCertificateWindow)
    (h : logarithmicTransferCertificateReady w) :
    w.certificateBudget ≤ logarithmicTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold logarithmicTransferCertificate
  omega

def sampleLogarithmicTransferCertificateWindow :
    LogarithmicTransferCertificateWindow where
  logWindow := 5
  radiusWindow := 6
  remainderSlack := 2
  certificateBudget := 10
  slack := 1

example :
    logarithmicTransferCertificateReady
      sampleLogarithmicTransferCertificateWindow := by
  norm_num [logarithmicTransferCertificateReady,
    logarithmicTransferCertificateControlled,
    sampleLogarithmicTransferCertificateWindow]

example :
    sampleLogarithmicTransferCertificateWindow.certificateBudget ≤
      logarithmicTransferCertificate
        sampleLogarithmicTransferCertificateWindow := by
  apply logarithmicTransferCertificate_budget_le_certificate
  norm_num [logarithmicTransferCertificateReady,
    logarithmicTransferCertificateControlled,
    sampleLogarithmicTransferCertificateWindow]

structure LogarithmicTransferRefinementCertificate where
  logWindow : ℕ
  radiusWindow : ℕ
  remainderSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicTransferRefinementCertificate.logControlled
    (c : LogarithmicTransferRefinementCertificate) : Prop :=
  c.logWindow ≤ c.radiusWindow + c.remainderSlackWindow + c.slack

def LogarithmicTransferRefinementCertificate.certificateBudgetControlled
    (c : LogarithmicTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.logWindow + c.radiusWindow + c.remainderSlackWindow + c.slack

def logarithmicTransferRefinementReady
    (c : LogarithmicTransferRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.logControlled ∧ c.certificateBudgetControlled

def LogarithmicTransferRefinementCertificate.size
    (c : LogarithmicTransferRefinementCertificate) : ℕ :=
  c.logWindow + c.radiusWindow + c.remainderSlackWindow + c.slack

theorem logarithmicTransfer_certificateBudgetWindow_le_size
    {c : LogarithmicTransferRefinementCertificate}
    (h : logarithmicTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleLogarithmicTransferRefinementCertificate :
    LogarithmicTransferRefinementCertificate :=
  { logWindow := 5, radiusWindow := 6, remainderSlackWindow := 2,
    certificateBudgetWindow := 14, slack := 1 }

example : logarithmicTransferRefinementReady
    sampleLogarithmicTransferRefinementCertificate := by
  norm_num [logarithmicTransferRefinementReady,
    LogarithmicTransferRefinementCertificate.logControlled,
    LogarithmicTransferRefinementCertificate.certificateBudgetControlled,
    sampleLogarithmicTransferRefinementCertificate]

example :
    sampleLogarithmicTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleLogarithmicTransferRefinementCertificate.size := by
  norm_num [LogarithmicTransferRefinementCertificate.size,
    sampleLogarithmicTransferRefinementCertificate]

structure LogarithmicTransferBudgetCertificate where
  logWindow : ℕ
  radiusWindow : ℕ
  remainderSlackWindow : ℕ
  logBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LogarithmicTransferBudgetCertificate.controlled
    (c : LogarithmicTransferBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.logWindow ≤ c.radiusWindow + c.remainderSlackWindow + c.slack ∧
      c.logBudgetWindow ≤
        c.logWindow + c.radiusWindow + c.remainderSlackWindow + c.slack

def LogarithmicTransferBudgetCertificate.budgetControlled
    (c : LogarithmicTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.logWindow + c.radiusWindow + c.remainderSlackWindow +
      c.logBudgetWindow + c.slack

def LogarithmicTransferBudgetCertificate.Ready
    (c : LogarithmicTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LogarithmicTransferBudgetCertificate.size
    (c : LogarithmicTransferBudgetCertificate) : ℕ :=
  c.logWindow + c.radiusWindow + c.remainderSlackWindow +
    c.logBudgetWindow + c.slack

theorem logarithmicTransfer_budgetCertificate_le_size
    (c : LogarithmicTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLogarithmicTransferBudgetCertificate :
    LogarithmicTransferBudgetCertificate :=
  { logWindow := 5
    radiusWindow := 6
    remainderSlackWindow := 2
    logBudgetWindow := 14
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleLogarithmicTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicTransferBudgetCertificate.controlled,
      sampleLogarithmicTransferBudgetCertificate]
  · norm_num [LogarithmicTransferBudgetCertificate.budgetControlled,
      sampleLogarithmicTransferBudgetCertificate]

example :
    sampleLogarithmicTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicTransferBudgetCertificate.size := by
  apply logarithmicTransfer_budgetCertificate_le_size
  constructor
  · norm_num [LogarithmicTransferBudgetCertificate.controlled,
      sampleLogarithmicTransferBudgetCertificate]
  · norm_num [LogarithmicTransferBudgetCertificate.budgetControlled,
      sampleLogarithmicTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLogarithmicTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [LogarithmicTransferBudgetCertificate.controlled,
      sampleLogarithmicTransferBudgetCertificate]
  · norm_num [LogarithmicTransferBudgetCertificate.budgetControlled,
      sampleLogarithmicTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLogarithmicTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLogarithmicTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LogarithmicTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLogarithmicTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLogarithmicTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.LogarithmicTransferWindows
