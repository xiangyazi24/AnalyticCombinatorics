import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic monodromy models.

This module records finite bookkeeping for monodromy windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticMonodromyModels

structure MonodromyData where
  loopCount : ℕ
  branchTransitions : ℕ
  monodromySlack : ℕ
deriving DecidableEq, Repr

def hasLoopCount (d : MonodromyData) : Prop :=
  0 < d.loopCount

def branchTransitionsControlled (d : MonodromyData) : Prop :=
  d.branchTransitions ≤ d.loopCount + d.monodromySlack

def monodromyReady (d : MonodromyData) : Prop :=
  hasLoopCount d ∧ branchTransitionsControlled d

def monodromyBudget (d : MonodromyData) : ℕ :=
  d.loopCount + d.branchTransitions + d.monodromySlack

theorem monodromyReady.hasLoopCount {d : MonodromyData}
    (h : monodromyReady d) :
    hasLoopCount d ∧ branchTransitionsControlled d ∧
      d.branchTransitions ≤ monodromyBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold monodromyBudget
  omega

theorem branchTransitions_le_budget (d : MonodromyData) :
    d.branchTransitions ≤ monodromyBudget d := by
  unfold monodromyBudget
  omega

def sampleMonodromyData : MonodromyData :=
  { loopCount := 6, branchTransitions := 8, monodromySlack := 3 }

example : monodromyReady sampleMonodromyData := by
  norm_num [monodromyReady, hasLoopCount]
  norm_num [branchTransitionsControlled, sampleMonodromyData]

example : monodromyBudget sampleMonodromyData = 17 := by
  native_decide

structure MonodromyWindow where
  loopWindow : ℕ
  transitionWindow : ℕ
  monodromySlack : ℕ
  branchBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MonodromyWindow.transitionsControlled (w : MonodromyWindow) : Prop :=
  w.transitionWindow ≤ w.loopWindow + w.monodromySlack + w.slack

def monodromyWindowReady (w : MonodromyWindow) : Prop :=
  0 < w.loopWindow ∧ w.transitionsControlled ∧
    w.branchBudget ≤ w.loopWindow + w.transitionWindow + w.slack

def MonodromyWindow.certificate (w : MonodromyWindow) : ℕ :=
  w.loopWindow + w.transitionWindow + w.monodromySlack + w.branchBudget + w.slack

theorem monodromy_branchBudget_le_certificate (w : MonodromyWindow) :
    w.branchBudget ≤ w.certificate := by
  unfold MonodromyWindow.certificate
  omega

def sampleMonodromyWindow : MonodromyWindow :=
  { loopWindow := 5, transitionWindow := 7, monodromySlack := 2, branchBudget := 14, slack := 2 }

example : monodromyWindowReady sampleMonodromyWindow := by
  norm_num [monodromyWindowReady, MonodromyWindow.transitionsControlled, sampleMonodromyWindow]


structure AnalyticMonodromyModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticMonodromyModelsBudgetCertificate.controlled
    (c : AnalyticMonodromyModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticMonodromyModelsBudgetCertificate.budgetControlled
    (c : AnalyticMonodromyModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticMonodromyModelsBudgetCertificate.Ready
    (c : AnalyticMonodromyModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticMonodromyModelsBudgetCertificate.size
    (c : AnalyticMonodromyModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticMonodromyModels_budgetCertificate_le_size
    (c : AnalyticMonodromyModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticMonodromyModelsBudgetCertificate :
    AnalyticMonodromyModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticMonodromyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.controlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticMonodromyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMonodromyModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticMonodromyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.controlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]

example :
    sampleAnalyticMonodromyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMonodromyModelsBudgetCertificate.size := by
  apply analyticMonodromyModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.controlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]
  · norm_num [AnalyticMonodromyModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMonodromyModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticMonodromyModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticMonodromyModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticMonodromyModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticMonodromyModels
