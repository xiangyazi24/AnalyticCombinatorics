import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic Robin boundary models.

This module records finite bookkeeping for Robin boundary windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticRobinBoundaryModels

structure RobinBoundaryData where
  boundaryPatches : ℕ
  mixedWindow : ℕ
  robinSlack : ℕ
deriving DecidableEq, Repr

def hasBoundaryPatches (d : RobinBoundaryData) : Prop :=
  0 < d.boundaryPatches

def mixedWindowControlled (d : RobinBoundaryData) : Prop :=
  d.mixedWindow ≤ d.boundaryPatches + d.robinSlack

def robinBoundaryReady (d : RobinBoundaryData) : Prop :=
  hasBoundaryPatches d ∧ mixedWindowControlled d

def robinBoundaryBudget (d : RobinBoundaryData) : ℕ :=
  d.boundaryPatches + d.mixedWindow + d.robinSlack

theorem robinBoundaryReady.hasBoundaryPatches {d : RobinBoundaryData}
    (h : robinBoundaryReady d) :
    hasBoundaryPatches d ∧ mixedWindowControlled d ∧
      d.mixedWindow ≤ robinBoundaryBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold robinBoundaryBudget
  omega

theorem mixedWindow_le_budget (d : RobinBoundaryData) :
    d.mixedWindow ≤ robinBoundaryBudget d := by
  unfold robinBoundaryBudget
  omega

def sampleRobinBoundaryData : RobinBoundaryData :=
  { boundaryPatches := 6, mixedWindow := 8, robinSlack := 3 }

example : robinBoundaryReady sampleRobinBoundaryData := by
  norm_num [robinBoundaryReady, hasBoundaryPatches]
  norm_num [mixedWindowControlled, sampleRobinBoundaryData]

example : robinBoundaryBudget sampleRobinBoundaryData = 17 := by
  native_decide

structure RobinBoundaryWindow where
  boundaryWindow : ℕ
  mixedWindow : ℕ
  robinSlack : ℕ
  mixedBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RobinBoundaryWindow.mixedControlled (w : RobinBoundaryWindow) : Prop :=
  w.mixedWindow ≤ w.boundaryWindow + w.robinSlack + w.slack

def robinBoundaryWindowReady (w : RobinBoundaryWindow) : Prop :=
  0 < w.boundaryWindow ∧ w.mixedControlled ∧
    w.mixedBudget ≤ w.boundaryWindow + w.mixedWindow + w.slack

def RobinBoundaryWindow.certificate (w : RobinBoundaryWindow) : ℕ :=
  w.boundaryWindow + w.mixedWindow + w.robinSlack + w.mixedBudget + w.slack

theorem robinBoundary_mixedBudget_le_certificate (w : RobinBoundaryWindow) :
    w.mixedBudget ≤ w.certificate := by
  unfold RobinBoundaryWindow.certificate
  omega

def sampleRobinBoundaryWindow : RobinBoundaryWindow :=
  { boundaryWindow := 5, mixedWindow := 7, robinSlack := 2, mixedBudget := 14, slack := 2 }

example : robinBoundaryWindowReady sampleRobinBoundaryWindow := by
  norm_num [robinBoundaryWindowReady, RobinBoundaryWindow.mixedControlled,
    sampleRobinBoundaryWindow]


structure AnalyticRobinBoundaryModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticRobinBoundaryModelsBudgetCertificate.controlled
    (c : AnalyticRobinBoundaryModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticRobinBoundaryModelsBudgetCertificate.budgetControlled
    (c : AnalyticRobinBoundaryModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticRobinBoundaryModelsBudgetCertificate.Ready
    (c : AnalyticRobinBoundaryModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticRobinBoundaryModelsBudgetCertificate.size
    (c : AnalyticRobinBoundaryModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticRobinBoundaryModels_budgetCertificate_le_size
    (c : AnalyticRobinBoundaryModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticRobinBoundaryModelsBudgetCertificate :
    AnalyticRobinBoundaryModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticRobinBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticRobinBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticRobinBoundaryModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticRobinBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]

example :
    sampleAnalyticRobinBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticRobinBoundaryModelsBudgetCertificate.size := by
  apply analyticRobinBoundaryModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticRobinBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticRobinBoundaryModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticRobinBoundaryModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticRobinBoundaryModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticRobinBoundaryModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticRobinBoundaryModels
