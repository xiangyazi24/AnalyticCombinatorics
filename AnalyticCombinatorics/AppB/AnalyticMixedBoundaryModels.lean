import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic mixed boundary models.

This module records finite bookkeeping for mixed boundary windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticMixedBoundaryModels

structure MixedBoundaryData where
  boundaryComponents : ℕ
  mixedWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasBoundaryComponents (d : MixedBoundaryData) : Prop :=
  0 < d.boundaryComponents

def mixedWindowControlled (d : MixedBoundaryData) : Prop :=
  d.mixedWindow ≤ d.boundaryComponents + d.boundarySlack

def mixedBoundaryReady (d : MixedBoundaryData) : Prop :=
  hasBoundaryComponents d ∧ mixedWindowControlled d

def mixedBoundaryBudget (d : MixedBoundaryData) : ℕ :=
  d.boundaryComponents + d.mixedWindow + d.boundarySlack

theorem mixedBoundaryReady.hasBoundaryComponents {d : MixedBoundaryData}
    (h : mixedBoundaryReady d) :
    hasBoundaryComponents d ∧ mixedWindowControlled d ∧
      d.mixedWindow ≤ mixedBoundaryBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold mixedBoundaryBudget
  omega

theorem mixedWindow_le_budget (d : MixedBoundaryData) :
    d.mixedWindow ≤ mixedBoundaryBudget d := by
  unfold mixedBoundaryBudget
  omega

def sampleMixedBoundaryData : MixedBoundaryData :=
  { boundaryComponents := 6, mixedWindow := 8, boundarySlack := 3 }

example : mixedBoundaryReady sampleMixedBoundaryData := by
  norm_num [mixedBoundaryReady, hasBoundaryComponents]
  norm_num [mixedWindowControlled, sampleMixedBoundaryData]

example : mixedBoundaryBudget sampleMixedBoundaryData = 17 := by
  native_decide

structure MixedBoundaryWindow where
  componentWindow : ℕ
  mixedWindow : ℕ
  boundarySlack : ℕ
  mixedBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MixedBoundaryWindow.mixedControlled (w : MixedBoundaryWindow) : Prop :=
  w.mixedWindow ≤ w.componentWindow + w.boundarySlack + w.slack

def mixedBoundaryWindowReady (w : MixedBoundaryWindow) : Prop :=
  0 < w.componentWindow ∧ w.mixedControlled ∧
    w.mixedBudget ≤ w.componentWindow + w.mixedWindow + w.slack

def MixedBoundaryWindow.certificate (w : MixedBoundaryWindow) : ℕ :=
  w.componentWindow + w.mixedWindow + w.boundarySlack + w.mixedBudget + w.slack

theorem mixedBoundary_mixedBudget_le_certificate (w : MixedBoundaryWindow) :
    w.mixedBudget ≤ w.certificate := by
  unfold MixedBoundaryWindow.certificate
  omega

def sampleMixedBoundaryWindow : MixedBoundaryWindow :=
  { componentWindow := 5, mixedWindow := 7, boundarySlack := 2, mixedBudget := 14, slack := 2 }

example : mixedBoundaryWindowReady sampleMixedBoundaryWindow := by
  norm_num [mixedBoundaryWindowReady, MixedBoundaryWindow.mixedControlled,
    sampleMixedBoundaryWindow]


structure AnalyticMixedBoundaryModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticMixedBoundaryModelsBudgetCertificate.controlled
    (c : AnalyticMixedBoundaryModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticMixedBoundaryModelsBudgetCertificate.budgetControlled
    (c : AnalyticMixedBoundaryModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticMixedBoundaryModelsBudgetCertificate.Ready
    (c : AnalyticMixedBoundaryModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticMixedBoundaryModelsBudgetCertificate.size
    (c : AnalyticMixedBoundaryModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticMixedBoundaryModels_budgetCertificate_le_size
    (c : AnalyticMixedBoundaryModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticMixedBoundaryModelsBudgetCertificate :
    AnalyticMixedBoundaryModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticMixedBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticMixedBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMixedBoundaryModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticMixedBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]

example :
    sampleAnalyticMixedBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticMixedBoundaryModelsBudgetCertificate.size := by
  apply analyticMixedBoundaryModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticMixedBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticMixedBoundaryModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticMixedBoundaryModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticMixedBoundaryModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticMixedBoundaryModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticMixedBoundaryModels
