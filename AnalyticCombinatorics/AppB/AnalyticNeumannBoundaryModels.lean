import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic Neumann boundary models.

This module records finite bookkeeping for Neumann boundary windows.
-/

namespace AnalyticCombinatorics.AppB.AnalyticNeumannBoundaryModels

structure NeumannBoundaryData where
  normalPatches : ℕ
  derivativeWindow : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasNormalPatches (d : NeumannBoundaryData) : Prop :=
  0 < d.normalPatches

def derivativeWindowControlled (d : NeumannBoundaryData) : Prop :=
  d.derivativeWindow ≤ d.normalPatches + d.boundarySlack

def neumannBoundaryReady (d : NeumannBoundaryData) : Prop :=
  hasNormalPatches d ∧ derivativeWindowControlled d

def neumannBoundaryBudget (d : NeumannBoundaryData) : ℕ :=
  d.normalPatches + d.derivativeWindow + d.boundarySlack

theorem neumannBoundaryReady.hasNormalPatches {d : NeumannBoundaryData}
    (h : neumannBoundaryReady d) :
    hasNormalPatches d ∧ derivativeWindowControlled d ∧
      d.derivativeWindow ≤ neumannBoundaryBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold neumannBoundaryBudget
  omega

theorem derivativeWindow_le_budget (d : NeumannBoundaryData) :
    d.derivativeWindow ≤ neumannBoundaryBudget d := by
  unfold neumannBoundaryBudget
  omega

def sampleNeumannBoundaryData : NeumannBoundaryData :=
  { normalPatches := 6, derivativeWindow := 8, boundarySlack := 3 }

example : neumannBoundaryReady sampleNeumannBoundaryData := by
  norm_num [neumannBoundaryReady, hasNormalPatches]
  norm_num [derivativeWindowControlled, sampleNeumannBoundaryData]

example : neumannBoundaryBudget sampleNeumannBoundaryData = 17 := by
  native_decide

structure NeumannBoundaryWindow where
  normalWindow : ℕ
  derivativeWindow : ℕ
  boundarySlack : ℕ
  derivativeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NeumannBoundaryWindow.derivativeControlled (w : NeumannBoundaryWindow) : Prop :=
  w.derivativeWindow ≤ w.normalWindow + w.boundarySlack + w.slack

def neumannBoundaryWindowReady (w : NeumannBoundaryWindow) : Prop :=
  0 < w.normalWindow ∧ w.derivativeControlled ∧
    w.derivativeBudget ≤ w.normalWindow + w.derivativeWindow + w.slack

def NeumannBoundaryWindow.certificate (w : NeumannBoundaryWindow) : ℕ :=
  w.normalWindow + w.derivativeWindow + w.boundarySlack + w.derivativeBudget + w.slack

theorem neumannBoundary_derivativeBudget_le_certificate (w : NeumannBoundaryWindow) :
    w.derivativeBudget ≤ w.certificate := by
  unfold NeumannBoundaryWindow.certificate
  omega

def sampleNeumannBoundaryWindow : NeumannBoundaryWindow :=
  { normalWindow := 5, derivativeWindow := 7, boundarySlack := 2,
    derivativeBudget := 14, slack := 2 }

example : neumannBoundaryWindowReady sampleNeumannBoundaryWindow := by
  norm_num [neumannBoundaryWindowReady, NeumannBoundaryWindow.derivativeControlled,
    sampleNeumannBoundaryWindow]


structure AnalyticNeumannBoundaryModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticNeumannBoundaryModelsBudgetCertificate.controlled
    (c : AnalyticNeumannBoundaryModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticNeumannBoundaryModelsBudgetCertificate.budgetControlled
    (c : AnalyticNeumannBoundaryModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticNeumannBoundaryModelsBudgetCertificate.Ready
    (c : AnalyticNeumannBoundaryModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticNeumannBoundaryModelsBudgetCertificate.size
    (c : AnalyticNeumannBoundaryModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticNeumannBoundaryModels_budgetCertificate_le_size
    (c : AnalyticNeumannBoundaryModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticNeumannBoundaryModelsBudgetCertificate :
    AnalyticNeumannBoundaryModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticNeumannBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticNeumannBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticNeumannBoundaryModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]

example :
    sampleAnalyticNeumannBoundaryModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate.size := by
  apply analyticNeumannBoundaryModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.controlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]
  · norm_num [AnalyticNeumannBoundaryModelsBudgetCertificate.budgetControlled,
      sampleAnalyticNeumannBoundaryModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List AnalyticNeumannBoundaryModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticNeumannBoundaryModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticNeumannBoundaryModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticNeumannBoundaryModels
