import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform depoissonization error windows.

This module records finite bookkeeping for uniform depoissonization errors.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformDepoissonizationErrorWindows

structure DepoissonizationErrorWindowData where
  analyticWindow : ℕ
  discreteError : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def hasAnalyticWindow (d : DepoissonizationErrorWindowData) : Prop :=
  0 < d.analyticWindow

def discreteErrorControlled (d : DepoissonizationErrorWindowData) : Prop :=
  d.discreteError ≤ d.analyticWindow + d.errorSlack

def depoissonizationErrorReady
    (d : DepoissonizationErrorWindowData) : Prop :=
  hasAnalyticWindow d ∧ discreteErrorControlled d

def depoissonizationErrorBudget
    (d : DepoissonizationErrorWindowData) : ℕ :=
  d.analyticWindow + d.discreteError + d.errorSlack

theorem depoissonizationErrorReady.hasAnalyticWindow
    {d : DepoissonizationErrorWindowData}
    (h : depoissonizationErrorReady d) :
    hasAnalyticWindow d ∧ discreteErrorControlled d ∧
      d.discreteError ≤ depoissonizationErrorBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold depoissonizationErrorBudget
  omega

theorem discreteError_le_budget (d : DepoissonizationErrorWindowData) :
    d.discreteError ≤ depoissonizationErrorBudget d := by
  unfold depoissonizationErrorBudget
  omega

def sampleDepoissonizationErrorWindowData :
    DepoissonizationErrorWindowData :=
  { analyticWindow := 6, discreteError := 8, errorSlack := 3 }

example : depoissonizationErrorReady sampleDepoissonizationErrorWindowData := by
  norm_num [depoissonizationErrorReady, hasAnalyticWindow]
  norm_num [discreteErrorControlled, sampleDepoissonizationErrorWindowData]

example :
    depoissonizationErrorBudget sampleDepoissonizationErrorWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for depoissonization error window data. -/
def depoissonizationErrorDataListReady
    (data : List DepoissonizationErrorWindowData) : Bool :=
  data.all fun d =>
    0 < d.analyticWindow && d.discreteError ≤ d.analyticWindow + d.errorSlack

theorem depoissonizationErrorDataList_readyWindow :
    depoissonizationErrorDataListReady
      [{ analyticWindow := 4, discreteError := 5, errorSlack := 1 },
       { analyticWindow := 6, discreteError := 8, errorSlack := 3 }] = true := by
  unfold depoissonizationErrorDataListReady
  native_decide

/-- A certificate window for uniform depoissonization errors. -/
structure DepoissonizationErrorCertificateWindow where
  analyticWindow : ℕ
  discreteWindow : ℕ
  errorSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The discrete error window is controlled by the analytic window. -/
def depoissonizationErrorCertificateControlled
    (w : DepoissonizationErrorCertificateWindow) : Prop :=
  w.discreteWindow ≤ w.analyticWindow + w.errorSlack + w.slack

/-- Readiness for a depoissonization error certificate. -/
def depoissonizationErrorCertificateReady
    (w : DepoissonizationErrorCertificateWindow) : Prop :=
  0 < w.analyticWindow ∧
    depoissonizationErrorCertificateControlled w ∧
      w.certificateBudget ≤ w.analyticWindow + w.discreteWindow + w.slack

/-- Total size of a depoissonization error certificate. -/
def depoissonizationErrorCertificate
    (w : DepoissonizationErrorCertificateWindow) : ℕ :=
  w.analyticWindow + w.discreteWindow + w.errorSlack + w.certificateBudget + w.slack

theorem depoissonizationErrorCertificate_budget_le_certificate
    (w : DepoissonizationErrorCertificateWindow)
    (h : depoissonizationErrorCertificateReady w) :
    w.certificateBudget ≤ depoissonizationErrorCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold depoissonizationErrorCertificate
  omega

def sampleDepoissonizationErrorCertificateWindow :
    DepoissonizationErrorCertificateWindow where
  analyticWindow := 6
  discreteWindow := 7
  errorSlack := 2
  certificateBudget := 12
  slack := 1

example :
    depoissonizationErrorCertificateReady
      sampleDepoissonizationErrorCertificateWindow := by
  norm_num [depoissonizationErrorCertificateReady,
    depoissonizationErrorCertificateControlled,
    sampleDepoissonizationErrorCertificateWindow]

example :
    sampleDepoissonizationErrorCertificateWindow.certificateBudget ≤
      depoissonizationErrorCertificate
        sampleDepoissonizationErrorCertificateWindow := by
  apply depoissonizationErrorCertificate_budget_le_certificate
  norm_num [depoissonizationErrorCertificateReady,
    depoissonizationErrorCertificateControlled,
    sampleDepoissonizationErrorCertificateWindow]

structure DepoissonizationErrorRefinementCertificate where
  analyticWindow : ℕ
  discreteWindow : ℕ
  errorSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationErrorRefinementCertificate.discreteControlled
    (c : DepoissonizationErrorRefinementCertificate) : Prop :=
  c.discreteWindow ≤ c.analyticWindow + c.errorSlackWindow + c.slack

def DepoissonizationErrorRefinementCertificate.certificateBudgetControlled
    (c : DepoissonizationErrorRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.discreteWindow + c.errorSlackWindow + c.slack

def depoissonizationErrorRefinementReady
    (c : DepoissonizationErrorRefinementCertificate) : Prop :=
  0 < c.analyticWindow ∧ c.discreteControlled ∧ c.certificateBudgetControlled

def DepoissonizationErrorRefinementCertificate.size
    (c : DepoissonizationErrorRefinementCertificate) : ℕ :=
  c.analyticWindow + c.discreteWindow + c.errorSlackWindow + c.slack

theorem depoissonizationError_certificateBudgetWindow_le_size
    {c : DepoissonizationErrorRefinementCertificate}
    (h : depoissonizationErrorRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleDepoissonizationErrorRefinementCertificate :
    DepoissonizationErrorRefinementCertificate :=
  { analyticWindow := 6, discreteWindow := 7, errorSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : depoissonizationErrorRefinementReady
    sampleDepoissonizationErrorRefinementCertificate := by
  norm_num [depoissonizationErrorRefinementReady,
    DepoissonizationErrorRefinementCertificate.discreteControlled,
    DepoissonizationErrorRefinementCertificate.certificateBudgetControlled,
    sampleDepoissonizationErrorRefinementCertificate]

example :
    sampleDepoissonizationErrorRefinementCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationErrorRefinementCertificate.size := by
  norm_num [DepoissonizationErrorRefinementCertificate.size,
    sampleDepoissonizationErrorRefinementCertificate]

structure DepoissonizationErrorBudgetCertificate where
  analyticWindow : ℕ
  discreteWindow : ℕ
  errorSlackWindow : ℕ
  errorBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DepoissonizationErrorBudgetCertificate.controlled
    (c : DepoissonizationErrorBudgetCertificate) : Prop :=
  0 < c.analyticWindow ∧
    c.discreteWindow ≤ c.analyticWindow + c.errorSlackWindow + c.slack ∧
      c.errorBudgetWindow ≤
        c.analyticWindow + c.discreteWindow + c.errorSlackWindow + c.slack

def DepoissonizationErrorBudgetCertificate.budgetControlled
    (c : DepoissonizationErrorBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.analyticWindow + c.discreteWindow + c.errorSlackWindow +
      c.errorBudgetWindow + c.slack

def DepoissonizationErrorBudgetCertificate.Ready
    (c : DepoissonizationErrorBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DepoissonizationErrorBudgetCertificate.size
    (c : DepoissonizationErrorBudgetCertificate) : ℕ :=
  c.analyticWindow + c.discreteWindow + c.errorSlackWindow +
    c.errorBudgetWindow + c.slack

theorem depoissonizationError_budgetCertificate_le_size
    (c : DepoissonizationErrorBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDepoissonizationErrorBudgetCertificate :
    DepoissonizationErrorBudgetCertificate :=
  { analyticWindow := 6
    discreteWindow := 7
    errorSlackWindow := 2
    errorBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleDepoissonizationErrorBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationErrorBudgetCertificate.controlled,
      sampleDepoissonizationErrorBudgetCertificate]
  · norm_num [DepoissonizationErrorBudgetCertificate.budgetControlled,
      sampleDepoissonizationErrorBudgetCertificate]

example :
    sampleDepoissonizationErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationErrorBudgetCertificate.size := by
  apply depoissonizationError_budgetCertificate_le_size
  constructor
  · norm_num [DepoissonizationErrorBudgetCertificate.controlled,
      sampleDepoissonizationErrorBudgetCertificate]
  · norm_num [DepoissonizationErrorBudgetCertificate.budgetControlled,
      sampleDepoissonizationErrorBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDepoissonizationErrorBudgetCertificate.Ready := by
  constructor
  · norm_num [DepoissonizationErrorBudgetCertificate.controlled,
      sampleDepoissonizationErrorBudgetCertificate]
  · norm_num [DepoissonizationErrorBudgetCertificate.budgetControlled,
      sampleDepoissonizationErrorBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDepoissonizationErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleDepoissonizationErrorBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DepoissonizationErrorBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDepoissonizationErrorBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDepoissonizationErrorBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformDepoissonizationErrorWindows
