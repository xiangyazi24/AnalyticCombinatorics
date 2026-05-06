import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform saddle transfer error windows.

This module records finite bookkeeping for saddle transfer error windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformSaddleTransferErrorWindows

structure SaddleTransferErrorData where
  saddleScale : ℕ
  errorWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleScale (d : SaddleTransferErrorData) : Prop :=
  0 < d.saddleScale

def errorWindowControlled (d : SaddleTransferErrorData) : Prop :=
  d.errorWindow ≤ d.saddleScale + d.transferSlack

def saddleTransferErrorReady (d : SaddleTransferErrorData) : Prop :=
  hasSaddleScale d ∧ errorWindowControlled d

def saddleTransferErrorBudget (d : SaddleTransferErrorData) : ℕ :=
  d.saddleScale + d.errorWindow + d.transferSlack

theorem saddleTransferErrorReady.hasSaddleScale
    {d : SaddleTransferErrorData}
    (h : saddleTransferErrorReady d) :
    hasSaddleScale d ∧ errorWindowControlled d ∧
      d.errorWindow ≤ saddleTransferErrorBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold saddleTransferErrorBudget
  omega

theorem errorWindow_le_budget (d : SaddleTransferErrorData) :
    d.errorWindow ≤ saddleTransferErrorBudget d := by
  unfold saddleTransferErrorBudget
  omega

def sampleSaddleTransferErrorData : SaddleTransferErrorData :=
  { saddleScale := 7, errorWindow := 9, transferSlack := 3 }

example : saddleTransferErrorReady sampleSaddleTransferErrorData := by
  norm_num [saddleTransferErrorReady, hasSaddleScale]
  norm_num [errorWindowControlled, sampleSaddleTransferErrorData]

example : saddleTransferErrorBudget sampleSaddleTransferErrorData = 19 := by
  native_decide

/-- Finite executable readiness audit for saddle transfer error data. -/
def saddleTransferErrorDataListReady
    (data : List SaddleTransferErrorData) : Bool :=
  data.all fun d =>
    0 < d.saddleScale && d.errorWindow ≤ d.saddleScale + d.transferSlack

theorem saddleTransferErrorDataList_readyWindow :
    saddleTransferErrorDataListReady
      [{ saddleScale := 4, errorWindow := 5, transferSlack := 1 },
       { saddleScale := 7, errorWindow := 9, transferSlack := 3 }] = true := by
  unfold saddleTransferErrorDataListReady
  native_decide

/-- A certificate window for uniform saddle transfer errors. -/
structure SaddleTransferErrorCertificateWindow where
  saddleWindow : ℕ
  errorWindow : ℕ
  transferSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The error window is controlled by the saddle window. -/
def saddleTransferErrorCertificateControlled
    (w : SaddleTransferErrorCertificateWindow) : Prop :=
  w.errorWindow ≤ w.saddleWindow + w.transferSlack + w.slack

/-- Readiness for a saddle transfer error certificate. -/
def saddleTransferErrorCertificateReady
    (w : SaddleTransferErrorCertificateWindow) : Prop :=
  0 < w.saddleWindow ∧
    saddleTransferErrorCertificateControlled w ∧
      w.certificateBudget ≤ w.saddleWindow + w.errorWindow + w.slack

/-- Total size of a saddle transfer error certificate. -/
def saddleTransferErrorCertificate
    (w : SaddleTransferErrorCertificateWindow) : ℕ :=
  w.saddleWindow + w.errorWindow + w.transferSlack + w.certificateBudget + w.slack

theorem saddleTransferErrorCertificate_budget_le_certificate
    (w : SaddleTransferErrorCertificateWindow)
    (h : saddleTransferErrorCertificateReady w) :
    w.certificateBudget ≤ saddleTransferErrorCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold saddleTransferErrorCertificate
  omega

def sampleSaddleTransferErrorCertificateWindow :
    SaddleTransferErrorCertificateWindow where
  saddleWindow := 7
  errorWindow := 8
  transferSlack := 2
  certificateBudget := 14
  slack := 1

example :
    saddleTransferErrorCertificateReady
      sampleSaddleTransferErrorCertificateWindow := by
  norm_num [saddleTransferErrorCertificateReady,
    saddleTransferErrorCertificateControlled,
    sampleSaddleTransferErrorCertificateWindow]

example :
    sampleSaddleTransferErrorCertificateWindow.certificateBudget ≤
      saddleTransferErrorCertificate
        sampleSaddleTransferErrorCertificateWindow := by
  apply saddleTransferErrorCertificate_budget_le_certificate
  norm_num [saddleTransferErrorCertificateReady,
    saddleTransferErrorCertificateControlled,
    sampleSaddleTransferErrorCertificateWindow]

structure SaddleTransferErrorRefinementCertificate where
  saddleWindow : ℕ
  errorWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleTransferErrorRefinementCertificate.errorControlled
    (c : SaddleTransferErrorRefinementCertificate) : Prop :=
  c.errorWindow ≤ c.saddleWindow + c.transferSlackWindow + c.slack

def SaddleTransferErrorRefinementCertificate.certificateBudgetControlled
    (c : SaddleTransferErrorRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.errorWindow + c.transferSlackWindow + c.slack

def saddleTransferErrorRefinementReady
    (c : SaddleTransferErrorRefinementCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.errorControlled ∧ c.certificateBudgetControlled

def SaddleTransferErrorRefinementCertificate.size
    (c : SaddleTransferErrorRefinementCertificate) : ℕ :=
  c.saddleWindow + c.errorWindow + c.transferSlackWindow + c.slack

theorem saddleTransferError_certificateBudgetWindow_le_size
    {c : SaddleTransferErrorRefinementCertificate}
    (h : saddleTransferErrorRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSaddleTransferErrorRefinementCertificate :
    SaddleTransferErrorRefinementCertificate :=
  { saddleWindow := 7, errorWindow := 8, transferSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : saddleTransferErrorRefinementReady
    sampleSaddleTransferErrorRefinementCertificate := by
  norm_num [saddleTransferErrorRefinementReady,
    SaddleTransferErrorRefinementCertificate.errorControlled,
    SaddleTransferErrorRefinementCertificate.certificateBudgetControlled,
    sampleSaddleTransferErrorRefinementCertificate]

example :
    sampleSaddleTransferErrorRefinementCertificate.certificateBudgetWindow ≤
      sampleSaddleTransferErrorRefinementCertificate.size := by
  norm_num [SaddleTransferErrorRefinementCertificate.size,
    sampleSaddleTransferErrorRefinementCertificate]

structure SaddleTransferErrorBudgetCertificate where
  saddleWindow : ℕ
  errorWindow : ℕ
  transferSlackWindow : ℕ
  errorBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleTransferErrorBudgetCertificate.controlled
    (c : SaddleTransferErrorBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.errorWindow ≤ c.saddleWindow + c.transferSlackWindow + c.slack ∧
      c.errorBudgetWindow ≤
        c.saddleWindow + c.errorWindow + c.transferSlackWindow + c.slack

def SaddleTransferErrorBudgetCertificate.budgetControlled
    (c : SaddleTransferErrorBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.errorWindow + c.transferSlackWindow +
      c.errorBudgetWindow + c.slack

def SaddleTransferErrorBudgetCertificate.Ready
    (c : SaddleTransferErrorBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SaddleTransferErrorBudgetCertificate.size
    (c : SaddleTransferErrorBudgetCertificate) : ℕ :=
  c.saddleWindow + c.errorWindow + c.transferSlackWindow +
    c.errorBudgetWindow + c.slack

theorem saddleTransferError_budgetCertificate_le_size
    (c : SaddleTransferErrorBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSaddleTransferErrorBudgetCertificate :
    SaddleTransferErrorBudgetCertificate :=
  { saddleWindow := 7
    errorWindow := 8
    transferSlackWindow := 2
    errorBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleSaddleTransferErrorBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleTransferErrorBudgetCertificate.controlled,
      sampleSaddleTransferErrorBudgetCertificate]
  · norm_num [SaddleTransferErrorBudgetCertificate.budgetControlled,
      sampleSaddleTransferErrorBudgetCertificate]

example :
    sampleSaddleTransferErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleTransferErrorBudgetCertificate.size := by
  apply saddleTransferError_budgetCertificate_le_size
  constructor
  · norm_num [SaddleTransferErrorBudgetCertificate.controlled,
      sampleSaddleTransferErrorBudgetCertificate]
  · norm_num [SaddleTransferErrorBudgetCertificate.budgetControlled,
      sampleSaddleTransferErrorBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSaddleTransferErrorBudgetCertificate.Ready := by
  constructor
  · norm_num [SaddleTransferErrorBudgetCertificate.controlled,
      sampleSaddleTransferErrorBudgetCertificate]
  · norm_num [SaddleTransferErrorBudgetCertificate.budgetControlled,
      sampleSaddleTransferErrorBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSaddleTransferErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleSaddleTransferErrorBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SaddleTransferErrorBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSaddleTransferErrorBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSaddleTransferErrorBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformSaddleTransferErrorWindows
