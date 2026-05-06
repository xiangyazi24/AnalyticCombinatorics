import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform transfer error windows.

This module records finite bookkeeping for transfer error windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformTransferErrorWindows

structure TransferErrorWindowData where
  transferOrder : ℕ
  errorWindow : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasTransferOrder (d : TransferErrorWindowData) : Prop :=
  0 < d.transferOrder

def errorWindowControlled (d : TransferErrorWindowData) : Prop :=
  d.errorWindow ≤ d.transferOrder + d.uniformSlack

def transferErrorWindowReady (d : TransferErrorWindowData) : Prop :=
  hasTransferOrder d ∧ errorWindowControlled d

def transferErrorWindowBudget (d : TransferErrorWindowData) : ℕ :=
  d.transferOrder + d.errorWindow + d.uniformSlack

theorem transferErrorWindowReady.hasTransferOrder
    {d : TransferErrorWindowData}
    (h : transferErrorWindowReady d) :
    hasTransferOrder d ∧ errorWindowControlled d ∧
      d.errorWindow ≤ transferErrorWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold transferErrorWindowBudget
  omega

theorem errorWindow_le_budget (d : TransferErrorWindowData) :
    d.errorWindow ≤ transferErrorWindowBudget d := by
  unfold transferErrorWindowBudget
  omega

def sampleTransferErrorWindowData : TransferErrorWindowData :=
  { transferOrder := 6, errorWindow := 8, uniformSlack := 3 }

example : transferErrorWindowReady sampleTransferErrorWindowData := by
  norm_num [transferErrorWindowReady, hasTransferOrder]
  norm_num [errorWindowControlled, sampleTransferErrorWindowData]

example : transferErrorWindowBudget sampleTransferErrorWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for transfer error windows. -/
def transferErrorWindowDataListReady
    (data : List TransferErrorWindowData) : Bool :=
  data.all fun d =>
    0 < d.transferOrder && d.errorWindow ≤ d.transferOrder + d.uniformSlack

theorem transferErrorWindowDataList_readyWindow :
    transferErrorWindowDataListReady
      [{ transferOrder := 4, errorWindow := 5, uniformSlack := 1 },
       { transferOrder := 6, errorWindow := 8, uniformSlack := 3 }] = true := by
  unfold transferErrorWindowDataListReady
  native_decide

/-- A certificate window for uniform transfer errors. -/
structure TransferErrorCertificateWindow where
  transferWindow : ℕ
  errorWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The error window is controlled by the transfer window. -/
def transferErrorCertificateControlled
    (w : TransferErrorCertificateWindow) : Prop :=
  w.errorWindow ≤ w.transferWindow + w.uniformSlack + w.slack

/-- Readiness for a transfer error certificate. -/
def transferErrorCertificateReady
    (w : TransferErrorCertificateWindow) : Prop :=
  0 < w.transferWindow ∧
    transferErrorCertificateControlled w ∧
      w.certificateBudget ≤ w.transferWindow + w.errorWindow + w.slack

/-- Total size of a transfer error certificate. -/
def transferErrorCertificate (w : TransferErrorCertificateWindow) : ℕ :=
  w.transferWindow + w.errorWindow + w.uniformSlack + w.certificateBudget + w.slack

theorem transferErrorCertificate_budget_le_certificate
    (w : TransferErrorCertificateWindow)
    (h : transferErrorCertificateReady w) :
    w.certificateBudget ≤ transferErrorCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold transferErrorCertificate
  omega

def sampleTransferErrorCertificateWindow :
    TransferErrorCertificateWindow where
  transferWindow := 6
  errorWindow := 7
  uniformSlack := 2
  certificateBudget := 12
  slack := 1

example :
    transferErrorCertificateReady sampleTransferErrorCertificateWindow := by
  norm_num [transferErrorCertificateReady,
    transferErrorCertificateControlled, sampleTransferErrorCertificateWindow]

example :
    sampleTransferErrorCertificateWindow.certificateBudget ≤
      transferErrorCertificate sampleTransferErrorCertificateWindow := by
  apply transferErrorCertificate_budget_le_certificate
  norm_num [transferErrorCertificateReady,
    transferErrorCertificateControlled, sampleTransferErrorCertificateWindow]

structure TransferErrorRefinementCertificate where
  transferWindow : ℕ
  errorWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferErrorRefinementCertificate.errorControlled
    (c : TransferErrorRefinementCertificate) : Prop :=
  c.errorWindow ≤ c.transferWindow + c.uniformSlackWindow + c.slack

def TransferErrorRefinementCertificate.certificateBudgetControlled
    (c : TransferErrorRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.transferWindow + c.errorWindow + c.uniformSlackWindow + c.slack

def transferErrorRefinementReady
    (c : TransferErrorRefinementCertificate) : Prop :=
  0 < c.transferWindow ∧ c.errorControlled ∧ c.certificateBudgetControlled

def TransferErrorRefinementCertificate.size
    (c : TransferErrorRefinementCertificate) : ℕ :=
  c.transferWindow + c.errorWindow + c.uniformSlackWindow + c.slack

theorem transferError_certificateBudgetWindow_le_size
    {c : TransferErrorRefinementCertificate}
    (h : transferErrorRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleTransferErrorRefinementCertificate :
    TransferErrorRefinementCertificate :=
  { transferWindow := 6, errorWindow := 7, uniformSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : transferErrorRefinementReady
    sampleTransferErrorRefinementCertificate := by
  norm_num [transferErrorRefinementReady,
    TransferErrorRefinementCertificate.errorControlled,
    TransferErrorRefinementCertificate.certificateBudgetControlled,
    sampleTransferErrorRefinementCertificate]

example :
    sampleTransferErrorRefinementCertificate.certificateBudgetWindow ≤
      sampleTransferErrorRefinementCertificate.size := by
  norm_num [TransferErrorRefinementCertificate.size,
    sampleTransferErrorRefinementCertificate]

/-- A second-stage transfer-error certificate with a named external budget. -/
structure TransferErrorBudgetCertificate where
  transferWindow : ℕ
  errorWindow : ℕ
  uniformSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TransferErrorBudgetCertificate.errorControlled
    (cert : TransferErrorBudgetCertificate) : Prop :=
  0 < cert.transferWindow ∧
    cert.errorWindow ≤ cert.transferWindow + cert.uniformSlackWindow + cert.slack ∧
      cert.transferBudgetWindow ≤
        cert.transferWindow + cert.errorWindow + cert.uniformSlackWindow + cert.slack

def TransferErrorBudgetCertificate.budgetControlled
    (cert : TransferErrorBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.transferWindow + cert.errorWindow + cert.uniformSlackWindow +
      cert.transferBudgetWindow + cert.slack

def transferErrorBudgetReady (cert : TransferErrorBudgetCertificate) : Prop :=
  cert.errorControlled ∧ cert.budgetControlled

def TransferErrorBudgetCertificate.size
    (cert : TransferErrorBudgetCertificate) : ℕ :=
  cert.transferWindow + cert.errorWindow + cert.uniformSlackWindow +
    cert.transferBudgetWindow + cert.slack

theorem transferError_budgetCertificate_le_size
    (cert : TransferErrorBudgetCertificate)
    (h : transferErrorBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTransferErrorBudgetCertificate :
    TransferErrorBudgetCertificate :=
  { transferWindow := 6, errorWindow := 7, uniformSlackWindow := 2,
    transferBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : transferErrorBudgetReady sampleTransferErrorBudgetCertificate := by
  norm_num [transferErrorBudgetReady,
    TransferErrorBudgetCertificate.errorControlled,
    TransferErrorBudgetCertificate.budgetControlled,
    sampleTransferErrorBudgetCertificate]

example :
    sampleTransferErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferErrorBudgetCertificate.size := by
  apply transferError_budgetCertificate_le_size
  norm_num [transferErrorBudgetReady,
    TransferErrorBudgetCertificate.errorControlled,
    TransferErrorBudgetCertificate.budgetControlled,
    sampleTransferErrorBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    transferErrorBudgetReady sampleTransferErrorBudgetCertificate := by
  constructor
  · norm_num [TransferErrorBudgetCertificate.errorControlled,
      sampleTransferErrorBudgetCertificate]
  · norm_num [TransferErrorBudgetCertificate.budgetControlled,
      sampleTransferErrorBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTransferErrorBudgetCertificate.certificateBudgetWindow ≤
      sampleTransferErrorBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TransferErrorBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTransferErrorBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTransferErrorBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformTransferErrorWindows
