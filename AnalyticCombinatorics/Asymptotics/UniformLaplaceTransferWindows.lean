import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Laplace transfer windows.

This module records finite bookkeeping for uniform Laplace transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLaplaceTransferWindows

structure LaplaceTransferWindowData where
  laplaceOrder : ℕ
  transferWindow : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasLaplaceOrder (d : LaplaceTransferWindowData) : Prop :=
  0 < d.laplaceOrder

def transferWindowControlled (d : LaplaceTransferWindowData) : Prop :=
  d.transferWindow ≤ d.laplaceOrder + d.uniformSlack

def laplaceTransferReady (d : LaplaceTransferWindowData) : Prop :=
  hasLaplaceOrder d ∧ transferWindowControlled d

def laplaceTransferBudget (d : LaplaceTransferWindowData) : ℕ :=
  d.laplaceOrder + d.transferWindow + d.uniformSlack

theorem laplaceTransferReady.hasLaplaceOrder
    {d : LaplaceTransferWindowData}
    (h : laplaceTransferReady d) :
    hasLaplaceOrder d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ laplaceTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold laplaceTransferBudget
  omega

theorem transferWindow_le_budget (d : LaplaceTransferWindowData) :
    d.transferWindow ≤ laplaceTransferBudget d := by
  unfold laplaceTransferBudget
  omega

def sampleLaplaceTransferWindowData : LaplaceTransferWindowData :=
  { laplaceOrder := 6, transferWindow := 8, uniformSlack := 3 }

example : laplaceTransferReady sampleLaplaceTransferWindowData := by
  norm_num [laplaceTransferReady, hasLaplaceOrder]
  norm_num [transferWindowControlled, sampleLaplaceTransferWindowData]

example : laplaceTransferBudget sampleLaplaceTransferWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Laplace transfer windows. -/
def laplaceTransferWindowDataListReady
    (data : List LaplaceTransferWindowData) : Bool :=
  data.all fun d =>
    0 < d.laplaceOrder && d.transferWindow ≤ d.laplaceOrder + d.uniformSlack

theorem laplaceTransferWindowDataList_readyWindow :
    laplaceTransferWindowDataListReady
      [{ laplaceOrder := 4, transferWindow := 5, uniformSlack := 1 },
       { laplaceOrder := 6, transferWindow := 8, uniformSlack := 3 }] = true := by
  unfold laplaceTransferWindowDataListReady
  native_decide

/-- A certificate window for uniform Laplace transfer. -/
structure LaplaceTransferCertificateWindow where
  laplaceWindow : ℕ
  transferWindow : ℕ
  uniformSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by the Laplace window. -/
def laplaceTransferCertificateControlled
    (w : LaplaceTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.laplaceWindow + w.uniformSlack + w.slack

/-- Readiness for a Laplace transfer certificate. -/
def laplaceTransferCertificateReady
    (w : LaplaceTransferCertificateWindow) : Prop :=
  0 < w.laplaceWindow ∧
    laplaceTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.laplaceWindow + w.transferWindow + w.slack

/-- Total size of a Laplace transfer certificate. -/
def laplaceTransferCertificate
    (w : LaplaceTransferCertificateWindow) : ℕ :=
  w.laplaceWindow + w.transferWindow + w.uniformSlack +
    w.certificateBudget + w.slack

theorem laplaceTransferCertificate_budget_le_certificate
    (w : LaplaceTransferCertificateWindow)
    (h : laplaceTransferCertificateReady w) :
    w.certificateBudget ≤ laplaceTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold laplaceTransferCertificate
  omega

def sampleLaplaceTransferCertificateWindow :
    LaplaceTransferCertificateWindow where
  laplaceWindow := 6
  transferWindow := 7
  uniformSlack := 2
  certificateBudget := 12
  slack := 1

example :
    laplaceTransferCertificateReady sampleLaplaceTransferCertificateWindow := by
  norm_num [laplaceTransferCertificateReady,
    laplaceTransferCertificateControlled, sampleLaplaceTransferCertificateWindow]

example :
    sampleLaplaceTransferCertificateWindow.certificateBudget ≤
      laplaceTransferCertificate sampleLaplaceTransferCertificateWindow := by
  apply laplaceTransferCertificate_budget_le_certificate
  norm_num [laplaceTransferCertificateReady,
    laplaceTransferCertificateControlled, sampleLaplaceTransferCertificateWindow]

structure LaplaceTransferRefinementCertificate where
  laplaceWindow : ℕ
  transferWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceTransferRefinementCertificate.transferControlled
    (c : LaplaceTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.laplaceWindow + c.uniformSlackWindow + c.slack

def LaplaceTransferRefinementCertificate.certificateBudgetControlled
    (c : LaplaceTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.laplaceWindow + c.transferWindow + c.uniformSlackWindow + c.slack

def laplaceTransferRefinementReady
    (c : LaplaceTransferRefinementCertificate) : Prop :=
  0 < c.laplaceWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def LaplaceTransferRefinementCertificate.size
    (c : LaplaceTransferRefinementCertificate) : ℕ :=
  c.laplaceWindow + c.transferWindow + c.uniformSlackWindow + c.slack

theorem laplaceTransfer_certificateBudgetWindow_le_size
    {c : LaplaceTransferRefinementCertificate}
    (h : laplaceTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleLaplaceTransferRefinementCertificate :
    LaplaceTransferRefinementCertificate :=
  { laplaceWindow := 6, transferWindow := 7, uniformSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : laplaceTransferRefinementReady
    sampleLaplaceTransferRefinementCertificate := by
  norm_num [laplaceTransferRefinementReady,
    LaplaceTransferRefinementCertificate.transferControlled,
    LaplaceTransferRefinementCertificate.certificateBudgetControlled,
    sampleLaplaceTransferRefinementCertificate]

example :
    sampleLaplaceTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleLaplaceTransferRefinementCertificate.size := by
  norm_num [LaplaceTransferRefinementCertificate.size,
    sampleLaplaceTransferRefinementCertificate]

/-- A second-stage uniform-Laplace-transfer certificate with a named external budget. -/
structure LaplaceTransferBudgetCertificate where
  laplaceWindow : ℕ
  transferWindow : ℕ
  uniformSlackWindow : ℕ
  laplaceBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LaplaceTransferBudgetCertificate.transferControlled
    (cert : LaplaceTransferBudgetCertificate) : Prop :=
  0 < cert.laplaceWindow ∧
    cert.transferWindow ≤ cert.laplaceWindow + cert.uniformSlackWindow + cert.slack ∧
      cert.laplaceBudgetWindow ≤
        cert.laplaceWindow + cert.transferWindow + cert.uniformSlackWindow + cert.slack

def LaplaceTransferBudgetCertificate.budgetControlled
    (cert : LaplaceTransferBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.laplaceWindow + cert.transferWindow + cert.uniformSlackWindow +
      cert.laplaceBudgetWindow + cert.slack

def laplaceTransferBudgetReady
    (cert : LaplaceTransferBudgetCertificate) : Prop :=
  cert.transferControlled ∧ cert.budgetControlled

def LaplaceTransferBudgetCertificate.size
    (cert : LaplaceTransferBudgetCertificate) : ℕ :=
  cert.laplaceWindow + cert.transferWindow + cert.uniformSlackWindow +
    cert.laplaceBudgetWindow + cert.slack

theorem laplaceTransfer_budgetCertificate_le_size
    (cert : LaplaceTransferBudgetCertificate)
    (h : laplaceTransferBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLaplaceTransferBudgetCertificate :
    LaplaceTransferBudgetCertificate :=
  { laplaceWindow := 6, transferWindow := 7, uniformSlackWindow := 2,
    laplaceBudgetWindow := 16, certificateBudgetWindow := 32, slack := 1 }

example : laplaceTransferBudgetReady sampleLaplaceTransferBudgetCertificate := by
  norm_num [laplaceTransferBudgetReady,
    LaplaceTransferBudgetCertificate.transferControlled,
    LaplaceTransferBudgetCertificate.budgetControlled,
    sampleLaplaceTransferBudgetCertificate]

example :
    sampleLaplaceTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceTransferBudgetCertificate.size := by
  apply laplaceTransfer_budgetCertificate_le_size
  norm_num [laplaceTransferBudgetReady,
    LaplaceTransferBudgetCertificate.transferControlled,
    LaplaceTransferBudgetCertificate.budgetControlled,
    sampleLaplaceTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    laplaceTransferBudgetReady sampleLaplaceTransferBudgetCertificate := by
  constructor
  · norm_num [LaplaceTransferBudgetCertificate.transferControlled,
      sampleLaplaceTransferBudgetCertificate]
  · norm_num [LaplaceTransferBudgetCertificate.budgetControlled,
      sampleLaplaceTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLaplaceTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLaplaceTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LaplaceTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLaplaceTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLaplaceTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLaplaceTransferWindows
