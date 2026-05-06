import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Implicit saddle windows.

This module records finite bookkeeping for implicit saddle windows.
-/

namespace AnalyticCombinatorics.Asymptotics.ImplicitSaddleWindows

structure ImplicitSaddleWindowData where
  implicitOrder : ℕ
  saddleWindow : ℕ
  balanceSlack : ℕ
deriving DecidableEq, Repr

def hasImplicitOrder (d : ImplicitSaddleWindowData) : Prop :=
  0 < d.implicitOrder

def saddleWindowControlled (d : ImplicitSaddleWindowData) : Prop :=
  d.saddleWindow ≤ d.implicitOrder + d.balanceSlack

def implicitSaddleWindowReady (d : ImplicitSaddleWindowData) : Prop :=
  hasImplicitOrder d ∧ saddleWindowControlled d

def implicitSaddleWindowBudget (d : ImplicitSaddleWindowData) : ℕ :=
  d.implicitOrder + d.saddleWindow + d.balanceSlack

theorem implicitSaddleWindowReady.hasImplicitOrder
    {d : ImplicitSaddleWindowData}
    (h : implicitSaddleWindowReady d) :
    hasImplicitOrder d ∧ saddleWindowControlled d ∧
      d.saddleWindow ≤ implicitSaddleWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold implicitSaddleWindowBudget
  omega

theorem saddleWindow_le_budget (d : ImplicitSaddleWindowData) :
    d.saddleWindow ≤ implicitSaddleWindowBudget d := by
  unfold implicitSaddleWindowBudget
  omega

def sampleImplicitSaddleWindowData : ImplicitSaddleWindowData :=
  { implicitOrder := 6, saddleWindow := 8, balanceSlack := 3 }

example : implicitSaddleWindowReady sampleImplicitSaddleWindowData := by
  norm_num [implicitSaddleWindowReady, hasImplicitOrder]
  norm_num [saddleWindowControlled, sampleImplicitSaddleWindowData]

example : implicitSaddleWindowBudget sampleImplicitSaddleWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for implicit saddle window data. -/
def implicitSaddleWindowDataListReady
    (data : List ImplicitSaddleWindowData) : Bool :=
  data.all fun d =>
    0 < d.implicitOrder && d.saddleWindow ≤ d.implicitOrder + d.balanceSlack

theorem implicitSaddleWindowDataList_readyWindow :
    implicitSaddleWindowDataListReady
      [{ implicitOrder := 4, saddleWindow := 5, balanceSlack := 1 },
       { implicitOrder := 6, saddleWindow := 8, balanceSlack := 3 }] = true := by
  unfold implicitSaddleWindowDataListReady
  native_decide

/-- A certificate window for implicit saddle balances. -/
structure ImplicitSaddleCertificateWindow where
  implicitWindow : ℕ
  saddleWindow : ℕ
  balanceSlack : ℕ
  saddleBudget : ℕ
  slack : ℕ

/-- The saddle window is controlled by the implicit window. -/
def implicitSaddleCertificateControlled
    (w : ImplicitSaddleCertificateWindow) : Prop :=
  w.saddleWindow ≤ w.implicitWindow + w.balanceSlack + w.slack

/-- Readiness predicate for an implicit saddle certificate. -/
def implicitSaddleCertificateReady
    (w : ImplicitSaddleCertificateWindow) : Prop :=
  0 < w.implicitWindow ∧
    implicitSaddleCertificateControlled w ∧
      w.saddleBudget ≤ w.implicitWindow + w.saddleWindow + w.slack

/-- Total size of the implicit saddle certificate. -/
def implicitSaddleCertificate (w : ImplicitSaddleCertificateWindow) : ℕ :=
  w.implicitWindow + w.saddleWindow + w.balanceSlack + w.saddleBudget + w.slack

theorem implicitSaddleCertificate_budget_le_certificate
    (w : ImplicitSaddleCertificateWindow)
    (h : implicitSaddleCertificateReady w) :
    w.saddleBudget ≤ implicitSaddleCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold implicitSaddleCertificate
  omega

def sampleImplicitSaddleCertificateWindow : ImplicitSaddleCertificateWindow where
  implicitWindow := 7
  saddleWindow := 8
  balanceSlack := 2
  saddleBudget := 14
  slack := 1

example :
    implicitSaddleCertificateReady sampleImplicitSaddleCertificateWindow := by
  norm_num [implicitSaddleCertificateReady,
    implicitSaddleCertificateControlled, sampleImplicitSaddleCertificateWindow]

example :
    sampleImplicitSaddleCertificateWindow.saddleBudget ≤
      implicitSaddleCertificate sampleImplicitSaddleCertificateWindow := by
  apply implicitSaddleCertificate_budget_le_certificate
  norm_num [implicitSaddleCertificateReady,
    implicitSaddleCertificateControlled, sampleImplicitSaddleCertificateWindow]

structure ImplicitSaddleRefinementCertificate where
  implicitWindow : ℕ
  saddleWindow : ℕ
  balanceSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitSaddleRefinementCertificate.saddleControlled
    (c : ImplicitSaddleRefinementCertificate) : Prop :=
  c.saddleWindow ≤ c.implicitWindow + c.balanceSlackWindow + c.slack

def ImplicitSaddleRefinementCertificate.saddleBudgetControlled
    (c : ImplicitSaddleRefinementCertificate) : Prop :=
  c.saddleBudgetWindow ≤
    c.implicitWindow + c.saddleWindow + c.balanceSlackWindow + c.slack

def implicitSaddleRefinementReady
    (c : ImplicitSaddleRefinementCertificate) : Prop :=
  0 < c.implicitWindow ∧ c.saddleControlled ∧ c.saddleBudgetControlled

def ImplicitSaddleRefinementCertificate.size
    (c : ImplicitSaddleRefinementCertificate) : ℕ :=
  c.implicitWindow + c.saddleWindow + c.balanceSlackWindow + c.slack

theorem implicitSaddle_saddleBudgetWindow_le_size
    {c : ImplicitSaddleRefinementCertificate}
    (h : implicitSaddleRefinementReady c) :
    c.saddleBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleImplicitSaddleRefinementCertificate :
    ImplicitSaddleRefinementCertificate :=
  { implicitWindow := 7, saddleWindow := 8, balanceSlackWindow := 2,
    saddleBudgetWindow := 18, slack := 1 }

example : implicitSaddleRefinementReady
    sampleImplicitSaddleRefinementCertificate := by
  norm_num [implicitSaddleRefinementReady,
    ImplicitSaddleRefinementCertificate.saddleControlled,
    ImplicitSaddleRefinementCertificate.saddleBudgetControlled,
    sampleImplicitSaddleRefinementCertificate]

example :
    sampleImplicitSaddleRefinementCertificate.saddleBudgetWindow ≤
      sampleImplicitSaddleRefinementCertificate.size := by
  norm_num [ImplicitSaddleRefinementCertificate.size,
    sampleImplicitSaddleRefinementCertificate]

/-- A second-stage implicit saddle certificate with an external budget. -/
structure ImplicitSaddleBudgetCertificate where
  implicitWindow : ℕ
  saddleWindow : ℕ
  balanceSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitSaddleBudgetCertificate.saddleControlled
    (cert : ImplicitSaddleBudgetCertificate) : Prop :=
  0 < cert.implicitWindow ∧
    cert.saddleWindow ≤ cert.implicitWindow + cert.balanceSlackWindow + cert.slack ∧
      cert.saddleBudgetWindow ≤
        cert.implicitWindow + cert.saddleWindow + cert.balanceSlackWindow + cert.slack

def ImplicitSaddleBudgetCertificate.budgetControlled
    (cert : ImplicitSaddleBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.implicitWindow + cert.saddleWindow + cert.balanceSlackWindow +
      cert.saddleBudgetWindow + cert.slack

def implicitSaddleBudgetReady
    (cert : ImplicitSaddleBudgetCertificate) : Prop :=
  cert.saddleControlled ∧ cert.budgetControlled

def ImplicitSaddleBudgetCertificate.size
    (cert : ImplicitSaddleBudgetCertificate) : ℕ :=
  cert.implicitWindow + cert.saddleWindow + cert.balanceSlackWindow +
    cert.saddleBudgetWindow + cert.slack

theorem implicitSaddle_certificateBudgetWindow_le_size
    (cert : ImplicitSaddleBudgetCertificate)
    (h : implicitSaddleBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitSaddleBudgetCertificate :
    ImplicitSaddleBudgetCertificate :=
  { implicitWindow := 7, saddleWindow := 8, balanceSlackWindow := 2,
    saddleBudgetWindow := 18, certificateBudgetWindow := 36, slack := 1 }

example : implicitSaddleBudgetReady sampleImplicitSaddleBudgetCertificate := by
  norm_num [implicitSaddleBudgetReady,
    ImplicitSaddleBudgetCertificate.saddleControlled,
    ImplicitSaddleBudgetCertificate.budgetControlled,
    sampleImplicitSaddleBudgetCertificate]

example :
    sampleImplicitSaddleBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitSaddleBudgetCertificate.size := by
  apply implicitSaddle_certificateBudgetWindow_le_size
  norm_num [implicitSaddleBudgetReady,
    ImplicitSaddleBudgetCertificate.saddleControlled,
    ImplicitSaddleBudgetCertificate.budgetControlled,
    sampleImplicitSaddleBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    implicitSaddleBudgetReady sampleImplicitSaddleBudgetCertificate := by
  constructor
  · norm_num [ImplicitSaddleBudgetCertificate.saddleControlled,
      sampleImplicitSaddleBudgetCertificate]
  · norm_num [ImplicitSaddleBudgetCertificate.budgetControlled,
      sampleImplicitSaddleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitSaddleBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitSaddleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ImplicitSaddleBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleImplicitSaddleBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleImplicitSaddleBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ImplicitSaddleWindows
