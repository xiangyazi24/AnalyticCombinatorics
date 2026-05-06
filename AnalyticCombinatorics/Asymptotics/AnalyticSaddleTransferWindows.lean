import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic saddle transfer windows.

This module records finite bookkeeping for analytic saddle transfer windows.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticSaddleTransferWindows

structure AnalyticSaddleTransferData where
  saddleOrder : ℕ
  transferWindow : ℕ
  analyticSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleOrder (d : AnalyticSaddleTransferData) : Prop :=
  0 < d.saddleOrder

def transferWindowControlled (d : AnalyticSaddleTransferData) : Prop :=
  d.transferWindow ≤ d.saddleOrder + d.analyticSlack

def analyticSaddleTransferReady (d : AnalyticSaddleTransferData) : Prop :=
  hasSaddleOrder d ∧ transferWindowControlled d

def analyticSaddleTransferBudget (d : AnalyticSaddleTransferData) : ℕ :=
  d.saddleOrder + d.transferWindow + d.analyticSlack

theorem analyticSaddleTransferReady.hasSaddleOrder
    {d : AnalyticSaddleTransferData}
    (h : analyticSaddleTransferReady d) :
    hasSaddleOrder d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ analyticSaddleTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticSaddleTransferBudget
  omega

theorem transferWindow_le_budget (d : AnalyticSaddleTransferData) :
    d.transferWindow ≤ analyticSaddleTransferBudget d := by
  unfold analyticSaddleTransferBudget
  omega

def sampleAnalyticSaddleTransferData : AnalyticSaddleTransferData :=
  { saddleOrder := 7, transferWindow := 9, analyticSlack := 3 }

example : analyticSaddleTransferReady sampleAnalyticSaddleTransferData := by
  norm_num [analyticSaddleTransferReady, hasSaddleOrder]
  norm_num [transferWindowControlled, sampleAnalyticSaddleTransferData]

example : analyticSaddleTransferBudget sampleAnalyticSaddleTransferData = 19 := by
  native_decide

/-- Finite executable readiness audit for analytic saddle transfer windows. -/
def analyticSaddleTransferListReady
    (windows : List AnalyticSaddleTransferData) : Bool :=
  windows.all fun d =>
    0 < d.saddleOrder && d.transferWindow ≤ d.saddleOrder + d.analyticSlack

theorem analyticSaddleTransferList_readyWindow :
    analyticSaddleTransferListReady
      [{ saddleOrder := 4, transferWindow := 5, analyticSlack := 1 },
       { saddleOrder := 7, transferWindow := 9, analyticSlack := 3 }] = true := by
  unfold analyticSaddleTransferListReady
  native_decide

/-- A certificate window for transferring analytic saddle estimates. -/
structure AnalyticSaddleTransferCertificateWindow where
  saddleWindow : ℕ
  transferWindow : ℕ
  analyticSlack : ℕ
  saddleBudget : ℕ
  slack : ℕ

/-- The transfer window is bounded by the saddle window and analytic slack. -/
def analyticSaddleTransferCertificateControlled
    (w : AnalyticSaddleTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.saddleWindow + w.analyticSlack + w.slack

/-- Readiness for a certified analytic saddle transfer window. -/
def analyticSaddleTransferCertificateReady
    (w : AnalyticSaddleTransferCertificateWindow) : Prop :=
  0 < w.saddleWindow ∧
    analyticSaddleTransferCertificateControlled w ∧
      w.saddleBudget ≤ w.saddleWindow + w.transferWindow + w.slack

/-- Total budget recorded by the analytic saddle transfer certificate. -/
def analyticSaddleTransferCertificate
    (w : AnalyticSaddleTransferCertificateWindow) : ℕ :=
  w.saddleWindow + w.transferWindow + w.analyticSlack + w.saddleBudget + w.slack

theorem analyticSaddleTransferCertificate_budget_le_certificate
    (w : AnalyticSaddleTransferCertificateWindow)
    (h : analyticSaddleTransferCertificateReady w) :
    w.saddleBudget ≤ analyticSaddleTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold analyticSaddleTransferCertificate
  omega

def sampleAnalyticSaddleTransferCertificateWindow :
    AnalyticSaddleTransferCertificateWindow where
  saddleWindow := 7
  transferWindow := 8
  analyticSlack := 2
  saddleBudget := 14
  slack := 1

example :
    analyticSaddleTransferCertificateReady
      sampleAnalyticSaddleTransferCertificateWindow := by
  norm_num [analyticSaddleTransferCertificateReady,
    analyticSaddleTransferCertificateControlled,
    sampleAnalyticSaddleTransferCertificateWindow]

example :
    sampleAnalyticSaddleTransferCertificateWindow.saddleBudget ≤
      analyticSaddleTransferCertificate
        sampleAnalyticSaddleTransferCertificateWindow := by
  apply analyticSaddleTransferCertificate_budget_le_certificate
  norm_num [analyticSaddleTransferCertificateReady,
    analyticSaddleTransferCertificateControlled,
    sampleAnalyticSaddleTransferCertificateWindow]

structure AnalyticSaddleTransferRefinementCertificate where
  saddleWindow : ℕ
  transferWindow : ℕ
  analyticSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSaddleTransferRefinementCertificate.transferControlled
    (c : AnalyticSaddleTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.saddleWindow + c.analyticSlackWindow + c.slack

def AnalyticSaddleTransferRefinementCertificate.saddleBudgetControlled
    (c : AnalyticSaddleTransferRefinementCertificate) : Prop :=
  c.saddleBudgetWindow ≤
    c.saddleWindow + c.transferWindow + c.analyticSlackWindow + c.slack

def analyticSaddleTransferRefinementReady
    (c : AnalyticSaddleTransferRefinementCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.transferControlled ∧ c.saddleBudgetControlled

def AnalyticSaddleTransferRefinementCertificate.size
    (c : AnalyticSaddleTransferRefinementCertificate) : ℕ :=
  c.saddleWindow + c.transferWindow + c.analyticSlackWindow + c.slack

theorem analyticSaddleTransfer_saddleBudgetWindow_le_size
    {c : AnalyticSaddleTransferRefinementCertificate}
    (h : analyticSaddleTransferRefinementReady c) :
    c.saddleBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleAnalyticSaddleTransferRefinementCertificate :
    AnalyticSaddleTransferRefinementCertificate :=
  { saddleWindow := 7, transferWindow := 8, analyticSlackWindow := 2,
    saddleBudgetWindow := 18, slack := 1 }

example : analyticSaddleTransferRefinementReady
    sampleAnalyticSaddleTransferRefinementCertificate := by
  norm_num [analyticSaddleTransferRefinementReady,
    AnalyticSaddleTransferRefinementCertificate.transferControlled,
    AnalyticSaddleTransferRefinementCertificate.saddleBudgetControlled,
    sampleAnalyticSaddleTransferRefinementCertificate]

example :
    sampleAnalyticSaddleTransferRefinementCertificate.saddleBudgetWindow ≤
      sampleAnalyticSaddleTransferRefinementCertificate.size := by
  norm_num [AnalyticSaddleTransferRefinementCertificate.size,
    sampleAnalyticSaddleTransferRefinementCertificate]

structure AnalyticSaddleTransferBudgetCertificate where
  saddleWindow : ℕ
  transferWindow : ℕ
  analyticSlackWindow : ℕ
  saddleBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticSaddleTransferBudgetCertificate.controlled
    (c : AnalyticSaddleTransferBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.transferWindow ≤ c.saddleWindow + c.analyticSlackWindow + c.slack ∧
      c.saddleBudgetWindow ≤
        c.saddleWindow + c.transferWindow + c.analyticSlackWindow + c.slack

def AnalyticSaddleTransferBudgetCertificate.budgetControlled
    (c : AnalyticSaddleTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.transferWindow + c.analyticSlackWindow +
      c.saddleBudgetWindow + c.slack

def AnalyticSaddleTransferBudgetCertificate.Ready
    (c : AnalyticSaddleTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticSaddleTransferBudgetCertificate.size
    (c : AnalyticSaddleTransferBudgetCertificate) : ℕ :=
  c.saddleWindow + c.transferWindow + c.analyticSlackWindow +
    c.saddleBudgetWindow + c.slack

theorem analyticSaddleTransfer_budgetCertificate_le_size
    (c : AnalyticSaddleTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticSaddleTransferBudgetCertificate :
    AnalyticSaddleTransferBudgetCertificate :=
  { saddleWindow := 7
    transferWindow := 8
    analyticSlackWindow := 2
    saddleBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleAnalyticSaddleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSaddleTransferBudgetCertificate.controlled,
      sampleAnalyticSaddleTransferBudgetCertificate]
  · norm_num [AnalyticSaddleTransferBudgetCertificate.budgetControlled,
      sampleAnalyticSaddleTransferBudgetCertificate]

example :
    sampleAnalyticSaddleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSaddleTransferBudgetCertificate.size := by
  apply analyticSaddleTransfer_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticSaddleTransferBudgetCertificate.controlled,
      sampleAnalyticSaddleTransferBudgetCertificate]
  · norm_num [AnalyticSaddleTransferBudgetCertificate.budgetControlled,
      sampleAnalyticSaddleTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticSaddleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticSaddleTransferBudgetCertificate.controlled,
      sampleAnalyticSaddleTransferBudgetCertificate]
  · norm_num [AnalyticSaddleTransferBudgetCertificate.budgetControlled,
      sampleAnalyticSaddleTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticSaddleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticSaddleTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticSaddleTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticSaddleTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticSaddleTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticSaddleTransferWindows
