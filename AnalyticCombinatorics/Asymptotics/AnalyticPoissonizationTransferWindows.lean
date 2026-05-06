import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic Poissonization transfer windows.

This module records finite bookkeeping for analytic Poissonization transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticPoissonizationTransferWindows

structure AnalyticPoissonizationTransferData where
  poissonScale : ℕ
  transferWindow : ℕ
  analyticSlack : ℕ
deriving DecidableEq, Repr

def hasPoissonScale (d : AnalyticPoissonizationTransferData) : Prop :=
  0 < d.poissonScale

def transferWindowControlled
    (d : AnalyticPoissonizationTransferData) : Prop :=
  d.transferWindow ≤ d.poissonScale + d.analyticSlack

def analyticPoissonizationTransferReady
    (d : AnalyticPoissonizationTransferData) : Prop :=
  hasPoissonScale d ∧ transferWindowControlled d

def analyticPoissonizationTransferBudget
    (d : AnalyticPoissonizationTransferData) : ℕ :=
  d.poissonScale + d.transferWindow + d.analyticSlack

theorem analyticPoissonizationTransferReady.hasPoissonScale
    {d : AnalyticPoissonizationTransferData}
    (h : analyticPoissonizationTransferReady d) :
    hasPoissonScale d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ analyticPoissonizationTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold analyticPoissonizationTransferBudget
  omega

theorem transferWindow_le_budget
    (d : AnalyticPoissonizationTransferData) :
    d.transferWindow ≤ analyticPoissonizationTransferBudget d := by
  unfold analyticPoissonizationTransferBudget
  omega

def sampleAnalyticPoissonizationTransferData :
    AnalyticPoissonizationTransferData :=
  { poissonScale := 6, transferWindow := 8, analyticSlack := 3 }

example : analyticPoissonizationTransferReady
    sampleAnalyticPoissonizationTransferData := by
  norm_num [analyticPoissonizationTransferReady, hasPoissonScale]
  norm_num [transferWindowControlled, sampleAnalyticPoissonizationTransferData]

example :
    analyticPoissonizationTransferBudget
      sampleAnalyticPoissonizationTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for analytic Poissonization transfer windows. -/
def analyticPoissonizationTransferListReady
    (windows : List AnalyticPoissonizationTransferData) : Bool :=
  windows.all fun d =>
    0 < d.poissonScale && d.transferWindow ≤ d.poissonScale + d.analyticSlack

theorem analyticPoissonizationTransferList_readyWindow :
    analyticPoissonizationTransferListReady
      [{ poissonScale := 4, transferWindow := 5, analyticSlack := 1 },
       { poissonScale := 6, transferWindow := 8, analyticSlack := 3 }] = true := by
  unfold analyticPoissonizationTransferListReady
  native_decide

/-- A certificate window for analytic Poissonization transfer. -/
structure AnalyticPoissonizationTransferCertificateWindow where
  poissonWindow : ℕ
  transferWindow : ℕ
  analyticSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by the Poisson window. -/
def analyticPoissonizationTransferCertificateControlled
    (w : AnalyticPoissonizationTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.poissonWindow + w.analyticSlack + w.slack

/-- Readiness for a Poissonization transfer certificate. -/
def analyticPoissonizationTransferCertificateReady
    (w : AnalyticPoissonizationTransferCertificateWindow) : Prop :=
  0 < w.poissonWindow ∧
    analyticPoissonizationTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.poissonWindow + w.transferWindow + w.slack

/-- Total size of a Poissonization transfer certificate. -/
def analyticPoissonizationTransferCertificate
    (w : AnalyticPoissonizationTransferCertificateWindow) : ℕ :=
  w.poissonWindow + w.transferWindow + w.analyticSlack +
    w.certificateBudget + w.slack

theorem analyticPoissonizationTransferCertificate_budget_le_certificate
    (w : AnalyticPoissonizationTransferCertificateWindow)
    (h : analyticPoissonizationTransferCertificateReady w) :
    w.certificateBudget ≤ analyticPoissonizationTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold analyticPoissonizationTransferCertificate
  omega

def sampleAnalyticPoissonizationTransferCertificateWindow :
    AnalyticPoissonizationTransferCertificateWindow where
  poissonWindow := 6
  transferWindow := 7
  analyticSlack := 2
  certificateBudget := 12
  slack := 1

example :
    analyticPoissonizationTransferCertificateReady
      sampleAnalyticPoissonizationTransferCertificateWindow := by
  norm_num [analyticPoissonizationTransferCertificateReady,
    analyticPoissonizationTransferCertificateControlled,
    sampleAnalyticPoissonizationTransferCertificateWindow]

example :
    sampleAnalyticPoissonizationTransferCertificateWindow.certificateBudget ≤
      analyticPoissonizationTransferCertificate
        sampleAnalyticPoissonizationTransferCertificateWindow := by
  apply analyticPoissonizationTransferCertificate_budget_le_certificate
  norm_num [analyticPoissonizationTransferCertificateReady,
    analyticPoissonizationTransferCertificateControlled,
    sampleAnalyticPoissonizationTransferCertificateWindow]

structure AnalyticPoissonizationTransferRefinementCertificate where
  poissonWindow : ℕ
  transferWindow : ℕ
  analyticSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticPoissonizationTransferRefinementCertificate.transferControlled
    (c : AnalyticPoissonizationTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.poissonWindow + c.analyticSlackWindow + c.slack

def AnalyticPoissonizationTransferRefinementCertificate.certificateBudgetControlled
    (c : AnalyticPoissonizationTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poissonWindow + c.transferWindow + c.analyticSlackWindow + c.slack

def analyticPoissonizationTransferRefinementReady
    (c : AnalyticPoissonizationTransferRefinementCertificate) : Prop :=
  0 < c.poissonWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def AnalyticPoissonizationTransferRefinementCertificate.size
    (c : AnalyticPoissonizationTransferRefinementCertificate) : ℕ :=
  c.poissonWindow + c.transferWindow + c.analyticSlackWindow + c.slack

theorem analyticPoissonizationTransfer_certificateBudgetWindow_le_size
    {c : AnalyticPoissonizationTransferRefinementCertificate}
    (h : analyticPoissonizationTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleAnalyticPoissonizationTransferRefinementCertificate :
    AnalyticPoissonizationTransferRefinementCertificate :=
  { poissonWindow := 6, transferWindow := 7, analyticSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : analyticPoissonizationTransferRefinementReady
    sampleAnalyticPoissonizationTransferRefinementCertificate := by
  norm_num [analyticPoissonizationTransferRefinementReady,
    AnalyticPoissonizationTransferRefinementCertificate.transferControlled,
    AnalyticPoissonizationTransferRefinementCertificate.certificateBudgetControlled,
    sampleAnalyticPoissonizationTransferRefinementCertificate]

example :
    sampleAnalyticPoissonizationTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleAnalyticPoissonizationTransferRefinementCertificate.size := by
  norm_num [AnalyticPoissonizationTransferRefinementCertificate.size,
    sampleAnalyticPoissonizationTransferRefinementCertificate]

structure AnalyticPoissonizationTransferBudgetCertificate where
  poissonWindow : ℕ
  transferWindow : ℕ
  analyticSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticPoissonizationTransferBudgetCertificate.controlled
    (c : AnalyticPoissonizationTransferBudgetCertificate) : Prop :=
  0 < c.poissonWindow ∧
    c.transferWindow ≤ c.poissonWindow + c.analyticSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.poissonWindow + c.transferWindow + c.analyticSlackWindow + c.slack

def AnalyticPoissonizationTransferBudgetCertificate.budgetControlled
    (c : AnalyticPoissonizationTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poissonWindow + c.transferWindow + c.analyticSlackWindow +
      c.transferBudgetWindow + c.slack

def AnalyticPoissonizationTransferBudgetCertificate.Ready
    (c : AnalyticPoissonizationTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticPoissonizationTransferBudgetCertificate.size
    (c : AnalyticPoissonizationTransferBudgetCertificate) : ℕ :=
  c.poissonWindow + c.transferWindow + c.analyticSlackWindow +
    c.transferBudgetWindow + c.slack

theorem analyticPoissonizationTransfer_budgetCertificate_le_size
    (c : AnalyticPoissonizationTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticPoissonizationTransferBudgetCertificate :
    AnalyticPoissonizationTransferBudgetCertificate :=
  { poissonWindow := 6
    transferWindow := 7
    analyticSlackWindow := 2
    transferBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleAnalyticPoissonizationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.controlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.budgetControlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]

example :
    sampleAnalyticPoissonizationTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPoissonizationTransferBudgetCertificate.size := by
  apply analyticPoissonizationTransfer_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.controlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.budgetControlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAnalyticPoissonizationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.controlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]
  · norm_num [AnalyticPoissonizationTransferBudgetCertificate.budgetControlled,
      sampleAnalyticPoissonizationTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticPoissonizationTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticPoissonizationTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AnalyticPoissonizationTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticPoissonizationTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAnalyticPoissonizationTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticPoissonizationTransferWindows
