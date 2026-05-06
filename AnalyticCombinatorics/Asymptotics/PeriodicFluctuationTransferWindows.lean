import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Periodic fluctuation transfer windows.

This module records finite bookkeeping for periodic fluctuation transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.PeriodicFluctuationTransferWindows

structure PeriodicFluctuationTransferData where
  periodCount : ℕ
  fluctuationWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasPeriodCount (d : PeriodicFluctuationTransferData) : Prop :=
  0 < d.periodCount

def fluctuationWindowControlled
    (d : PeriodicFluctuationTransferData) : Prop :=
  d.fluctuationWindow ≤ d.periodCount + d.transferSlack

def periodicFluctuationTransferReady
    (d : PeriodicFluctuationTransferData) : Prop :=
  hasPeriodCount d ∧ fluctuationWindowControlled d

def periodicFluctuationTransferBudget
    (d : PeriodicFluctuationTransferData) : ℕ :=
  d.periodCount + d.fluctuationWindow + d.transferSlack

theorem periodicFluctuationTransferReady.hasPeriodCount
    {d : PeriodicFluctuationTransferData}
    (h : periodicFluctuationTransferReady d) :
    hasPeriodCount d ∧ fluctuationWindowControlled d ∧
      d.fluctuationWindow ≤ periodicFluctuationTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold periodicFluctuationTransferBudget
  omega

theorem fluctuationWindow_le_budget
    (d : PeriodicFluctuationTransferData) :
    d.fluctuationWindow ≤ periodicFluctuationTransferBudget d := by
  unfold periodicFluctuationTransferBudget
  omega

def samplePeriodicFluctuationTransferData :
    PeriodicFluctuationTransferData :=
  { periodCount := 6, fluctuationWindow := 8, transferSlack := 3 }

example : periodicFluctuationTransferReady
    samplePeriodicFluctuationTransferData := by
  norm_num [periodicFluctuationTransferReady, hasPeriodCount]
  norm_num
    [fluctuationWindowControlled, samplePeriodicFluctuationTransferData]

example :
    periodicFluctuationTransferBudget
      samplePeriodicFluctuationTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for periodic fluctuation transfer data. -/
def periodicFluctuationTransferDataListReady
    (data : List PeriodicFluctuationTransferData) : Bool :=
  data.all fun d =>
    0 < d.periodCount && d.fluctuationWindow ≤ d.periodCount + d.transferSlack

theorem periodicFluctuationTransferDataList_readyWindow :
    periodicFluctuationTransferDataListReady
      [{ periodCount := 4, fluctuationWindow := 5, transferSlack := 1 },
       { periodCount := 6, fluctuationWindow := 8, transferSlack := 3 }] =
      true := by
  unfold periodicFluctuationTransferDataListReady
  native_decide

/-- A certificate window for periodic fluctuation transfer. -/
structure PeriodicFluctuationTransferCertificateWindow where
  periodWindow : ℕ
  fluctuationWindow : ℕ
  transferSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The fluctuation window is controlled by the period window. -/
def periodicFluctuationTransferCertificateControlled
    (w : PeriodicFluctuationTransferCertificateWindow) : Prop :=
  w.fluctuationWindow ≤ w.periodWindow + w.transferSlack + w.slack

/-- Readiness for a periodic fluctuation transfer certificate. -/
def periodicFluctuationTransferCertificateReady
    (w : PeriodicFluctuationTransferCertificateWindow) : Prop :=
  0 < w.periodWindow ∧
    periodicFluctuationTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.periodWindow + w.fluctuationWindow + w.slack

/-- Total size of a periodic fluctuation transfer certificate. -/
def periodicFluctuationTransferCertificate
    (w : PeriodicFluctuationTransferCertificateWindow) : ℕ :=
  w.periodWindow + w.fluctuationWindow + w.transferSlack +
    w.certificateBudget + w.slack

theorem periodicFluctuationTransferCertificate_budget_le_certificate
    (w : PeriodicFluctuationTransferCertificateWindow)
    (h : periodicFluctuationTransferCertificateReady w) :
    w.certificateBudget ≤ periodicFluctuationTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold periodicFluctuationTransferCertificate
  omega

def samplePeriodicFluctuationTransferCertificateWindow :
    PeriodicFluctuationTransferCertificateWindow where
  periodWindow := 6
  fluctuationWindow := 7
  transferSlack := 2
  certificateBudget := 12
  slack := 1

example :
    periodicFluctuationTransferCertificateReady
      samplePeriodicFluctuationTransferCertificateWindow := by
  norm_num [periodicFluctuationTransferCertificateReady,
    periodicFluctuationTransferCertificateControlled,
    samplePeriodicFluctuationTransferCertificateWindow]

example :
    samplePeriodicFluctuationTransferCertificateWindow.certificateBudget ≤
      periodicFluctuationTransferCertificate
        samplePeriodicFluctuationTransferCertificateWindow := by
  apply periodicFluctuationTransferCertificate_budget_le_certificate
  norm_num [periodicFluctuationTransferCertificateReady,
    periodicFluctuationTransferCertificateControlled,
    samplePeriodicFluctuationTransferCertificateWindow]

structure PeriodicFluctuationTransferRefinementCertificate where
  periodWindow : ℕ
  fluctuationWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicFluctuationTransferRefinementCertificate.fluctuationControlled
    (c : PeriodicFluctuationTransferRefinementCertificate) : Prop :=
  c.fluctuationWindow ≤ c.periodWindow + c.transferSlackWindow + c.slack

def PeriodicFluctuationTransferRefinementCertificate.certificateBudgetControlled
    (c : PeriodicFluctuationTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.periodWindow + c.fluctuationWindow + c.transferSlackWindow + c.slack

def periodicFluctuationTransferRefinementReady
    (c : PeriodicFluctuationTransferRefinementCertificate) : Prop :=
  0 < c.periodWindow ∧ c.fluctuationControlled ∧ c.certificateBudgetControlled

def PeriodicFluctuationTransferRefinementCertificate.size
    (c : PeriodicFluctuationTransferRefinementCertificate) : ℕ :=
  c.periodWindow + c.fluctuationWindow + c.transferSlackWindow + c.slack

theorem periodicFluctuationTransfer_certificateBudgetWindow_le_size
    {c : PeriodicFluctuationTransferRefinementCertificate}
    (h : periodicFluctuationTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def samplePeriodicFluctuationTransferRefinementCertificate :
    PeriodicFluctuationTransferRefinementCertificate :=
  { periodWindow := 6, fluctuationWindow := 7, transferSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : periodicFluctuationTransferRefinementReady
    samplePeriodicFluctuationTransferRefinementCertificate := by
  norm_num [periodicFluctuationTransferRefinementReady,
    PeriodicFluctuationTransferRefinementCertificate.fluctuationControlled,
    PeriodicFluctuationTransferRefinementCertificate.certificateBudgetControlled,
    samplePeriodicFluctuationTransferRefinementCertificate]

example :
    samplePeriodicFluctuationTransferRefinementCertificate.certificateBudgetWindow ≤
      samplePeriodicFluctuationTransferRefinementCertificate.size := by
  norm_num [PeriodicFluctuationTransferRefinementCertificate.size,
    samplePeriodicFluctuationTransferRefinementCertificate]

structure PeriodicFluctuationTransferBudgetCertificate where
  periodWindow : ℕ
  fluctuationWindow : ℕ
  transferSlackWindow : ℕ
  fluctuationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicFluctuationTransferBudgetCertificate.controlled
    (c : PeriodicFluctuationTransferBudgetCertificate) : Prop :=
  0 < c.periodWindow ∧
    c.fluctuationWindow ≤ c.periodWindow + c.transferSlackWindow + c.slack ∧
      c.fluctuationBudgetWindow ≤
        c.periodWindow + c.fluctuationWindow + c.transferSlackWindow + c.slack

def PeriodicFluctuationTransferBudgetCertificate.budgetControlled
    (c : PeriodicFluctuationTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.periodWindow + c.fluctuationWindow + c.transferSlackWindow +
      c.fluctuationBudgetWindow + c.slack

def PeriodicFluctuationTransferBudgetCertificate.Ready
    (c : PeriodicFluctuationTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PeriodicFluctuationTransferBudgetCertificate.size
    (c : PeriodicFluctuationTransferBudgetCertificate) : ℕ :=
  c.periodWindow + c.fluctuationWindow + c.transferSlackWindow +
    c.fluctuationBudgetWindow + c.slack

theorem periodicFluctuationTransfer_budgetCertificate_le_size
    (c : PeriodicFluctuationTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePeriodicFluctuationTransferBudgetCertificate :
    PeriodicFluctuationTransferBudgetCertificate :=
  { periodWindow := 6
    fluctuationWindow := 7
    transferSlackWindow := 2
    fluctuationBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : samplePeriodicFluctuationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.controlled,
      samplePeriodicFluctuationTransferBudgetCertificate]
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationTransferBudgetCertificate]

example :
    samplePeriodicFluctuationTransferBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicFluctuationTransferBudgetCertificate.size := by
  apply periodicFluctuationTransfer_budgetCertificate_le_size
  constructor
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.controlled,
      samplePeriodicFluctuationTransferBudgetCertificate]
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePeriodicFluctuationTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.controlled,
      samplePeriodicFluctuationTransferBudgetCertificate]
  · norm_num [PeriodicFluctuationTransferBudgetCertificate.budgetControlled,
      samplePeriodicFluctuationTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePeriodicFluctuationTransferBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicFluctuationTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PeriodicFluctuationTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePeriodicFluctuationTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePeriodicFluctuationTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.PeriodicFluctuationTransferWindows
