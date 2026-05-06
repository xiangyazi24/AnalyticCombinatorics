import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic large powers transfer windows.

This module records finite bookkeeping for transfer estimates in large powers.
-/

namespace AnalyticCombinatorics.Asymptotics.AnalyticLargePowersTransferWindows

structure LargePowersTransferData where
  powerScale : ℕ
  transferWindow : ℕ
  powerSlack : ℕ
deriving DecidableEq, Repr

def hasPowerScale (d : LargePowersTransferData) : Prop :=
  0 < d.powerScale

def transferWindowControlled (d : LargePowersTransferData) : Prop :=
  d.transferWindow ≤ d.powerScale + d.powerSlack

def largePowersTransferReady (d : LargePowersTransferData) : Prop :=
  hasPowerScale d ∧ transferWindowControlled d

def largePowersTransferBudget (d : LargePowersTransferData) : ℕ :=
  d.powerScale + d.transferWindow + d.powerSlack

theorem largePowersTransferReady.hasPowerScale
    {d : LargePowersTransferData}
    (h : largePowersTransferReady d) :
    hasPowerScale d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ largePowersTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold largePowersTransferBudget
  omega

theorem transferWindow_le_budget (d : LargePowersTransferData) :
    d.transferWindow ≤ largePowersTransferBudget d := by
  unfold largePowersTransferBudget
  omega

def sampleLargePowersTransferData : LargePowersTransferData :=
  { powerScale := 7, transferWindow := 9, powerSlack := 3 }

example : largePowersTransferReady sampleLargePowersTransferData := by
  norm_num [largePowersTransferReady, hasPowerScale]
  norm_num [transferWindowControlled, sampleLargePowersTransferData]

example : largePowersTransferBudget sampleLargePowersTransferData = 19 := by
  native_decide

/-- Finite executable readiness audit for large-powers transfer windows. -/
def largePowersTransferListReady
    (windows : List LargePowersTransferData) : Bool :=
  windows.all fun d =>
    0 < d.powerScale && d.transferWindow ≤ d.powerScale + d.powerSlack

theorem largePowersTransferList_readyWindow :
    largePowersTransferListReady
      [{ powerScale := 4, transferWindow := 5, powerSlack := 1 },
       { powerScale := 7, transferWindow := 9, powerSlack := 3 }] = true := by
  unfold largePowersTransferListReady
  native_decide

/-- A local certificate window for large-powers transfer estimates. -/
structure LargePowersTransferCertificateWindow where
  powerWindow : ℕ
  transferWindow : ℕ
  powerSlack : ℕ
  transferBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by the power window and slack. -/
def largePowersTransferCertificateControlled
    (w : LargePowersTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.powerWindow + w.powerSlack + w.slack

/-- Readiness for the local certificate window. -/
def largePowersTransferCertificateReady
    (w : LargePowersTransferCertificateWindow) : Prop :=
  0 < w.powerWindow ∧
    largePowersTransferCertificateControlled w ∧
      w.transferBudget ≤ w.powerWindow + w.transferWindow + w.slack

/-- Total certificate size for a large-powers transfer window. -/
def largePowersTransferCertificate
    (w : LargePowersTransferCertificateWindow) : ℕ :=
  w.powerWindow + w.transferWindow + w.powerSlack + w.transferBudget + w.slack

theorem largePowersTransferCertificate_budget_le_certificate
    (w : LargePowersTransferCertificateWindow)
    (h : largePowersTransferCertificateReady w) :
    w.transferBudget ≤ largePowersTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold largePowersTransferCertificate
  omega

def sampleLargePowersTransferCertificateWindow :
    LargePowersTransferCertificateWindow where
  powerWindow := 8
  transferWindow := 9
  powerSlack := 2
  transferBudget := 16
  slack := 1

example :
    largePowersTransferCertificateReady
      sampleLargePowersTransferCertificateWindow := by
  norm_num [largePowersTransferCertificateReady,
    largePowersTransferCertificateControlled,
    sampleLargePowersTransferCertificateWindow]

example :
    sampleLargePowersTransferCertificateWindow.transferBudget ≤
      largePowersTransferCertificate sampleLargePowersTransferCertificateWindow := by
  apply largePowersTransferCertificate_budget_le_certificate
  norm_num [largePowersTransferCertificateReady,
    largePowersTransferCertificateControlled,
    sampleLargePowersTransferCertificateWindow]

structure LargePowersTransferRefinementCertificate where
  powerWindow : ℕ
  transferWindow : ℕ
  powerSlackWindow : ℕ
  transferBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargePowersTransferRefinementCertificate.transferControlled
    (c : LargePowersTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.powerWindow + c.powerSlackWindow + c.slack

def LargePowersTransferRefinementCertificate.transferBudgetControlled
    (c : LargePowersTransferRefinementCertificate) : Prop :=
  c.transferBudgetWindow ≤
    c.powerWindow + c.transferWindow + c.powerSlackWindow + c.slack

def largePowersTransferRefinementReady
    (c : LargePowersTransferRefinementCertificate) : Prop :=
  0 < c.powerWindow ∧ c.transferControlled ∧ c.transferBudgetControlled

def LargePowersTransferRefinementCertificate.size
    (c : LargePowersTransferRefinementCertificate) : ℕ :=
  c.powerWindow + c.transferWindow + c.powerSlackWindow + c.slack

theorem largePowersTransfer_transferBudgetWindow_le_size
    {c : LargePowersTransferRefinementCertificate}
    (h : largePowersTransferRefinementReady c) :
    c.transferBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleLargePowersTransferRefinementCertificate :
    LargePowersTransferRefinementCertificate :=
  { powerWindow := 8, transferWindow := 9, powerSlackWindow := 2,
    transferBudgetWindow := 20, slack := 1 }

example : largePowersTransferRefinementReady
    sampleLargePowersTransferRefinementCertificate := by
  norm_num [largePowersTransferRefinementReady,
    LargePowersTransferRefinementCertificate.transferControlled,
    LargePowersTransferRefinementCertificate.transferBudgetControlled,
    sampleLargePowersTransferRefinementCertificate]

example :
    sampleLargePowersTransferRefinementCertificate.transferBudgetWindow ≤
      sampleLargePowersTransferRefinementCertificate.size := by
  norm_num [LargePowersTransferRefinementCertificate.size,
    sampleLargePowersTransferRefinementCertificate]

structure LargePowersTransferBudgetCertificate where
  powerWindow : ℕ
  transferWindow : ℕ
  powerSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LargePowersTransferBudgetCertificate.controlled
    (c : LargePowersTransferBudgetCertificate) : Prop :=
  0 < c.powerWindow ∧
    c.transferWindow ≤ c.powerWindow + c.powerSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.powerWindow + c.transferWindow + c.powerSlackWindow + c.slack

def LargePowersTransferBudgetCertificate.budgetControlled
    (c : LargePowersTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.powerWindow + c.transferWindow + c.powerSlackWindow +
      c.transferBudgetWindow + c.slack

def LargePowersTransferBudgetCertificate.Ready
    (c : LargePowersTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LargePowersTransferBudgetCertificate.size
    (c : LargePowersTransferBudgetCertificate) : ℕ :=
  c.powerWindow + c.transferWindow + c.powerSlackWindow +
    c.transferBudgetWindow + c.slack

theorem largePowersTransfer_budgetCertificate_le_size
    (c : LargePowersTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLargePowersTransferBudgetCertificate :
    LargePowersTransferBudgetCertificate :=
  { powerWindow := 8
    transferWindow := 9
    powerSlackWindow := 2
    transferBudgetWindow := 20
    certificateBudgetWindow := 40
    slack := 1 }

example : sampleLargePowersTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersTransferBudgetCertificate.controlled,
      sampleLargePowersTransferBudgetCertificate]
  · norm_num [LargePowersTransferBudgetCertificate.budgetControlled,
      sampleLargePowersTransferBudgetCertificate]

example :
    sampleLargePowersTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersTransferBudgetCertificate.size := by
  apply largePowersTransfer_budgetCertificate_le_size
  constructor
  · norm_num [LargePowersTransferBudgetCertificate.controlled,
      sampleLargePowersTransferBudgetCertificate]
  · norm_num [LargePowersTransferBudgetCertificate.budgetControlled,
      sampleLargePowersTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLargePowersTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [LargePowersTransferBudgetCertificate.controlled,
      sampleLargePowersTransferBudgetCertificate]
  · norm_num [LargePowersTransferBudgetCertificate.budgetControlled,
      sampleLargePowersTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLargePowersTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleLargePowersTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LargePowersTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLargePowersTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLargePowersTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.AnalyticLargePowersTransferWindows
