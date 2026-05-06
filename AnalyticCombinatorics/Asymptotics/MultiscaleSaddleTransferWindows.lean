import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiscale saddle transfer windows.

This module records finite bookkeeping for multiscale saddle transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.MultiscaleSaddleTransferWindows

structure MultiscaleSaddleTransferData where
  saddleScale : ℕ
  transferWindow : ℕ
  multiscaleSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleScale (d : MultiscaleSaddleTransferData) : Prop :=
  0 < d.saddleScale

def transferWindowControlled (d : MultiscaleSaddleTransferData) : Prop :=
  d.transferWindow ≤ d.saddleScale + d.multiscaleSlack

def multiscaleSaddleTransferReady
    (d : MultiscaleSaddleTransferData) : Prop :=
  hasSaddleScale d ∧ transferWindowControlled d

def multiscaleSaddleTransferBudget
    (d : MultiscaleSaddleTransferData) : ℕ :=
  d.saddleScale + d.transferWindow + d.multiscaleSlack

theorem multiscaleSaddleTransferReady.hasSaddleScale
    {d : MultiscaleSaddleTransferData}
    (h : multiscaleSaddleTransferReady d) :
    hasSaddleScale d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ multiscaleSaddleTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold multiscaleSaddleTransferBudget
  omega

theorem transferWindow_le_budget (d : MultiscaleSaddleTransferData) :
    d.transferWindow ≤ multiscaleSaddleTransferBudget d := by
  unfold multiscaleSaddleTransferBudget
  omega

def sampleMultiscaleSaddleTransferData : MultiscaleSaddleTransferData :=
  { saddleScale := 7, transferWindow := 9, multiscaleSlack := 3 }

example : multiscaleSaddleTransferReady sampleMultiscaleSaddleTransferData := by
  norm_num [multiscaleSaddleTransferReady, hasSaddleScale]
  norm_num [transferWindowControlled, sampleMultiscaleSaddleTransferData]

example : multiscaleSaddleTransferBudget sampleMultiscaleSaddleTransferData = 19 := by
  native_decide

/-- Finite executable readiness audit for multiscale saddle-transfer data. -/
def multiscaleSaddleTransferDataListReady
    (data : List MultiscaleSaddleTransferData) : Bool :=
  data.all fun d =>
    0 < d.saddleScale && d.transferWindow ≤ d.saddleScale + d.multiscaleSlack

theorem multiscaleSaddleTransferDataList_readyWindow :
    multiscaleSaddleTransferDataListReady
      [{ saddleScale := 4, transferWindow := 5, multiscaleSlack := 1 },
       { saddleScale := 7, transferWindow := 9, multiscaleSlack := 3 }] = true := by
  unfold multiscaleSaddleTransferDataListReady
  native_decide

/-- A certificate window for multiscale saddle transfer. -/
structure MultiscaleSaddleTransferCertificateWindow where
  saddleWindow : ℕ
  transferWindow : ℕ
  multiscaleSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by saddle scale and slack. -/
def multiscaleSaddleTransferCertificateControlled
    (w : MultiscaleSaddleTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.saddleWindow + w.multiscaleSlack + w.slack

/-- Readiness for a multiscale saddle transfer certificate. -/
def multiscaleSaddleTransferCertificateReady
    (w : MultiscaleSaddleTransferCertificateWindow) : Prop :=
  0 < w.saddleWindow ∧
    multiscaleSaddleTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.saddleWindow + w.transferWindow + w.slack

/-- Total size of a multiscale saddle transfer certificate. -/
def multiscaleSaddleTransferCertificate
    (w : MultiscaleSaddleTransferCertificateWindow) : ℕ :=
  w.saddleWindow + w.transferWindow + w.multiscaleSlack + w.certificateBudget + w.slack

theorem multiscaleSaddleTransferCertificate_budget_le_certificate
    (w : MultiscaleSaddleTransferCertificateWindow)
    (h : multiscaleSaddleTransferCertificateReady w) :
    w.certificateBudget ≤ multiscaleSaddleTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold multiscaleSaddleTransferCertificate
  omega

def sampleMultiscaleSaddleTransferCertificateWindow :
    MultiscaleSaddleTransferCertificateWindow where
  saddleWindow := 7
  transferWindow := 8
  multiscaleSlack := 2
  certificateBudget := 14
  slack := 1

example :
    multiscaleSaddleTransferCertificateReady
      sampleMultiscaleSaddleTransferCertificateWindow := by
  norm_num [multiscaleSaddleTransferCertificateReady,
    multiscaleSaddleTransferCertificateControlled,
    sampleMultiscaleSaddleTransferCertificateWindow]

example :
    sampleMultiscaleSaddleTransferCertificateWindow.certificateBudget ≤
      multiscaleSaddleTransferCertificate
        sampleMultiscaleSaddleTransferCertificateWindow := by
  apply multiscaleSaddleTransferCertificate_budget_le_certificate
  norm_num [multiscaleSaddleTransferCertificateReady,
    multiscaleSaddleTransferCertificateControlled,
    sampleMultiscaleSaddleTransferCertificateWindow]

structure MultiscaleSaddleTransferRefinementCertificate where
  saddleWindow : ℕ
  transferWindow : ℕ
  multiscaleSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleSaddleTransferRefinementCertificate.transferControlled
    (c : MultiscaleSaddleTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.saddleWindow + c.multiscaleSlackWindow + c.slack

def MultiscaleSaddleTransferRefinementCertificate.certificateBudgetControlled
    (c : MultiscaleSaddleTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.transferWindow + c.multiscaleSlackWindow + c.slack

def multiscaleSaddleTransferRefinementReady
    (c : MultiscaleSaddleTransferRefinementCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def MultiscaleSaddleTransferRefinementCertificate.size
    (c : MultiscaleSaddleTransferRefinementCertificate) : ℕ :=
  c.saddleWindow + c.transferWindow + c.multiscaleSlackWindow + c.slack

theorem multiscaleSaddleTransfer_certificateBudgetWindow_le_size
    {c : MultiscaleSaddleTransferRefinementCertificate}
    (h : multiscaleSaddleTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMultiscaleSaddleTransferRefinementCertificate :
    MultiscaleSaddleTransferRefinementCertificate :=
  { saddleWindow := 7, transferWindow := 8, multiscaleSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : multiscaleSaddleTransferRefinementReady
    sampleMultiscaleSaddleTransferRefinementCertificate := by
  norm_num [multiscaleSaddleTransferRefinementReady,
    MultiscaleSaddleTransferRefinementCertificate.transferControlled,
    MultiscaleSaddleTransferRefinementCertificate.certificateBudgetControlled,
    sampleMultiscaleSaddleTransferRefinementCertificate]

example :
    sampleMultiscaleSaddleTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleMultiscaleSaddleTransferRefinementCertificate.size := by
  norm_num [MultiscaleSaddleTransferRefinementCertificate.size,
    sampleMultiscaleSaddleTransferRefinementCertificate]

structure MultiscaleSaddleTransferBudgetCertificate where
  saddleWindow : ℕ
  transferWindow : ℕ
  multiscaleSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleSaddleTransferBudgetCertificate.controlled
    (c : MultiscaleSaddleTransferBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.transferWindow ≤ c.saddleWindow + c.multiscaleSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.saddleWindow + c.transferWindow + c.multiscaleSlackWindow + c.slack

def MultiscaleSaddleTransferBudgetCertificate.budgetControlled
    (c : MultiscaleSaddleTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.transferWindow + c.multiscaleSlackWindow +
      c.transferBudgetWindow + c.slack

def MultiscaleSaddleTransferBudgetCertificate.Ready
    (c : MultiscaleSaddleTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultiscaleSaddleTransferBudgetCertificate.size
    (c : MultiscaleSaddleTransferBudgetCertificate) : ℕ :=
  c.saddleWindow + c.transferWindow + c.multiscaleSlackWindow +
    c.transferBudgetWindow + c.slack

theorem multiscaleSaddleTransfer_budgetCertificate_le_size
    (c : MultiscaleSaddleTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultiscaleSaddleTransferBudgetCertificate :
    MultiscaleSaddleTransferBudgetCertificate :=
  { saddleWindow := 7
    transferWindow := 8
    multiscaleSlackWindow := 2
    transferBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleMultiscaleSaddleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.controlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]

example :
    sampleMultiscaleSaddleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleSaddleTransferBudgetCertificate.size := by
  apply multiscaleSaddleTransfer_budgetCertificate_le_size
  constructor
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.controlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultiscaleSaddleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.controlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]
  · norm_num [MultiscaleSaddleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleSaddleTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultiscaleSaddleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleSaddleTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultiscaleSaddleTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultiscaleSaddleTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultiscaleSaddleTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MultiscaleSaddleTransferWindows
