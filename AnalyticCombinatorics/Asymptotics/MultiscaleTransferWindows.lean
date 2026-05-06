import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Multiscale transfer windows.

This module records finite bookkeeping for multiscale transfer: a positive
primary scale controls secondary scale count with transfer slack.
-/

namespace AnalyticCombinatorics.Asymptotics.MultiscaleTransferWindows

structure MultiscaleTransferData where
  primaryScale : ℕ
  secondaryScaleCount : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasPrimaryScale (d : MultiscaleTransferData) : Prop :=
  0 < d.primaryScale

def secondaryScaleControlled (d : MultiscaleTransferData) : Prop :=
  d.secondaryScaleCount ≤ d.primaryScale + d.transferSlack

def multiscaleTransferReady (d : MultiscaleTransferData) : Prop :=
  hasPrimaryScale d ∧ secondaryScaleControlled d

def multiscaleTransferBudget (d : MultiscaleTransferData) : ℕ :=
  d.primaryScale + d.secondaryScaleCount + d.transferSlack

theorem multiscaleTransferReady.hasPrimaryScale
    {d : MultiscaleTransferData}
    (h : multiscaleTransferReady d) :
    hasPrimaryScale d ∧ secondaryScaleControlled d ∧
      d.secondaryScaleCount ≤ multiscaleTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold multiscaleTransferBudget
  omega

theorem secondaryScaleCount_le_budget (d : MultiscaleTransferData) :
    d.secondaryScaleCount ≤ multiscaleTransferBudget d := by
  unfold multiscaleTransferBudget
  omega

def sampleMultiscaleTransferData : MultiscaleTransferData :=
  { primaryScale := 7, secondaryScaleCount := 9, transferSlack := 3 }

example : multiscaleTransferReady sampleMultiscaleTransferData := by
  norm_num [multiscaleTransferReady, hasPrimaryScale]
  norm_num [secondaryScaleControlled, sampleMultiscaleTransferData]

example : multiscaleTransferBudget sampleMultiscaleTransferData = 19 := by
  native_decide

/-- Finite executable readiness audit for multiscale transfer data. -/
def multiscaleTransferDataListReady
    (data : List MultiscaleTransferData) : Bool :=
  data.all fun d =>
    0 < d.primaryScale && d.secondaryScaleCount ≤ d.primaryScale + d.transferSlack

theorem multiscaleTransferDataList_readyWindow :
    multiscaleTransferDataListReady
      [{ primaryScale := 4, secondaryScaleCount := 5, transferSlack := 1 },
       { primaryScale := 7, secondaryScaleCount := 9, transferSlack := 3 }] = true := by
  unfold multiscaleTransferDataListReady
  native_decide

/-- A certificate window for multiscale transfer. -/
structure MultiscaleTransferCertificateWindow where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  transferSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Secondary scales are controlled by the primary scale. -/
def multiscaleTransferCertificateControlled
    (w : MultiscaleTransferCertificateWindow) : Prop :=
  w.secondaryWindow ≤ w.primaryWindow + w.transferSlack + w.slack

/-- Readiness for a multiscale transfer certificate. -/
def multiscaleTransferCertificateReady
    (w : MultiscaleTransferCertificateWindow) : Prop :=
  0 < w.primaryWindow ∧
    multiscaleTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.primaryWindow + w.secondaryWindow + w.slack

/-- Total size of a multiscale transfer certificate. -/
def multiscaleTransferCertificate
    (w : MultiscaleTransferCertificateWindow) : ℕ :=
  w.primaryWindow + w.secondaryWindow + w.transferSlack + w.certificateBudget + w.slack

theorem multiscaleTransferCertificate_budget_le_certificate
    (w : MultiscaleTransferCertificateWindow)
    (h : multiscaleTransferCertificateReady w) :
    w.certificateBudget ≤ multiscaleTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold multiscaleTransferCertificate
  omega

def sampleMultiscaleTransferCertificateWindow :
    MultiscaleTransferCertificateWindow where
  primaryWindow := 7
  secondaryWindow := 8
  transferSlack := 2
  certificateBudget := 14
  slack := 1

example :
    multiscaleTransferCertificateReady
      sampleMultiscaleTransferCertificateWindow := by
  norm_num [multiscaleTransferCertificateReady,
    multiscaleTransferCertificateControlled,
    sampleMultiscaleTransferCertificateWindow]

example :
    sampleMultiscaleTransferCertificateWindow.certificateBudget ≤
      multiscaleTransferCertificate sampleMultiscaleTransferCertificateWindow := by
  apply multiscaleTransferCertificate_budget_le_certificate
  norm_num [multiscaleTransferCertificateReady,
    multiscaleTransferCertificateControlled,
    sampleMultiscaleTransferCertificateWindow]

structure MultiscaleTransferRefinementCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleTransferRefinementCertificate.secondaryControlled
    (c : MultiscaleTransferRefinementCertificate) : Prop :=
  c.secondaryWindow ≤ c.primaryWindow + c.transferSlackWindow + c.slack

def MultiscaleTransferRefinementCertificate.certificateBudgetControlled
    (c : MultiscaleTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.primaryWindow + c.secondaryWindow + c.transferSlackWindow + c.slack

def multiscaleTransferRefinementReady
    (c : MultiscaleTransferRefinementCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryControlled ∧ c.certificateBudgetControlled

def MultiscaleTransferRefinementCertificate.size
    (c : MultiscaleTransferRefinementCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.transferSlackWindow + c.slack

theorem multiscaleTransfer_certificateBudgetWindow_le_size
    {c : MultiscaleTransferRefinementCertificate}
    (h : multiscaleTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleMultiscaleTransferRefinementCertificate :
    MultiscaleTransferRefinementCertificate :=
  { primaryWindow := 7, secondaryWindow := 8, transferSlackWindow := 2,
    certificateBudgetWindow := 18, slack := 1 }

example : multiscaleTransferRefinementReady
    sampleMultiscaleTransferRefinementCertificate := by
  norm_num [multiscaleTransferRefinementReady,
    MultiscaleTransferRefinementCertificate.secondaryControlled,
    MultiscaleTransferRefinementCertificate.certificateBudgetControlled,
    sampleMultiscaleTransferRefinementCertificate]

example :
    sampleMultiscaleTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleMultiscaleTransferRefinementCertificate.size := by
  norm_num [MultiscaleTransferRefinementCertificate.size,
    sampleMultiscaleTransferRefinementCertificate]

structure MultiscaleTransferBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  transferSlackWindow : ℕ
  transferBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MultiscaleTransferBudgetCertificate.controlled
    (c : MultiscaleTransferBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧
    c.secondaryWindow ≤ c.primaryWindow + c.transferSlackWindow + c.slack ∧
      c.transferBudgetWindow ≤
        c.primaryWindow + c.secondaryWindow + c.transferSlackWindow + c.slack

def MultiscaleTransferBudgetCertificate.budgetControlled
    (c : MultiscaleTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.primaryWindow + c.secondaryWindow + c.transferSlackWindow +
      c.transferBudgetWindow + c.slack

def MultiscaleTransferBudgetCertificate.Ready
    (c : MultiscaleTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MultiscaleTransferBudgetCertificate.size
    (c : MultiscaleTransferBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.transferSlackWindow +
    c.transferBudgetWindow + c.slack

theorem multiscaleTransfer_budgetCertificate_le_size
    (c : MultiscaleTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMultiscaleTransferBudgetCertificate :
    MultiscaleTransferBudgetCertificate :=
  { primaryWindow := 7
    secondaryWindow := 8
    transferSlackWindow := 2
    transferBudgetWindow := 18
    certificateBudgetWindow := 36
    slack := 1 }

example : sampleMultiscaleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleTransferBudgetCertificate.controlled,
      sampleMultiscaleTransferBudgetCertificate]
  · norm_num [MultiscaleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleTransferBudgetCertificate]

example :
    sampleMultiscaleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleTransferBudgetCertificate.size := by
  apply multiscaleTransfer_budgetCertificate_le_size
  constructor
  · norm_num [MultiscaleTransferBudgetCertificate.controlled,
      sampleMultiscaleTransferBudgetCertificate]
  · norm_num [MultiscaleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleMultiscaleTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [MultiscaleTransferBudgetCertificate.controlled,
      sampleMultiscaleTransferBudgetCertificate]
  · norm_num [MultiscaleTransferBudgetCertificate.budgetControlled,
      sampleMultiscaleTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleMultiscaleTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleMultiscaleTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MultiscaleTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMultiscaleTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleMultiscaleTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.MultiscaleTransferWindows
