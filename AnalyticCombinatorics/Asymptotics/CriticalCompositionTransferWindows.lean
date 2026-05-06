import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Critical composition transfer windows.

This module records finite bookkeeping for critical composition transfer.
-/

namespace AnalyticCombinatorics.Asymptotics.CriticalCompositionTransferWindows

structure CriticalCompositionTransferData where
  criticalScale : ℕ
  compositionWindow : ℕ
  transferSlack : ℕ
deriving DecidableEq, Repr

def hasCriticalScale (d : CriticalCompositionTransferData) : Prop :=
  0 < d.criticalScale

def compositionWindowControlled
    (d : CriticalCompositionTransferData) : Prop :=
  d.compositionWindow ≤ d.criticalScale + d.transferSlack

def criticalCompositionTransferReady
    (d : CriticalCompositionTransferData) : Prop :=
  hasCriticalScale d ∧ compositionWindowControlled d

def criticalCompositionTransferBudget
    (d : CriticalCompositionTransferData) : ℕ :=
  d.criticalScale + d.compositionWindow + d.transferSlack

theorem criticalCompositionTransferReady.hasCriticalScale
    {d : CriticalCompositionTransferData}
    (h : criticalCompositionTransferReady d) :
    hasCriticalScale d ∧ compositionWindowControlled d ∧
      d.compositionWindow ≤ criticalCompositionTransferBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold criticalCompositionTransferBudget
  omega

theorem compositionWindow_le_budget
    (d : CriticalCompositionTransferData) :
    d.compositionWindow ≤ criticalCompositionTransferBudget d := by
  unfold criticalCompositionTransferBudget
  omega

def sampleCriticalCompositionTransferData :
    CriticalCompositionTransferData :=
  { criticalScale := 6, compositionWindow := 8, transferSlack := 3 }

example : criticalCompositionTransferReady
    sampleCriticalCompositionTransferData := by
  norm_num [criticalCompositionTransferReady, hasCriticalScale]
  norm_num [compositionWindowControlled, sampleCriticalCompositionTransferData]

example :
    criticalCompositionTransferBudget
      sampleCriticalCompositionTransferData = 17 := by
  native_decide

/-- Finite executable readiness audit for critical composition transfer windows. -/
def criticalCompositionTransferListReady
    (windows : List CriticalCompositionTransferData) : Bool :=
  windows.all fun d =>
    0 < d.criticalScale &&
      d.compositionWindow ≤ d.criticalScale + d.transferSlack

theorem criticalCompositionTransferList_readyWindow :
    criticalCompositionTransferListReady
      [{ criticalScale := 4, compositionWindow := 5, transferSlack := 1 },
       { criticalScale := 6, compositionWindow := 8, transferSlack := 3 }] =
      true := by
  unfold criticalCompositionTransferListReady
  native_decide

/-- A certificate window for critical composition transfer. -/
structure CriticalCompositionTransferCertificateWindow where
  criticalWindow : ℕ
  compositionWindow : ℕ
  transferSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The composition window is controlled by critical scale and slack. -/
def criticalCompositionTransferCertificateControlled
    (w : CriticalCompositionTransferCertificateWindow) : Prop :=
  w.compositionWindow ≤ w.criticalWindow + w.transferSlack + w.slack

/-- Readiness for a critical composition transfer certificate. -/
def criticalCompositionTransferCertificateReady
    (w : CriticalCompositionTransferCertificateWindow) : Prop :=
  0 < w.criticalWindow ∧
    criticalCompositionTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.criticalWindow + w.compositionWindow + w.slack

/-- Total size of a critical composition transfer certificate. -/
def criticalCompositionTransferCertificate
    (w : CriticalCompositionTransferCertificateWindow) : ℕ :=
  w.criticalWindow + w.compositionWindow + w.transferSlack +
    w.certificateBudget + w.slack

theorem criticalCompositionTransferCertificate_budget_le_certificate
    (w : CriticalCompositionTransferCertificateWindow)
    (h : criticalCompositionTransferCertificateReady w) :
    w.certificateBudget ≤ criticalCompositionTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold criticalCompositionTransferCertificate
  omega

def sampleCriticalCompositionTransferCertificateWindow :
    CriticalCompositionTransferCertificateWindow where
  criticalWindow := 6
  compositionWindow := 7
  transferSlack := 2
  certificateBudget := 12
  slack := 1

example :
    criticalCompositionTransferCertificateReady
      sampleCriticalCompositionTransferCertificateWindow := by
  norm_num [criticalCompositionTransferCertificateReady,
    criticalCompositionTransferCertificateControlled,
    sampleCriticalCompositionTransferCertificateWindow]

example :
    sampleCriticalCompositionTransferCertificateWindow.certificateBudget ≤
      criticalCompositionTransferCertificate
        sampleCriticalCompositionTransferCertificateWindow := by
  apply criticalCompositionTransferCertificate_budget_le_certificate
  norm_num [criticalCompositionTransferCertificateReady,
    criticalCompositionTransferCertificateControlled,
    sampleCriticalCompositionTransferCertificateWindow]

structure CriticalCompositionTransferRefinementCertificate where
  criticalWindow : ℕ
  compositionWindow : ℕ
  transferSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalCompositionTransferRefinementCertificate.compositionControlled
    (c : CriticalCompositionTransferRefinementCertificate) : Prop :=
  c.compositionWindow ≤ c.criticalWindow + c.transferSlackWindow + c.slack

def CriticalCompositionTransferRefinementCertificate.certificateBudgetControlled
    (c : CriticalCompositionTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalWindow + c.compositionWindow + c.transferSlackWindow + c.slack

def criticalCompositionTransferRefinementReady
    (c : CriticalCompositionTransferRefinementCertificate) : Prop :=
  0 < c.criticalWindow ∧ c.compositionControlled ∧ c.certificateBudgetControlled

def CriticalCompositionTransferRefinementCertificate.size
    (c : CriticalCompositionTransferRefinementCertificate) : ℕ :=
  c.criticalWindow + c.compositionWindow + c.transferSlackWindow + c.slack

theorem criticalCompositionTransfer_certificateBudgetWindow_le_size
    {c : CriticalCompositionTransferRefinementCertificate}
    (h : criticalCompositionTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleCriticalCompositionTransferRefinementCertificate :
    CriticalCompositionTransferRefinementCertificate :=
  { criticalWindow := 6, compositionWindow := 7, transferSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : criticalCompositionTransferRefinementReady
    sampleCriticalCompositionTransferRefinementCertificate := by
  norm_num [criticalCompositionTransferRefinementReady,
    CriticalCompositionTransferRefinementCertificate.compositionControlled,
    CriticalCompositionTransferRefinementCertificate.certificateBudgetControlled,
    sampleCriticalCompositionTransferRefinementCertificate]

example :
    sampleCriticalCompositionTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleCriticalCompositionTransferRefinementCertificate.size := by
  norm_num [CriticalCompositionTransferRefinementCertificate.size,
    sampleCriticalCompositionTransferRefinementCertificate]

structure CriticalCompositionTransferBudgetCertificate where
  criticalWindow : ℕ
  compositionWindow : ℕ
  transferSlackWindow : ℕ
  compositionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CriticalCompositionTransferBudgetCertificate.controlled
    (c : CriticalCompositionTransferBudgetCertificate) : Prop :=
  0 < c.criticalWindow ∧
    c.compositionWindow ≤ c.criticalWindow + c.transferSlackWindow + c.slack ∧
      c.compositionBudgetWindow ≤
        c.criticalWindow + c.compositionWindow + c.transferSlackWindow + c.slack

def CriticalCompositionTransferBudgetCertificate.budgetControlled
    (c : CriticalCompositionTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalWindow + c.compositionWindow + c.transferSlackWindow +
      c.compositionBudgetWindow + c.slack

def CriticalCompositionTransferBudgetCertificate.Ready
    (c : CriticalCompositionTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CriticalCompositionTransferBudgetCertificate.size
    (c : CriticalCompositionTransferBudgetCertificate) : ℕ :=
  c.criticalWindow + c.compositionWindow + c.transferSlackWindow +
    c.compositionBudgetWindow + c.slack

theorem criticalCompositionTransfer_budgetCertificate_le_size
    (c : CriticalCompositionTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCriticalCompositionTransferBudgetCertificate :
    CriticalCompositionTransferBudgetCertificate :=
  { criticalWindow := 6
    compositionWindow := 7
    transferSlackWindow := 2
    compositionBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleCriticalCompositionTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalCompositionTransferBudgetCertificate.controlled,
      sampleCriticalCompositionTransferBudgetCertificate]
  · norm_num [CriticalCompositionTransferBudgetCertificate.budgetControlled,
      sampleCriticalCompositionTransferBudgetCertificate]

example :
    sampleCriticalCompositionTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalCompositionTransferBudgetCertificate.size := by
  apply criticalCompositionTransfer_budgetCertificate_le_size
  constructor
  · norm_num [CriticalCompositionTransferBudgetCertificate.controlled,
      sampleCriticalCompositionTransferBudgetCertificate]
  · norm_num [CriticalCompositionTransferBudgetCertificate.budgetControlled,
      sampleCriticalCompositionTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCriticalCompositionTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [CriticalCompositionTransferBudgetCertificate.controlled,
      sampleCriticalCompositionTransferBudgetCertificate]
  · norm_num [CriticalCompositionTransferBudgetCertificate.budgetControlled,
      sampleCriticalCompositionTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCriticalCompositionTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleCriticalCompositionTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CriticalCompositionTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCriticalCompositionTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCriticalCompositionTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.CriticalCompositionTransferWindows
