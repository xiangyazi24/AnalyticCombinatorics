import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform local expansion windows.

This module isolates arithmetic bookkeeping for local expansions: a positive
local radius controls expansion order with explicit remainder slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformLocalExpansionWindows

structure LocalExpansionData where
  localRadius : ℕ
  expansionOrder : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def hasLocalRadius (d : LocalExpansionData) : Prop :=
  0 < d.localRadius

def expansionOrderControlled (d : LocalExpansionData) : Prop :=
  d.expansionOrder ≤ d.localRadius + d.remainderSlack

def localExpansionReady (d : LocalExpansionData) : Prop :=
  hasLocalRadius d ∧ expansionOrderControlled d

def localExpansionBudget (d : LocalExpansionData) : ℕ :=
  d.localRadius + d.expansionOrder + d.remainderSlack

theorem localExpansionReady.hasLocalRadius {d : LocalExpansionData}
    (h : localExpansionReady d) :
    hasLocalRadius d ∧ expansionOrderControlled d ∧ d.expansionOrder ≤ localExpansionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold localExpansionBudget
  omega

theorem expansionOrder_le_budget (d : LocalExpansionData) :
    d.expansionOrder ≤ localExpansionBudget d := by
  unfold localExpansionBudget
  omega

def sampleLocalExpansionData : LocalExpansionData :=
  { localRadius := 6, expansionOrder := 8, remainderSlack := 3 }

example : localExpansionReady sampleLocalExpansionData := by
  norm_num [localExpansionReady, hasLocalRadius]
  norm_num [expansionOrderControlled, sampleLocalExpansionData]

example : localExpansionBudget sampleLocalExpansionData = 17 := by
  native_decide

/-- Finite executable readiness audit for local expansion data. -/
def localExpansionDataListReady (data : List LocalExpansionData) : Bool :=
  data.all fun d =>
    0 < d.localRadius && d.expansionOrder ≤ d.localRadius + d.remainderSlack

theorem localExpansionDataList_readyWindow :
    localExpansionDataListReady
      [{ localRadius := 4, expansionOrder := 5, remainderSlack := 1 },
       { localRadius := 6, expansionOrder := 8, remainderSlack := 3 }] = true := by
  unfold localExpansionDataListReady
  native_decide

structure LocalExpansionCertificateWindow where
  radiusWindow : ℕ
  expansionWindow : ℕ
  remainderSlack : ℕ
  expansionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalExpansionCertificateWindow.expansionControlled
    (w : LocalExpansionCertificateWindow) : Prop :=
  w.expansionWindow ≤ w.radiusWindow + w.remainderSlack + w.slack

def localExpansionCertificateReady
    (w : LocalExpansionCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧ w.expansionControlled ∧
    w.expansionBudget ≤ w.radiusWindow + w.expansionWindow + w.slack

def LocalExpansionCertificateWindow.certificate
    (w : LocalExpansionCertificateWindow) : ℕ :=
  w.radiusWindow + w.expansionWindow + w.remainderSlack + w.expansionBudget + w.slack

theorem localExpansion_budget_le_certificate
    (w : LocalExpansionCertificateWindow) :
    w.expansionBudget ≤ w.certificate := by
  unfold LocalExpansionCertificateWindow.certificate
  omega

def sampleLocalExpansionCertificateWindow :
    LocalExpansionCertificateWindow :=
  { radiusWindow := 5, expansionWindow := 7, remainderSlack := 2,
    expansionBudget := 14, slack := 2 }

example : localExpansionCertificateReady
    sampleLocalExpansionCertificateWindow := by
  norm_num [localExpansionCertificateReady,
    LocalExpansionCertificateWindow.expansionControlled,
    sampleLocalExpansionCertificateWindow]

structure LocalExpansionRefinementCertificate where
  radiusWindow : ℕ
  expansionWindow : ℕ
  remainderSlackWindow : ℕ
  expansionBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalExpansionRefinementCertificate.expansionControlled
    (c : LocalExpansionRefinementCertificate) : Prop :=
  c.expansionWindow ≤ c.radiusWindow + c.remainderSlackWindow + c.slack

def LocalExpansionRefinementCertificate.expansionBudgetControlled
    (c : LocalExpansionRefinementCertificate) : Prop :=
  c.expansionBudgetWindow ≤
    c.radiusWindow + c.expansionWindow + c.remainderSlackWindow + c.slack

def localExpansionRefinementReady
    (c : LocalExpansionRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.expansionControlled ∧
    c.expansionBudgetControlled

def LocalExpansionRefinementCertificate.size
    (c : LocalExpansionRefinementCertificate) : ℕ :=
  c.radiusWindow + c.expansionWindow + c.remainderSlackWindow + c.slack

theorem localExpansion_expansionBudgetWindow_le_size
    {c : LocalExpansionRefinementCertificate}
    (h : localExpansionRefinementReady c) :
    c.expansionBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleLocalExpansionRefinementCertificate :
    LocalExpansionRefinementCertificate :=
  { radiusWindow := 5, expansionWindow := 7, remainderSlackWindow := 2,
    expansionBudgetWindow := 14, slack := 2 }

example : localExpansionRefinementReady
    sampleLocalExpansionRefinementCertificate := by
  norm_num [localExpansionRefinementReady,
    LocalExpansionRefinementCertificate.expansionControlled,
    LocalExpansionRefinementCertificate.expansionBudgetControlled,
    sampleLocalExpansionRefinementCertificate]

example :
    sampleLocalExpansionRefinementCertificate.expansionBudgetWindow ≤
      sampleLocalExpansionRefinementCertificate.size := by
  norm_num [LocalExpansionRefinementCertificate.size,
    sampleLocalExpansionRefinementCertificate]

/-- A second-stage certificate with the local-expansion budget separated from size. -/
structure LocalExpansionBudgetCertificate where
  radiusWindow : ℕ
  expansionWindow : ℕ
  remainderSlackWindow : ℕ
  expansionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LocalExpansionBudgetCertificate.expansionControlled
    (cert : LocalExpansionBudgetCertificate) : Prop :=
  0 < cert.radiusWindow ∧
    cert.expansionWindow ≤ cert.radiusWindow + cert.remainderSlackWindow + cert.slack ∧
      cert.expansionBudgetWindow ≤
        cert.radiusWindow + cert.expansionWindow + cert.remainderSlackWindow + cert.slack

def LocalExpansionBudgetCertificate.budgetControlled
    (cert : LocalExpansionBudgetCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.radiusWindow + cert.expansionWindow + cert.remainderSlackWindow +
      cert.expansionBudgetWindow + cert.slack

def localExpansionBudgetReady (cert : LocalExpansionBudgetCertificate) : Prop :=
  cert.expansionControlled ∧ cert.budgetControlled

def LocalExpansionBudgetCertificate.size
    (cert : LocalExpansionBudgetCertificate) : ℕ :=
  cert.radiusWindow + cert.expansionWindow + cert.remainderSlackWindow +
    cert.expansionBudgetWindow + cert.slack

theorem localExpansion_certificateBudgetWindow_le_size
    (cert : LocalExpansionBudgetCertificate)
    (h : localExpansionBudgetReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLocalExpansionBudgetCertificate :
    LocalExpansionBudgetCertificate :=
  { radiusWindow := 5, expansionWindow := 7, remainderSlackWindow := 2,
    expansionBudgetWindow := 14, certificateBudgetWindow := 30, slack := 2 }

example : localExpansionBudgetReady sampleLocalExpansionBudgetCertificate := by
  norm_num [localExpansionBudgetReady,
    LocalExpansionBudgetCertificate.expansionControlled,
    LocalExpansionBudgetCertificate.budgetControlled,
    sampleLocalExpansionBudgetCertificate]

example :
    sampleLocalExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalExpansionBudgetCertificate.size := by
  apply localExpansion_certificateBudgetWindow_le_size
  norm_num [localExpansionBudgetReady,
    LocalExpansionBudgetCertificate.expansionControlled,
    LocalExpansionBudgetCertificate.budgetControlled,
    sampleLocalExpansionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    localExpansionBudgetReady sampleLocalExpansionBudgetCertificate := by
  constructor
  · norm_num [LocalExpansionBudgetCertificate.expansionControlled,
      sampleLocalExpansionBudgetCertificate]
  · norm_num [LocalExpansionBudgetCertificate.budgetControlled,
      sampleLocalExpansionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLocalExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleLocalExpansionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LocalExpansionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLocalExpansionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLocalExpansionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformLocalExpansionWindows
