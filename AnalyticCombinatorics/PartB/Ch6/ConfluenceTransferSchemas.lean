import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Confluence transfer schemas.

The schema records finite data for combining local transfer windows near
coalescing singular behaviours.
-/

namespace AnalyticCombinatorics.PartB.Ch6.ConfluenceTransferSchemas

structure ConfluenceTransferData where
  localWindows : ℕ
  confluenceOrder : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveConfluenceOrder (d : ConfluenceTransferData) : Prop :=
  0 < d.confluenceOrder

def localWindowsControlled (d : ConfluenceTransferData) : Prop :=
  d.localWindows ≤ d.confluenceOrder + d.errorBudget

def confluenceTransferReady (d : ConfluenceTransferData) : Prop :=
  positiveConfluenceOrder d ∧ localWindowsControlled d

def confluenceTransferBudget (d : ConfluenceTransferData) : ℕ :=
  d.localWindows + d.confluenceOrder + d.errorBudget

theorem confluenceTransferReady.order {d : ConfluenceTransferData}
    (h : confluenceTransferReady d) :
    positiveConfluenceOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem localWindows_le_confluenceBudget (d : ConfluenceTransferData) :
    d.localWindows ≤ confluenceTransferBudget d := by
  unfold confluenceTransferBudget
  omega

def sampleConfluenceTransferData : ConfluenceTransferData :=
  { localWindows := 7, confluenceOrder := 5, errorBudget := 3 }

example : confluenceTransferReady sampleConfluenceTransferData := by
  norm_num [confluenceTransferReady, positiveConfluenceOrder]
  norm_num [localWindowsControlled, sampleConfluenceTransferData]

example : confluenceTransferBudget sampleConfluenceTransferData = 15 := by
  native_decide

structure ConfluenceTransferWindow where
  localWindows : ℕ
  confluenceOrder : ℕ
  errorBudget : ℕ
  matchingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConfluenceTransferWindow.localControlled (w : ConfluenceTransferWindow) : Prop :=
  w.localWindows ≤ w.confluenceOrder + w.errorBudget + w.slack

def ConfluenceTransferWindow.matchingControlled (w : ConfluenceTransferWindow) : Prop :=
  w.matchingBudget ≤ w.localWindows + w.confluenceOrder + w.errorBudget + w.slack

def confluenceTransferWindowReady (w : ConfluenceTransferWindow) : Prop :=
  0 < w.confluenceOrder ∧
    w.localControlled ∧
    w.matchingControlled

def ConfluenceTransferWindow.certificate (w : ConfluenceTransferWindow) : ℕ :=
  w.localWindows + w.confluenceOrder + w.errorBudget + w.slack

theorem confluenceTransfer_matchingBudget_le_certificate {w : ConfluenceTransferWindow}
    (h : confluenceTransferWindowReady w) :
    w.matchingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hmatching⟩
  exact hmatching

def sampleConfluenceTransferWindow : ConfluenceTransferWindow :=
  { localWindows := 7, confluenceOrder := 5, errorBudget := 3, matchingBudget := 14,
    slack := 0 }

example : confluenceTransferWindowReady sampleConfluenceTransferWindow := by
  norm_num [confluenceTransferWindowReady, ConfluenceTransferWindow.localControlled,
    ConfluenceTransferWindow.matchingControlled, sampleConfluenceTransferWindow]

example : sampleConfluenceTransferWindow.certificate = 15 := by
  native_decide


structure ConfluenceTransferSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConfluenceTransferSchemasBudgetCertificate.controlled
    (c : ConfluenceTransferSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConfluenceTransferSchemasBudgetCertificate.budgetControlled
    (c : ConfluenceTransferSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConfluenceTransferSchemasBudgetCertificate.Ready
    (c : ConfluenceTransferSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConfluenceTransferSchemasBudgetCertificate.size
    (c : ConfluenceTransferSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem confluenceTransferSchemas_budgetCertificate_le_size
    (c : ConfluenceTransferSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConfluenceTransferSchemasBudgetCertificate :
    ConfluenceTransferSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleConfluenceTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.controlled,
      sampleConfluenceTransferSchemasBudgetCertificate]
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.budgetControlled,
      sampleConfluenceTransferSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConfluenceTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConfluenceTransferSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleConfluenceTransferSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.controlled,
      sampleConfluenceTransferSchemasBudgetCertificate]
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.budgetControlled,
      sampleConfluenceTransferSchemasBudgetCertificate]

example :
    sampleConfluenceTransferSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleConfluenceTransferSchemasBudgetCertificate.size := by
  apply confluenceTransferSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.controlled,
      sampleConfluenceTransferSchemasBudgetCertificate]
  · norm_num [ConfluenceTransferSchemasBudgetCertificate.budgetControlled,
      sampleConfluenceTransferSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ConfluenceTransferSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConfluenceTransferSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConfluenceTransferSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.ConfluenceTransferSchemas
