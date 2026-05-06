import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Boundary transfer windows.

The finite record stores boundary width, transfer scale, and remainder
slack.
-/

namespace AnalyticCombinatorics.Asymptotics.BoundaryTransferWindows

structure BoundaryTransferWindowData where
  boundaryWidth : ℕ
  transferScale : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def transferScalePositive (d : BoundaryTransferWindowData) : Prop :=
  0 < d.transferScale

def boundaryWidthControlled (d : BoundaryTransferWindowData) : Prop :=
  d.boundaryWidth ≤ d.transferScale + d.remainderSlack

def boundaryTransferWindowReady (d : BoundaryTransferWindowData) : Prop :=
  transferScalePositive d ∧ boundaryWidthControlled d

def boundaryTransferWindowBudget (d : BoundaryTransferWindowData) : ℕ :=
  d.boundaryWidth + d.transferScale + d.remainderSlack

theorem boundaryTransferWindowReady.scale
    {d : BoundaryTransferWindowData}
    (h : boundaryTransferWindowReady d) :
    transferScalePositive d ∧ boundaryWidthControlled d ∧
      d.boundaryWidth ≤ boundaryTransferWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold boundaryTransferWindowBudget
  omega

theorem boundaryWidth_le_transferWindowBudget
    (d : BoundaryTransferWindowData) :
    d.boundaryWidth ≤ boundaryTransferWindowBudget d := by
  unfold boundaryTransferWindowBudget
  omega

def sampleBoundaryTransferWindowData : BoundaryTransferWindowData :=
  { boundaryWidth := 7, transferScale := 5, remainderSlack := 3 }

example : boundaryTransferWindowReady sampleBoundaryTransferWindowData := by
  norm_num [boundaryTransferWindowReady, transferScalePositive]
  norm_num [boundaryWidthControlled, sampleBoundaryTransferWindowData]

example : boundaryTransferWindowBudget sampleBoundaryTransferWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for boundary transfer windows. -/
def boundaryTransferWindowListReady
    (windows : List BoundaryTransferWindowData) : Bool :=
  windows.all fun d =>
    0 < d.transferScale && d.boundaryWidth ≤ d.transferScale + d.remainderSlack

theorem boundaryTransferWindowList_readyWindow :
    boundaryTransferWindowListReady
      [{ boundaryWidth := 4, transferScale := 3, remainderSlack := 1 },
       { boundaryWidth := 7, transferScale := 5, remainderSlack := 3 }] = true := by
  unfold boundaryTransferWindowListReady
  native_decide

/-- A certificate window for boundary transfer estimates. -/
structure BoundaryTransferCertificateWindow where
  boundaryWindow : ℕ
  transferWindow : ℕ
  remainderSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The boundary window is controlled by transfer scale and slack. -/
def boundaryTransferCertificateControlled
    (w : BoundaryTransferCertificateWindow) : Prop :=
  w.boundaryWindow ≤ w.transferWindow + w.remainderSlack + w.slack

/-- Readiness for a boundary transfer certificate. -/
def boundaryTransferCertificateReady
    (w : BoundaryTransferCertificateWindow) : Prop :=
  0 < w.transferWindow ∧
    boundaryTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.boundaryWindow + w.transferWindow + w.slack

/-- Total size of a boundary transfer certificate. -/
def boundaryTransferCertificate
    (w : BoundaryTransferCertificateWindow) : ℕ :=
  w.boundaryWindow + w.transferWindow + w.remainderSlack + w.certificateBudget + w.slack

theorem boundaryTransferCertificate_budget_le_certificate
    (w : BoundaryTransferCertificateWindow)
    (h : boundaryTransferCertificateReady w) :
    w.certificateBudget ≤ boundaryTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold boundaryTransferCertificate
  omega

def sampleBoundaryTransferCertificateWindow :
    BoundaryTransferCertificateWindow where
  boundaryWindow := 6
  transferWindow := 7
  remainderSlack := 2
  certificateBudget := 12
  slack := 1

example :
    boundaryTransferCertificateReady
      sampleBoundaryTransferCertificateWindow := by
  norm_num [boundaryTransferCertificateReady,
    boundaryTransferCertificateControlled, sampleBoundaryTransferCertificateWindow]

example :
    sampleBoundaryTransferCertificateWindow.certificateBudget ≤
      boundaryTransferCertificate sampleBoundaryTransferCertificateWindow := by
  apply boundaryTransferCertificate_budget_le_certificate
  norm_num [boundaryTransferCertificateReady,
    boundaryTransferCertificateControlled, sampleBoundaryTransferCertificateWindow]

structure BoundaryTransferRefinementCertificate where
  boundaryWindow : ℕ
  transferWindow : ℕ
  remainderSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryTransferRefinementCertificate.boundaryControlled
    (c : BoundaryTransferRefinementCertificate) : Prop :=
  c.boundaryWindow ≤ c.transferWindow + c.remainderSlackWindow + c.slack

def BoundaryTransferRefinementCertificate.certificateBudgetControlled
    (c : BoundaryTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.boundaryWindow + c.transferWindow + c.remainderSlackWindow + c.slack

def boundaryTransferRefinementReady
    (c : BoundaryTransferRefinementCertificate) : Prop :=
  0 < c.transferWindow ∧ c.boundaryControlled ∧ c.certificateBudgetControlled

def BoundaryTransferRefinementCertificate.size
    (c : BoundaryTransferRefinementCertificate) : ℕ :=
  c.boundaryWindow + c.transferWindow + c.remainderSlackWindow + c.slack

theorem boundaryTransfer_certificateBudgetWindow_le_size
    {c : BoundaryTransferRefinementCertificate}
    (h : boundaryTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleBoundaryTransferRefinementCertificate :
    BoundaryTransferRefinementCertificate :=
  { boundaryWindow := 6, transferWindow := 7, remainderSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : boundaryTransferRefinementReady
    sampleBoundaryTransferRefinementCertificate := by
  norm_num [boundaryTransferRefinementReady,
    BoundaryTransferRefinementCertificate.boundaryControlled,
    BoundaryTransferRefinementCertificate.certificateBudgetControlled,
    sampleBoundaryTransferRefinementCertificate]

example :
    sampleBoundaryTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleBoundaryTransferRefinementCertificate.size := by
  norm_num [BoundaryTransferRefinementCertificate.size,
    sampleBoundaryTransferRefinementCertificate]

structure BoundaryTransferBudgetCertificate where
  boundaryWindow : ℕ
  transferWindow : ℕ
  remainderSlackWindow : ℕ
  boundaryBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryTransferBudgetCertificate.controlled
    (c : BoundaryTransferBudgetCertificate) : Prop :=
  0 < c.transferWindow ∧
    c.boundaryWindow ≤ c.transferWindow + c.remainderSlackWindow + c.slack ∧
      c.boundaryBudgetWindow ≤
        c.boundaryWindow + c.transferWindow + c.remainderSlackWindow + c.slack

def BoundaryTransferBudgetCertificate.budgetControlled
    (c : BoundaryTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.boundaryWindow + c.transferWindow + c.remainderSlackWindow +
      c.boundaryBudgetWindow + c.slack

def BoundaryTransferBudgetCertificate.Ready
    (c : BoundaryTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundaryTransferBudgetCertificate.size
    (c : BoundaryTransferBudgetCertificate) : ℕ :=
  c.boundaryWindow + c.transferWindow + c.remainderSlackWindow +
    c.boundaryBudgetWindow + c.slack

theorem boundaryTransfer_budgetCertificate_le_size
    (c : BoundaryTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundaryTransferBudgetCertificate :
    BoundaryTransferBudgetCertificate :=
  { boundaryWindow := 6
    transferWindow := 7
    remainderSlackWindow := 2
    boundaryBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleBoundaryTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryTransferBudgetCertificate.controlled,
      sampleBoundaryTransferBudgetCertificate]
  · norm_num [BoundaryTransferBudgetCertificate.budgetControlled,
      sampleBoundaryTransferBudgetCertificate]

example :
    sampleBoundaryTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryTransferBudgetCertificate.size := by
  apply boundaryTransfer_budgetCertificate_le_size
  constructor
  · norm_num [BoundaryTransferBudgetCertificate.controlled,
      sampleBoundaryTransferBudgetCertificate]
  · norm_num [BoundaryTransferBudgetCertificate.budgetControlled,
      sampleBoundaryTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBoundaryTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryTransferBudgetCertificate.controlled,
      sampleBoundaryTransferBudgetCertificate]
  · norm_num [BoundaryTransferBudgetCertificate.budgetControlled,
      sampleBoundaryTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBoundaryTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BoundaryTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundaryTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBoundaryTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.BoundaryTransferWindows
