import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Implicit transfer windows.

The finite record tracks implicit radius, transfer window, and error
budget for implicit singular transfer schemas.
-/

namespace AnalyticCombinatorics.Asymptotics.ImplicitTransferWindows

structure ImplicitTransferWindowData where
  implicitRadius : ℕ
  transferWindow : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def implicitRadiusPositive (d : ImplicitTransferWindowData) : Prop :=
  0 < d.implicitRadius

def transferWindowControlled (d : ImplicitTransferWindowData) : Prop :=
  d.transferWindow ≤ d.implicitRadius + d.errorBudget

def implicitTransferWindowReady (d : ImplicitTransferWindowData) : Prop :=
  implicitRadiusPositive d ∧ transferWindowControlled d

def implicitTransferWindowBudget (d : ImplicitTransferWindowData) : ℕ :=
  d.implicitRadius + d.transferWindow + d.errorBudget

theorem implicitTransferWindowReady.radius
    {d : ImplicitTransferWindowData}
    (h : implicitTransferWindowReady d) :
    implicitRadiusPositive d ∧ transferWindowControlled d ∧
      d.transferWindow ≤ implicitTransferWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold implicitTransferWindowBudget
  omega

theorem transferWindow_le_implicitTransferBudget
    (d : ImplicitTransferWindowData) :
    d.transferWindow ≤ implicitTransferWindowBudget d := by
  unfold implicitTransferWindowBudget
  omega

def sampleImplicitTransferWindowData : ImplicitTransferWindowData :=
  { implicitRadius := 5, transferWindow := 7, errorBudget := 3 }

example : implicitTransferWindowReady sampleImplicitTransferWindowData := by
  norm_num [implicitTransferWindowReady, implicitRadiusPositive]
  norm_num [transferWindowControlled, sampleImplicitTransferWindowData]

example :
    implicitTransferWindowBudget sampleImplicitTransferWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for implicit transfer window data. -/
def implicitTransferWindowDataListReady
    (data : List ImplicitTransferWindowData) : Bool :=
  data.all fun d =>
    0 < d.implicitRadius && d.transferWindow ≤ d.implicitRadius + d.errorBudget

theorem implicitTransferWindowDataList_readyWindow :
    implicitTransferWindowDataListReady
      [{ implicitRadius := 4, transferWindow := 5, errorBudget := 1 },
       { implicitRadius := 5, transferWindow := 7, errorBudget := 3 }] = true := by
  unfold implicitTransferWindowDataListReady
  native_decide

/-- A certificate window for implicit transfer estimates. -/
structure ImplicitTransferCertificateWindow where
  radiusWindow : ℕ
  transferWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The transfer window is controlled by radius and error windows. -/
def implicitTransferCertificateControlled
    (w : ImplicitTransferCertificateWindow) : Prop :=
  w.transferWindow ≤ w.radiusWindow + w.errorWindow + w.slack

/-- Readiness for an implicit transfer certificate. -/
def implicitTransferCertificateReady
    (w : ImplicitTransferCertificateWindow) : Prop :=
  0 < w.radiusWindow ∧
    implicitTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.radiusWindow + w.transferWindow + w.slack

/-- Total size of an implicit transfer certificate. -/
def implicitTransferCertificate
    (w : ImplicitTransferCertificateWindow) : ℕ :=
  w.radiusWindow + w.transferWindow + w.errorWindow + w.certificateBudget + w.slack

theorem implicitTransferCertificate_budget_le_certificate
    (w : ImplicitTransferCertificateWindow)
    (h : implicitTransferCertificateReady w) :
    w.certificateBudget ≤ implicitTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold implicitTransferCertificate
  omega

def sampleImplicitTransferCertificateWindow :
    ImplicitTransferCertificateWindow where
  radiusWindow := 5
  transferWindow := 6
  errorWindow := 2
  certificateBudget := 10
  slack := 1

example :
    implicitTransferCertificateReady
      sampleImplicitTransferCertificateWindow := by
  norm_num [implicitTransferCertificateReady,
    implicitTransferCertificateControlled, sampleImplicitTransferCertificateWindow]

example :
    sampleImplicitTransferCertificateWindow.certificateBudget ≤
      implicitTransferCertificate sampleImplicitTransferCertificateWindow := by
  apply implicitTransferCertificate_budget_le_certificate
  norm_num [implicitTransferCertificateReady,
    implicitTransferCertificateControlled, sampleImplicitTransferCertificateWindow]

structure ImplicitTransferRefinementCertificate where
  radiusWindow : ℕ
  transferWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitTransferRefinementCertificate.transferControlled
    (c : ImplicitTransferRefinementCertificate) : Prop :=
  c.transferWindow ≤ c.radiusWindow + c.errorWindow + c.slack

def ImplicitTransferRefinementCertificate.certificateBudgetControlled
    (c : ImplicitTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.transferWindow + c.errorWindow + c.slack

def implicitTransferRefinementReady
    (c : ImplicitTransferRefinementCertificate) : Prop :=
  0 < c.radiusWindow ∧ c.transferControlled ∧ c.certificateBudgetControlled

def ImplicitTransferRefinementCertificate.size
    (c : ImplicitTransferRefinementCertificate) : ℕ :=
  c.radiusWindow + c.transferWindow + c.errorWindow + c.slack

theorem implicitTransfer_certificateBudgetWindow_le_size
    {c : ImplicitTransferRefinementCertificate}
    (h : implicitTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleImplicitTransferRefinementCertificate :
    ImplicitTransferRefinementCertificate :=
  { radiusWindow := 5, transferWindow := 6, errorWindow := 2,
    certificateBudgetWindow := 14, slack := 1 }

example : implicitTransferRefinementReady
    sampleImplicitTransferRefinementCertificate := by
  norm_num [implicitTransferRefinementReady,
    ImplicitTransferRefinementCertificate.transferControlled,
    ImplicitTransferRefinementCertificate.certificateBudgetControlled,
    sampleImplicitTransferRefinementCertificate]

example :
    sampleImplicitTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferRefinementCertificate.size := by
  norm_num [ImplicitTransferRefinementCertificate.size,
    sampleImplicitTransferRefinementCertificate]

structure ImplicitTransferBudgetCertificate where
  radiusWindow : ℕ
  transferWindow : ℕ
  errorWindow : ℕ
  implicitBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ImplicitTransferBudgetCertificate.controlled
    (c : ImplicitTransferBudgetCertificate) : Prop :=
  0 < c.radiusWindow ∧
    c.transferWindow ≤ c.radiusWindow + c.errorWindow + c.slack ∧
      c.implicitBudgetWindow ≤
        c.radiusWindow + c.transferWindow + c.errorWindow + c.slack

def ImplicitTransferBudgetCertificate.budgetControlled
    (c : ImplicitTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radiusWindow + c.transferWindow + c.errorWindow +
      c.implicitBudgetWindow + c.slack

def ImplicitTransferBudgetCertificate.Ready
    (c : ImplicitTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ImplicitTransferBudgetCertificate.size
    (c : ImplicitTransferBudgetCertificate) : ℕ :=
  c.radiusWindow + c.transferWindow + c.errorWindow +
    c.implicitBudgetWindow + c.slack

theorem implicitTransfer_budgetCertificate_le_size
    (c : ImplicitTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleImplicitTransferBudgetCertificate :
    ImplicitTransferBudgetCertificate :=
  { radiusWindow := 5
    transferWindow := 6
    errorWindow := 2
    implicitBudgetWindow := 14
    certificateBudgetWindow := 28
    slack := 1 }

example : sampleImplicitTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitTransferBudgetCertificate.controlled,
      sampleImplicitTransferBudgetCertificate]
  · norm_num [ImplicitTransferBudgetCertificate.budgetControlled,
      sampleImplicitTransferBudgetCertificate]

example :
    sampleImplicitTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferBudgetCertificate.size := by
  apply implicitTransfer_budgetCertificate_le_size
  constructor
  · norm_num [ImplicitTransferBudgetCertificate.controlled,
      sampleImplicitTransferBudgetCertificate]
  · norm_num [ImplicitTransferBudgetCertificate.budgetControlled,
      sampleImplicitTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleImplicitTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [ImplicitTransferBudgetCertificate.controlled,
      sampleImplicitTransferBudgetCertificate]
  · norm_num [ImplicitTransferBudgetCertificate.budgetControlled,
      sampleImplicitTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleImplicitTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleImplicitTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ImplicitTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleImplicitTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleImplicitTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ImplicitTransferWindows
