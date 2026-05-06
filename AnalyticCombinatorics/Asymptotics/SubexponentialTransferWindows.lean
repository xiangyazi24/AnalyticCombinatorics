import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Subexponential transfer windows.

The finite schema records exponential scale, subexponential correction,
and remainder slack.
-/

namespace AnalyticCombinatorics.Asymptotics.SubexponentialTransferWindows

structure SubexponentialTransferWindowData where
  exponentialScale : ℕ
  correctionBudget : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def exponentialScalePositive (d : SubexponentialTransferWindowData) : Prop :=
  0 < d.exponentialScale

def correctionControlled (d : SubexponentialTransferWindowData) : Prop :=
  d.correctionBudget ≤ d.exponentialScale + d.remainderSlack

def subexponentialTransferWindowReady
    (d : SubexponentialTransferWindowData) : Prop :=
  exponentialScalePositive d ∧ correctionControlled d

def subexponentialTransferWindowBudget
    (d : SubexponentialTransferWindowData) : ℕ :=
  d.exponentialScale + d.correctionBudget + d.remainderSlack

theorem subexponentialTransferWindowReady.scale
    {d : SubexponentialTransferWindowData}
    (h : subexponentialTransferWindowReady d) :
    exponentialScalePositive d ∧ correctionControlled d ∧
      d.correctionBudget ≤ subexponentialTransferWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold subexponentialTransferWindowBudget
  omega

theorem correctionBudget_le_subexponentialBudget
    (d : SubexponentialTransferWindowData) :
    d.correctionBudget ≤ subexponentialTransferWindowBudget d := by
  unfold subexponentialTransferWindowBudget
  omega

def sampleSubexponentialTransferWindowData :
    SubexponentialTransferWindowData :=
  { exponentialScale := 6, correctionBudget := 8, remainderSlack := 3 }

example :
    subexponentialTransferWindowReady
      sampleSubexponentialTransferWindowData := by
  norm_num [subexponentialTransferWindowReady, exponentialScalePositive]
  norm_num [correctionControlled, sampleSubexponentialTransferWindowData]

example :
    subexponentialTransferWindowBudget
      sampleSubexponentialTransferWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for subexponential transfer window data. -/
def subexponentialTransferDataListReady
    (data : List SubexponentialTransferWindowData) : Bool :=
  data.all fun d =>
    0 < d.exponentialScale && d.correctionBudget ≤ d.exponentialScale + d.remainderSlack

theorem subexponentialTransferDataList_readyWindow :
    subexponentialTransferDataListReady
      [{ exponentialScale := 4, correctionBudget := 5, remainderSlack := 1 },
       { exponentialScale := 6, correctionBudget := 8, remainderSlack := 3 }] =
      true := by
  unfold subexponentialTransferDataListReady
  native_decide

/-- A certificate window for subexponential transfer. -/
structure SubexponentialTransferCertificateWindow where
  exponentialWindow : ℕ
  correctionWindow : ℕ
  remainderSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The correction window is controlled by the exponential scale. -/
def subexponentialTransferCertificateControlled
    (w : SubexponentialTransferCertificateWindow) : Prop :=
  w.correctionWindow ≤ w.exponentialWindow + w.remainderSlack + w.slack

/-- Readiness for a subexponential transfer certificate. -/
def subexponentialTransferCertificateReady
    (w : SubexponentialTransferCertificateWindow) : Prop :=
  0 < w.exponentialWindow ∧
    subexponentialTransferCertificateControlled w ∧
      w.certificateBudget ≤ w.exponentialWindow + w.correctionWindow + w.slack

/-- Total size of a subexponential transfer certificate. -/
def subexponentialTransferCertificate
    (w : SubexponentialTransferCertificateWindow) : ℕ :=
  w.exponentialWindow + w.correctionWindow + w.remainderSlack +
    w.certificateBudget + w.slack

theorem subexponentialTransferCertificate_budget_le_certificate
    (w : SubexponentialTransferCertificateWindow)
    (h : subexponentialTransferCertificateReady w) :
    w.certificateBudget ≤ subexponentialTransferCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold subexponentialTransferCertificate
  omega

def sampleSubexponentialTransferCertificateWindow :
    SubexponentialTransferCertificateWindow where
  exponentialWindow := 6
  correctionWindow := 7
  remainderSlack := 2
  certificateBudget := 12
  slack := 1

example :
    subexponentialTransferCertificateReady
      sampleSubexponentialTransferCertificateWindow := by
  norm_num [subexponentialTransferCertificateReady,
    subexponentialTransferCertificateControlled,
    sampleSubexponentialTransferCertificateWindow]

example :
    sampleSubexponentialTransferCertificateWindow.certificateBudget ≤
      subexponentialTransferCertificate
        sampleSubexponentialTransferCertificateWindow := by
  apply subexponentialTransferCertificate_budget_le_certificate
  norm_num [subexponentialTransferCertificateReady,
    subexponentialTransferCertificateControlled,
    sampleSubexponentialTransferCertificateWindow]

structure SubexponentialTransferRefinementCertificate where
  exponentialWindow : ℕ
  correctionWindow : ℕ
  remainderSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubexponentialTransferRefinementCertificate.correctionControlled
    (c : SubexponentialTransferRefinementCertificate) : Prop :=
  c.correctionWindow ≤ c.exponentialWindow + c.remainderSlackWindow + c.slack

def SubexponentialTransferRefinementCertificate.certificateBudgetControlled
    (c : SubexponentialTransferRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.correctionWindow + c.remainderSlackWindow + c.slack

def subexponentialTransferRefinementReady
    (c : SubexponentialTransferRefinementCertificate) : Prop :=
  0 < c.exponentialWindow ∧ c.correctionControlled ∧ c.certificateBudgetControlled

def SubexponentialTransferRefinementCertificate.size
    (c : SubexponentialTransferRefinementCertificate) : ℕ :=
  c.exponentialWindow + c.correctionWindow + c.remainderSlackWindow + c.slack

theorem subexponentialTransfer_certificateBudgetWindow_le_size
    {c : SubexponentialTransferRefinementCertificate}
    (h : subexponentialTransferRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSubexponentialTransferRefinementCertificate :
    SubexponentialTransferRefinementCertificate :=
  { exponentialWindow := 6, correctionWindow := 7, remainderSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : subexponentialTransferRefinementReady
    sampleSubexponentialTransferRefinementCertificate := by
  norm_num [subexponentialTransferRefinementReady,
    SubexponentialTransferRefinementCertificate.correctionControlled,
    SubexponentialTransferRefinementCertificate.certificateBudgetControlled,
    sampleSubexponentialTransferRefinementCertificate]

example :
    sampleSubexponentialTransferRefinementCertificate.certificateBudgetWindow ≤
      sampleSubexponentialTransferRefinementCertificate.size := by
  norm_num [SubexponentialTransferRefinementCertificate.size,
    sampleSubexponentialTransferRefinementCertificate]

structure SubexponentialTransferBudgetCertificate where
  exponentialWindow : ℕ
  correctionWindow : ℕ
  remainderSlackWindow : ℕ
  correctionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SubexponentialTransferBudgetCertificate.controlled
    (c : SubexponentialTransferBudgetCertificate) : Prop :=
  0 < c.exponentialWindow ∧
    c.correctionWindow ≤ c.exponentialWindow + c.remainderSlackWindow + c.slack ∧
      c.correctionBudgetWindow ≤
        c.exponentialWindow + c.correctionWindow + c.remainderSlackWindow + c.slack

def SubexponentialTransferBudgetCertificate.budgetControlled
    (c : SubexponentialTransferBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.exponentialWindow + c.correctionWindow + c.remainderSlackWindow +
      c.correctionBudgetWindow + c.slack

def SubexponentialTransferBudgetCertificate.Ready
    (c : SubexponentialTransferBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SubexponentialTransferBudgetCertificate.size
    (c : SubexponentialTransferBudgetCertificate) : ℕ :=
  c.exponentialWindow + c.correctionWindow + c.remainderSlackWindow +
    c.correctionBudgetWindow + c.slack

theorem subexponentialTransfer_budgetCertificate_le_size
    (c : SubexponentialTransferBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSubexponentialTransferBudgetCertificate :
    SubexponentialTransferBudgetCertificate :=
  { exponentialWindow := 6
    correctionWindow := 7
    remainderSlackWindow := 2
    correctionBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSubexponentialTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialTransferBudgetCertificate.controlled,
      sampleSubexponentialTransferBudgetCertificate]
  · norm_num [SubexponentialTransferBudgetCertificate.budgetControlled,
      sampleSubexponentialTransferBudgetCertificate]

example :
    sampleSubexponentialTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialTransferBudgetCertificate.size := by
  apply subexponentialTransfer_budgetCertificate_le_size
  constructor
  · norm_num [SubexponentialTransferBudgetCertificate.controlled,
      sampleSubexponentialTransferBudgetCertificate]
  · norm_num [SubexponentialTransferBudgetCertificate.budgetControlled,
      sampleSubexponentialTransferBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSubexponentialTransferBudgetCertificate.Ready := by
  constructor
  · norm_num [SubexponentialTransferBudgetCertificate.controlled,
      sampleSubexponentialTransferBudgetCertificate]
  · norm_num [SubexponentialTransferBudgetCertificate.budgetControlled,
      sampleSubexponentialTransferBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSubexponentialTransferBudgetCertificate.certificateBudgetWindow ≤
      sampleSubexponentialTransferBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SubexponentialTransferBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSubexponentialTransferBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSubexponentialTransferBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SubexponentialTransferWindows
