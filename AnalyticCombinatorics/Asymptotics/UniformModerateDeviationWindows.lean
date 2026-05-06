import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform moderate deviation windows.

This module records finite bookkeeping for moderate deviation windows.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformModerateDeviationWindows

structure ModerateDeviationWindowData where
  deviationScale : ℕ
  probabilityWindow : ℕ
  deviationSlack : ℕ
deriving DecidableEq, Repr

def hasDeviationScale (d : ModerateDeviationWindowData) : Prop :=
  0 < d.deviationScale

def probabilityWindowControlled (d : ModerateDeviationWindowData) : Prop :=
  d.probabilityWindow ≤ d.deviationScale + d.deviationSlack

def moderateDeviationReady (d : ModerateDeviationWindowData) : Prop :=
  hasDeviationScale d ∧ probabilityWindowControlled d

def moderateDeviationBudget (d : ModerateDeviationWindowData) : ℕ :=
  d.deviationScale + d.probabilityWindow + d.deviationSlack

theorem moderateDeviationReady.hasDeviationScale
    {d : ModerateDeviationWindowData}
    (h : moderateDeviationReady d) :
    hasDeviationScale d ∧ probabilityWindowControlled d ∧
      d.probabilityWindow ≤ moderateDeviationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold moderateDeviationBudget
  omega

theorem probabilityWindow_le_budget (d : ModerateDeviationWindowData) :
    d.probabilityWindow ≤ moderateDeviationBudget d := by
  unfold moderateDeviationBudget
  omega

def sampleModerateDeviationWindowData : ModerateDeviationWindowData :=
  { deviationScale := 6, probabilityWindow := 8, deviationSlack := 3 }

example : moderateDeviationReady sampleModerateDeviationWindowData := by
  norm_num [moderateDeviationReady, hasDeviationScale]
  norm_num [probabilityWindowControlled, sampleModerateDeviationWindowData]

example : moderateDeviationBudget sampleModerateDeviationWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for moderate deviation windows. -/
def moderateDeviationWindowDataListReady
    (data : List ModerateDeviationWindowData) : Bool :=
  data.all fun d =>
    0 < d.deviationScale && d.probabilityWindow ≤ d.deviationScale + d.deviationSlack

theorem moderateDeviationWindowDataList_readyWindow :
    moderateDeviationWindowDataListReady
      [{ deviationScale := 4, probabilityWindow := 5, deviationSlack := 1 },
       { deviationScale := 6, probabilityWindow := 8, deviationSlack := 3 }] = true := by
  unfold moderateDeviationWindowDataListReady
  native_decide

/-- A certificate window for uniform moderate deviations. -/
structure ModerateDeviationCertificateWindow where
  deviationWindow : ℕ
  probabilityWindow : ℕ
  deviationSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The probability window is controlled by the deviation window. -/
def moderateDeviationCertificateControlled
    (w : ModerateDeviationCertificateWindow) : Prop :=
  w.probabilityWindow ≤ w.deviationWindow + w.deviationSlack + w.slack

/-- Readiness for a moderate deviation certificate. -/
def moderateDeviationCertificateReady
    (w : ModerateDeviationCertificateWindow) : Prop :=
  0 < w.deviationWindow ∧
    moderateDeviationCertificateControlled w ∧
      w.certificateBudget ≤ w.deviationWindow + w.probabilityWindow + w.slack

/-- Total size of a moderate deviation certificate. -/
def moderateDeviationCertificate
    (w : ModerateDeviationCertificateWindow) : ℕ :=
  w.deviationWindow + w.probabilityWindow + w.deviationSlack +
    w.certificateBudget + w.slack

theorem moderateDeviationCertificate_budget_le_certificate
    (w : ModerateDeviationCertificateWindow)
    (h : moderateDeviationCertificateReady w) :
    w.certificateBudget ≤ moderateDeviationCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold moderateDeviationCertificate
  omega

def sampleModerateDeviationCertificateWindow :
    ModerateDeviationCertificateWindow where
  deviationWindow := 6
  probabilityWindow := 7
  deviationSlack := 2
  certificateBudget := 12
  slack := 1

example :
    moderateDeviationCertificateReady
      sampleModerateDeviationCertificateWindow := by
  norm_num [moderateDeviationCertificateReady,
    moderateDeviationCertificateControlled,
    sampleModerateDeviationCertificateWindow]

example :
    sampleModerateDeviationCertificateWindow.certificateBudget ≤
      moderateDeviationCertificate sampleModerateDeviationCertificateWindow := by
  apply moderateDeviationCertificate_budget_le_certificate
  norm_num [moderateDeviationCertificateReady,
    moderateDeviationCertificateControlled,
    sampleModerateDeviationCertificateWindow]

structure ModerateDeviationRefinementCertificate where
  deviationWindow : ℕ
  probabilityWindow : ℕ
  deviationSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationRefinementCertificate.probabilityControlled
    (c : ModerateDeviationRefinementCertificate) : Prop :=
  c.probabilityWindow ≤ c.deviationWindow + c.deviationSlackWindow + c.slack

def ModerateDeviationRefinementCertificate.certificateBudgetControlled
    (c : ModerateDeviationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.deviationWindow + c.probabilityWindow + c.deviationSlackWindow + c.slack

def moderateDeviationRefinementReady
    (c : ModerateDeviationRefinementCertificate) : Prop :=
  0 < c.deviationWindow ∧ c.probabilityControlled ∧ c.certificateBudgetControlled

def ModerateDeviationRefinementCertificate.size
    (c : ModerateDeviationRefinementCertificate) : ℕ :=
  c.deviationWindow + c.probabilityWindow + c.deviationSlackWindow + c.slack

theorem moderateDeviation_certificateBudgetWindow_le_size
    {c : ModerateDeviationRefinementCertificate}
    (h : moderateDeviationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleModerateDeviationRefinementCertificate :
    ModerateDeviationRefinementCertificate :=
  { deviationWindow := 6, probabilityWindow := 7, deviationSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : moderateDeviationRefinementReady
    sampleModerateDeviationRefinementCertificate := by
  norm_num [moderateDeviationRefinementReady,
    ModerateDeviationRefinementCertificate.probabilityControlled,
    ModerateDeviationRefinementCertificate.certificateBudgetControlled,
    sampleModerateDeviationRefinementCertificate]

example :
    sampleModerateDeviationRefinementCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationRefinementCertificate.size := by
  norm_num [ModerateDeviationRefinementCertificate.size,
    sampleModerateDeviationRefinementCertificate]

structure ModerateDeviationBudgetCertificate where
  deviationWindow : ℕ
  probabilityWindow : ℕ
  deviationSlackWindow : ℕ
  deviationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModerateDeviationBudgetCertificate.controlled
    (c : ModerateDeviationBudgetCertificate) : Prop :=
  0 < c.deviationWindow ∧
    c.probabilityWindow ≤ c.deviationWindow + c.deviationSlackWindow + c.slack ∧
      c.deviationBudgetWindow ≤
        c.deviationWindow + c.probabilityWindow + c.deviationSlackWindow + c.slack

def ModerateDeviationBudgetCertificate.budgetControlled
    (c : ModerateDeviationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.deviationWindow + c.probabilityWindow + c.deviationSlackWindow +
      c.deviationBudgetWindow + c.slack

def ModerateDeviationBudgetCertificate.Ready
    (c : ModerateDeviationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ModerateDeviationBudgetCertificate.size
    (c : ModerateDeviationBudgetCertificate) : ℕ :=
  c.deviationWindow + c.probabilityWindow + c.deviationSlackWindow +
    c.deviationBudgetWindow + c.slack

theorem moderateDeviation_budgetCertificate_le_size
    (c : ModerateDeviationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleModerateDeviationBudgetCertificate :
    ModerateDeviationBudgetCertificate :=
  { deviationWindow := 6
    probabilityWindow := 7
    deviationSlackWindow := 2
    deviationBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleModerateDeviationBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationBudgetCertificate.controlled,
      sampleModerateDeviationBudgetCertificate]
  · norm_num [ModerateDeviationBudgetCertificate.budgetControlled,
      sampleModerateDeviationBudgetCertificate]

example :
    sampleModerateDeviationBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationBudgetCertificate.size := by
  apply moderateDeviation_budgetCertificate_le_size
  constructor
  · norm_num [ModerateDeviationBudgetCertificate.controlled,
      sampleModerateDeviationBudgetCertificate]
  · norm_num [ModerateDeviationBudgetCertificate.budgetControlled,
      sampleModerateDeviationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleModerateDeviationBudgetCertificate.Ready := by
  constructor
  · norm_num [ModerateDeviationBudgetCertificate.controlled,
      sampleModerateDeviationBudgetCertificate]
  · norm_num [ModerateDeviationBudgetCertificate.budgetControlled,
      sampleModerateDeviationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleModerateDeviationBudgetCertificate.certificateBudgetWindow ≤
      sampleModerateDeviationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ModerateDeviationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleModerateDeviationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleModerateDeviationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformModerateDeviationWindows
