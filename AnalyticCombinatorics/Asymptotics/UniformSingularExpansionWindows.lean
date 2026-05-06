import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform singular expansion windows.

This module records finite bookkeeping for uniform singular expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformSingularExpansionWindows

structure SingularExpansionWindowData where
  singularOrder : ℕ
  expansionDepth : ℕ
  remainderSlack : ℕ
deriving DecidableEq, Repr

def hasSingularOrder (d : SingularExpansionWindowData) : Prop :=
  0 < d.singularOrder

def expansionDepthControlled (d : SingularExpansionWindowData) : Prop :=
  d.expansionDepth ≤ d.singularOrder + d.remainderSlack

def singularExpansionReady (d : SingularExpansionWindowData) : Prop :=
  hasSingularOrder d ∧ expansionDepthControlled d

def singularExpansionBudget (d : SingularExpansionWindowData) : ℕ :=
  d.singularOrder + d.expansionDepth + d.remainderSlack

theorem singularExpansionReady.hasSingularOrder
    {d : SingularExpansionWindowData}
    (h : singularExpansionReady d) :
    hasSingularOrder d ∧ expansionDepthControlled d ∧
      d.expansionDepth ≤ singularExpansionBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold singularExpansionBudget
  omega

theorem expansionDepth_le_budget (d : SingularExpansionWindowData) :
    d.expansionDepth ≤ singularExpansionBudget d := by
  unfold singularExpansionBudget
  omega

def sampleSingularExpansionWindowData : SingularExpansionWindowData :=
  { singularOrder := 6, expansionDepth := 8, remainderSlack := 3 }

example : singularExpansionReady sampleSingularExpansionWindowData := by
  norm_num [singularExpansionReady, hasSingularOrder]
  norm_num [expansionDepthControlled, sampleSingularExpansionWindowData]

example :
    singularExpansionBudget sampleSingularExpansionWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for singular expansion windows. -/
def singularExpansionWindowDataListReady
    (data : List SingularExpansionWindowData) : Bool :=
  data.all fun d =>
    0 < d.singularOrder && d.expansionDepth ≤ d.singularOrder + d.remainderSlack

theorem singularExpansionWindowDataList_readyWindow :
    singularExpansionWindowDataListReady
      [{ singularOrder := 4, expansionDepth := 5, remainderSlack := 1 },
       { singularOrder := 6, expansionDepth := 8, remainderSlack := 3 }] = true := by
  unfold singularExpansionWindowDataListReady
  native_decide

/-- A certificate window for uniform singular expansion. -/
structure SingularExpansionCertificateWindow where
  singularWindow : ℕ
  expansionWindow : ℕ
  remainderSlack : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Expansion depth is controlled by singular order and slack. -/
def singularExpansionCertificateControlled
    (w : SingularExpansionCertificateWindow) : Prop :=
  w.expansionWindow ≤ w.singularWindow + w.remainderSlack + w.slack

/-- Readiness for a singular expansion certificate. -/
def singularExpansionCertificateReady
    (w : SingularExpansionCertificateWindow) : Prop :=
  0 < w.singularWindow ∧
    singularExpansionCertificateControlled w ∧
      w.certificateBudget ≤ w.singularWindow + w.expansionWindow + w.slack

/-- Total size of a singular expansion certificate. -/
def singularExpansionCertificate
    (w : SingularExpansionCertificateWindow) : ℕ :=
  w.singularWindow + w.expansionWindow + w.remainderSlack +
    w.certificateBudget + w.slack

theorem singularExpansionCertificate_budget_le_certificate
    (w : SingularExpansionCertificateWindow)
    (h : singularExpansionCertificateReady w) :
    w.certificateBudget ≤ singularExpansionCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold singularExpansionCertificate
  omega

def sampleSingularExpansionCertificateWindow :
    SingularExpansionCertificateWindow where
  singularWindow := 6
  expansionWindow := 7
  remainderSlack := 2
  certificateBudget := 12
  slack := 1

example :
    singularExpansionCertificateReady
      sampleSingularExpansionCertificateWindow := by
  norm_num [singularExpansionCertificateReady,
    singularExpansionCertificateControlled,
    sampleSingularExpansionCertificateWindow]

example :
    sampleSingularExpansionCertificateWindow.certificateBudget ≤
      singularExpansionCertificate sampleSingularExpansionCertificateWindow := by
  apply singularExpansionCertificate_budget_le_certificate
  norm_num [singularExpansionCertificateReady,
    singularExpansionCertificateControlled,
    sampleSingularExpansionCertificateWindow]

structure SingularExpansionRefinementCertificate where
  singularWindow : ℕ
  expansionWindow : ℕ
  remainderSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularExpansionRefinementCertificate.expansionControlled
    (c : SingularExpansionRefinementCertificate) : Prop :=
  c.expansionWindow ≤ c.singularWindow + c.remainderSlackWindow + c.slack

def SingularExpansionRefinementCertificate.certificateBudgetControlled
    (c : SingularExpansionRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularWindow + c.expansionWindow + c.remainderSlackWindow + c.slack

def singularExpansionRefinementReady
    (c : SingularExpansionRefinementCertificate) : Prop :=
  0 < c.singularWindow ∧ c.expansionControlled ∧ c.certificateBudgetControlled

def SingularExpansionRefinementCertificate.size
    (c : SingularExpansionRefinementCertificate) : ℕ :=
  c.singularWindow + c.expansionWindow + c.remainderSlackWindow + c.slack

theorem singularExpansion_certificateBudgetWindow_le_size
    {c : SingularExpansionRefinementCertificate}
    (h : singularExpansionRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleSingularExpansionRefinementCertificate :
    SingularExpansionRefinementCertificate :=
  { singularWindow := 6, expansionWindow := 7, remainderSlackWindow := 2,
    certificateBudgetWindow := 16, slack := 1 }

example : singularExpansionRefinementReady
    sampleSingularExpansionRefinementCertificate := by
  norm_num [singularExpansionRefinementReady,
    SingularExpansionRefinementCertificate.expansionControlled,
    SingularExpansionRefinementCertificate.certificateBudgetControlled,
    sampleSingularExpansionRefinementCertificate]

example :
    sampleSingularExpansionRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularExpansionRefinementCertificate.size := by
  norm_num [SingularExpansionRefinementCertificate.size,
    sampleSingularExpansionRefinementCertificate]

structure SingularExpansionBudgetCertificate where
  singularWindow : ℕ
  expansionWindow : ℕ
  remainderSlackWindow : ℕ
  expansionBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularExpansionBudgetCertificate.controlled
    (c : SingularExpansionBudgetCertificate) : Prop :=
  0 < c.singularWindow ∧
    c.expansionWindow ≤ c.singularWindow + c.remainderSlackWindow + c.slack ∧
      c.expansionBudgetWindow ≤
        c.singularWindow + c.expansionWindow + c.remainderSlackWindow + c.slack

def SingularExpansionBudgetCertificate.budgetControlled
    (c : SingularExpansionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularWindow + c.expansionWindow + c.remainderSlackWindow +
      c.expansionBudgetWindow + c.slack

def SingularExpansionBudgetCertificate.Ready
    (c : SingularExpansionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularExpansionBudgetCertificate.size
    (c : SingularExpansionBudgetCertificate) : ℕ :=
  c.singularWindow + c.expansionWindow + c.remainderSlackWindow +
    c.expansionBudgetWindow + c.slack

theorem singularExpansion_budgetCertificate_le_size
    (c : SingularExpansionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularExpansionBudgetCertificate :
    SingularExpansionBudgetCertificate :=
  { singularWindow := 6
    expansionWindow := 7
    remainderSlackWindow := 2
    expansionBudgetWindow := 16
    certificateBudgetWindow := 32
    slack := 1 }

example : sampleSingularExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularExpansionBudgetCertificate.controlled,
      sampleSingularExpansionBudgetCertificate]
  · norm_num [SingularExpansionBudgetCertificate.budgetControlled,
      sampleSingularExpansionBudgetCertificate]

example :
    sampleSingularExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularExpansionBudgetCertificate.size := by
  apply singularExpansion_budgetCertificate_le_size
  constructor
  · norm_num [SingularExpansionBudgetCertificate.controlled,
      sampleSingularExpansionBudgetCertificate]
  · norm_num [SingularExpansionBudgetCertificate.budgetControlled,
      sampleSingularExpansionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularExpansionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularExpansionBudgetCertificate.controlled,
      sampleSingularExpansionBudgetCertificate]
  · norm_num [SingularExpansionBudgetCertificate.budgetControlled,
      sampleSingularExpansionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularExpansionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularExpansionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularExpansionBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularExpansionBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularExpansionBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformSingularExpansionWindows
