import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Moment comparison window schemas.

This module records finite bookkeeping for moment comparison windows.
-/

namespace AnalyticCombinatorics.AppC.MomentComparisonWindowSchemas

structure MomentComparisonWindowData where
  momentOrder : ℕ
  comparisonWindow : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def hasMomentOrder (d : MomentComparisonWindowData) : Prop :=
  0 < d.momentOrder

def comparisonWindowControlled (d : MomentComparisonWindowData) : Prop :=
  d.comparisonWindow ≤ d.momentOrder + d.comparisonSlack

def momentComparisonWindowReady
    (d : MomentComparisonWindowData) : Prop :=
  hasMomentOrder d ∧ comparisonWindowControlled d

def momentComparisonWindowBudget
    (d : MomentComparisonWindowData) : ℕ :=
  d.momentOrder + d.comparisonWindow + d.comparisonSlack

theorem momentComparisonWindowReady.hasMomentOrder
    {d : MomentComparisonWindowData}
    (h : momentComparisonWindowReady d) :
    hasMomentOrder d ∧ comparisonWindowControlled d ∧
      d.comparisonWindow ≤ momentComparisonWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold momentComparisonWindowBudget
  omega

theorem comparisonWindow_le_budget (d : MomentComparisonWindowData) :
    d.comparisonWindow ≤ momentComparisonWindowBudget d := by
  unfold momentComparisonWindowBudget
  omega

def sampleMomentComparisonWindowData : MomentComparisonWindowData :=
  { momentOrder := 6, comparisonWindow := 8, comparisonSlack := 3 }

example : momentComparisonWindowReady sampleMomentComparisonWindowData := by
  norm_num [momentComparisonWindowReady, hasMomentOrder]
  norm_num [comparisonWindowControlled, sampleMomentComparisonWindowData]

example :
    momentComparisonWindowBudget sampleMomentComparisonWindowData = 17 := by
  native_decide

structure MomentComparisonCertificateWindow where
  momentWindow : ℕ
  comparisonWindow : ℕ
  comparisonSlack : ℕ
  momentBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentComparisonCertificateWindow.comparisonControlled
    (w : MomentComparisonCertificateWindow) : Prop :=
  w.comparisonWindow ≤ w.momentWindow + w.comparisonSlack + w.slack

def momentComparisonCertificateReady
    (w : MomentComparisonCertificateWindow) : Prop :=
  0 < w.momentWindow ∧ w.comparisonControlled ∧
    w.momentBudget ≤ w.momentWindow + w.comparisonWindow + w.slack

def MomentComparisonCertificateWindow.certificate
    (w : MomentComparisonCertificateWindow) : ℕ :=
  w.momentWindow + w.comparisonWindow + w.comparisonSlack + w.momentBudget + w.slack

theorem momentComparison_momentBudget_le_certificate
    (w : MomentComparisonCertificateWindow) :
    w.momentBudget ≤ w.certificate := by
  unfold MomentComparisonCertificateWindow.certificate
  omega

def sampleMomentComparisonCertificateWindow :
    MomentComparisonCertificateWindow :=
  { momentWindow := 5, comparisonWindow := 7, comparisonSlack := 2,
    momentBudget := 14, slack := 2 }

example : momentComparisonCertificateReady
    sampleMomentComparisonCertificateWindow := by
  norm_num [momentComparisonCertificateReady,
    MomentComparisonCertificateWindow.comparisonControlled,
    sampleMomentComparisonCertificateWindow]


structure MomentComparisonWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MomentComparisonWindowSchemasBudgetCertificate.controlled
    (c : MomentComparisonWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MomentComparisonWindowSchemasBudgetCertificate.budgetControlled
    (c : MomentComparisonWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MomentComparisonWindowSchemasBudgetCertificate.Ready
    (c : MomentComparisonWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MomentComparisonWindowSchemasBudgetCertificate.size
    (c : MomentComparisonWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem momentComparisonWindowSchemas_budgetCertificate_le_size
    (c : MomentComparisonWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMomentComparisonWindowSchemasBudgetCertificate :
    MomentComparisonWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMomentComparisonWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.controlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.budgetControlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]

example : sampleMomentComparisonWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.controlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.budgetControlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]

example :
    sampleMomentComparisonWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentComparisonWindowSchemasBudgetCertificate.size := by
  apply momentComparisonWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.controlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]
  · norm_num [MomentComparisonWindowSchemasBudgetCertificate.budgetControlled,
      sampleMomentComparisonWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleMomentComparisonWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMomentComparisonWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List MomentComparisonWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMomentComparisonWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMomentComparisonWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MomentComparisonWindowSchemas
