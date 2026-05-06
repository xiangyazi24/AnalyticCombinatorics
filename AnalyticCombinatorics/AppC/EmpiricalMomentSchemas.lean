import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Empirical moment schemas.

This module records a finite empirical-moment schema: a positive sample size
controls a moment order with an error slack.
-/

namespace AnalyticCombinatorics.AppC.EmpiricalMomentSchemas

structure EmpiricalMomentData where
  sampleSize : ℕ
  momentOrder : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def hasSampleSize (d : EmpiricalMomentData) : Prop :=
  0 < d.sampleSize

def momentOrderControlled (d : EmpiricalMomentData) : Prop :=
  d.momentOrder ≤ d.sampleSize + d.errorSlack

def empiricalMomentReady (d : EmpiricalMomentData) : Prop :=
  hasSampleSize d ∧ momentOrderControlled d

def empiricalMomentBudget (d : EmpiricalMomentData) : ℕ :=
  d.sampleSize + d.momentOrder + d.errorSlack

theorem empiricalMomentReady.hasSampleSize {d : EmpiricalMomentData}
    (h : empiricalMomentReady d) :
    hasSampleSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem momentOrder_le_budget (d : EmpiricalMomentData) :
    d.momentOrder ≤ empiricalMomentBudget d := by
  unfold empiricalMomentBudget
  omega

def sampleEmpiricalMomentData : EmpiricalMomentData :=
  { sampleSize := 6, momentOrder := 8, errorSlack := 3 }

example : empiricalMomentReady sampleEmpiricalMomentData := by
  norm_num [empiricalMomentReady, hasSampleSize]
  norm_num [momentOrderControlled, sampleEmpiricalMomentData]

example : empiricalMomentBudget sampleEmpiricalMomentData = 17 := by
  native_decide

structure EmpiricalMomentWindow where
  sampleWindow : ℕ
  momentWindow : ℕ
  errorSlack : ℕ
  momentBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalMomentWindow.momentControlled (w : EmpiricalMomentWindow) : Prop :=
  w.momentWindow ≤ w.sampleWindow + w.errorSlack + w.slack

def empiricalMomentWindowReady (w : EmpiricalMomentWindow) : Prop :=
  0 < w.sampleWindow ∧ w.momentControlled ∧
    w.momentBudget ≤ w.sampleWindow + w.momentWindow + w.slack

def EmpiricalMomentWindow.certificate (w : EmpiricalMomentWindow) : ℕ :=
  w.sampleWindow + w.momentWindow + w.errorSlack + w.momentBudget + w.slack

theorem empiricalMoment_momentBudget_le_certificate (w : EmpiricalMomentWindow) :
    w.momentBudget ≤ w.certificate := by
  unfold EmpiricalMomentWindow.certificate
  omega

def sampleEmpiricalMomentWindow : EmpiricalMomentWindow :=
  { sampleWindow := 5, momentWindow := 7, errorSlack := 2, momentBudget := 14, slack := 2 }

example : empiricalMomentWindowReady sampleEmpiricalMomentWindow := by
  norm_num [empiricalMomentWindowReady, EmpiricalMomentWindow.momentControlled,
    sampleEmpiricalMomentWindow]


structure EmpiricalMomentSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalMomentSchemasBudgetCertificate.controlled
    (c : EmpiricalMomentSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EmpiricalMomentSchemasBudgetCertificate.budgetControlled
    (c : EmpiricalMomentSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EmpiricalMomentSchemasBudgetCertificate.Ready
    (c : EmpiricalMomentSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EmpiricalMomentSchemasBudgetCertificate.size
    (c : EmpiricalMomentSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem empiricalMomentSchemas_budgetCertificate_le_size
    (c : EmpiricalMomentSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEmpiricalMomentSchemasBudgetCertificate :
    EmpiricalMomentSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEmpiricalMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.controlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]

example : sampleEmpiricalMomentSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.controlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]

example :
    sampleEmpiricalMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalMomentSchemasBudgetCertificate.size := by
  apply empiricalMomentSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.controlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]
  · norm_num [EmpiricalMomentSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalMomentSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEmpiricalMomentSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalMomentSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EmpiricalMomentSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEmpiricalMomentSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEmpiricalMomentSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EmpiricalMomentSchemas
