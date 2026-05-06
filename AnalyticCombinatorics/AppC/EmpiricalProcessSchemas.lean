import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Empirical process schemas.

The finite record stores sample size, class complexity, and deviation
slack.
-/

namespace AnalyticCombinatorics.AppC.EmpiricalProcessSchemas

structure EmpiricalProcessData where
  sampleSize : ℕ
  classComplexity : ℕ
  deviationSlack : ℕ
deriving DecidableEq, Repr

def sampleSizePositive (d : EmpiricalProcessData) : Prop :=
  0 < d.sampleSize

def complexityControlled (d : EmpiricalProcessData) : Prop :=
  d.classComplexity ≤ d.sampleSize + d.deviationSlack

def empiricalProcessReady (d : EmpiricalProcessData) : Prop :=
  sampleSizePositive d ∧ complexityControlled d

def empiricalProcessBudget (d : EmpiricalProcessData) : ℕ :=
  d.sampleSize + d.classComplexity + d.deviationSlack

theorem empiricalProcessReady.sample {d : EmpiricalProcessData}
    (h : empiricalProcessReady d) :
    sampleSizePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem complexity_le_empiricalProcessBudget (d : EmpiricalProcessData) :
    d.classComplexity ≤ empiricalProcessBudget d := by
  unfold empiricalProcessBudget
  omega

def sampleEmpiricalProcessData : EmpiricalProcessData :=
  { sampleSize := 8, classComplexity := 10, deviationSlack := 3 }

example : empiricalProcessReady sampleEmpiricalProcessData := by
  norm_num [empiricalProcessReady, sampleSizePositive]
  norm_num [complexityControlled, sampleEmpiricalProcessData]

example : empiricalProcessBudget sampleEmpiricalProcessData = 21 := by
  native_decide

structure EmpiricalProcessWindow where
  sampleSize : ℕ
  classComplexity : ℕ
  deviationSlack : ℕ
  bracketingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalProcessWindow.complexityControlled (w : EmpiricalProcessWindow) : Prop :=
  w.classComplexity ≤ w.sampleSize + w.deviationSlack + w.slack

def EmpiricalProcessWindow.bracketingControlled (w : EmpiricalProcessWindow) : Prop :=
  w.bracketingBudget ≤ w.sampleSize + w.classComplexity + w.deviationSlack + w.slack

def empiricalProcessWindowReady (w : EmpiricalProcessWindow) : Prop :=
  0 < w.sampleSize ∧
    w.complexityControlled ∧
    w.bracketingControlled

def EmpiricalProcessWindow.certificate (w : EmpiricalProcessWindow) : ℕ :=
  w.sampleSize + w.classComplexity + w.deviationSlack + w.slack

theorem empiricalProcess_bracketingBudget_le_certificate {w : EmpiricalProcessWindow}
    (h : empiricalProcessWindowReady w) :
    w.bracketingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hbracketing⟩
  exact hbracketing

def sampleEmpiricalProcessWindow : EmpiricalProcessWindow :=
  { sampleSize := 8, classComplexity := 10, deviationSlack := 3, bracketingBudget := 20,
    slack := 0 }

example : empiricalProcessWindowReady sampleEmpiricalProcessWindow := by
  norm_num [empiricalProcessWindowReady, EmpiricalProcessWindow.complexityControlled,
    EmpiricalProcessWindow.bracketingControlled, sampleEmpiricalProcessWindow]

example : sampleEmpiricalProcessWindow.certificate = 21 := by
  native_decide


structure EmpiricalProcessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EmpiricalProcessSchemasBudgetCertificate.controlled
    (c : EmpiricalProcessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EmpiricalProcessSchemasBudgetCertificate.budgetControlled
    (c : EmpiricalProcessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EmpiricalProcessSchemasBudgetCertificate.Ready
    (c : EmpiricalProcessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EmpiricalProcessSchemasBudgetCertificate.size
    (c : EmpiricalProcessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem empiricalProcessSchemas_budgetCertificate_le_size
    (c : EmpiricalProcessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEmpiricalProcessSchemasBudgetCertificate :
    EmpiricalProcessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleEmpiricalProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]

example : sampleEmpiricalProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]

example :
    sampleEmpiricalProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalProcessSchemasBudgetCertificate.size := by
  apply empiricalProcessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.controlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]
  · norm_num [EmpiricalProcessSchemasBudgetCertificate.budgetControlled,
      sampleEmpiricalProcessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleEmpiricalProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleEmpiricalProcessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EmpiricalProcessSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEmpiricalProcessSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEmpiricalProcessSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.EmpiricalProcessSchemas
