import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stein method schemas.

The finite schema records Stein operator budget, test class size, and
error slack.
-/

namespace AnalyticCombinatorics.AppC.SteinMethodSchemas

structure SteinMethodData where
  operatorBudget : ℕ
  testClassSize : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def operatorBudgetPositive (d : SteinMethodData) : Prop :=
  0 < d.operatorBudget

def testClassControlled (d : SteinMethodData) : Prop :=
  d.testClassSize ≤ d.operatorBudget + d.errorSlack

def steinMethodReady (d : SteinMethodData) : Prop :=
  operatorBudgetPositive d ∧ testClassControlled d

def steinMethodBudget (d : SteinMethodData) : ℕ :=
  d.operatorBudget + d.testClassSize + d.errorSlack

theorem steinMethodReady.operator {d : SteinMethodData}
    (h : steinMethodReady d) :
    operatorBudgetPositive d ∧ testClassControlled d ∧ d.testClassSize ≤ steinMethodBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold steinMethodBudget
  omega

theorem testClassSize_le_steinBudget (d : SteinMethodData) :
    d.testClassSize ≤ steinMethodBudget d := by
  unfold steinMethodBudget
  omega

def sampleSteinMethodData : SteinMethodData :=
  { operatorBudget := 5, testClassSize := 7, errorSlack := 3 }

example : steinMethodReady sampleSteinMethodData := by
  norm_num [steinMethodReady, operatorBudgetPositive]
  norm_num [testClassControlled, sampleSteinMethodData]

example : steinMethodBudget sampleSteinMethodData = 15 := by
  native_decide

structure SteinMethodWindow where
  operatorWindow : ℕ
  testClassWindow : ℕ
  errorSlack : ℕ
  methodBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteinMethodWindow.testClassControlled (w : SteinMethodWindow) : Prop :=
  w.testClassWindow ≤ w.operatorWindow + w.errorSlack + w.slack

def steinMethodWindowReady (w : SteinMethodWindow) : Prop :=
  0 < w.operatorWindow ∧ w.testClassControlled ∧
    w.methodBudget ≤ w.operatorWindow + w.testClassWindow + w.slack

def SteinMethodWindow.certificate (w : SteinMethodWindow) : ℕ :=
  w.operatorWindow + w.testClassWindow + w.errorSlack + w.methodBudget + w.slack

theorem steinMethod_methodBudget_le_certificate (w : SteinMethodWindow) :
    w.methodBudget ≤ w.certificate := by
  unfold SteinMethodWindow.certificate
  omega

def sampleSteinMethodWindow : SteinMethodWindow :=
  { operatorWindow := 5, testClassWindow := 7, errorSlack := 2, methodBudget := 14, slack := 2 }

example : steinMethodWindowReady sampleSteinMethodWindow := by
  norm_num [steinMethodWindowReady, SteinMethodWindow.testClassControlled,
    sampleSteinMethodWindow]


structure SteinMethodSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SteinMethodSchemasBudgetCertificate.controlled
    (c : SteinMethodSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SteinMethodSchemasBudgetCertificate.budgetControlled
    (c : SteinMethodSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SteinMethodSchemasBudgetCertificate.Ready
    (c : SteinMethodSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SteinMethodSchemasBudgetCertificate.size
    (c : SteinMethodSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem steinMethodSchemas_budgetCertificate_le_size
    (c : SteinMethodSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSteinMethodSchemasBudgetCertificate :
    SteinMethodSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSteinMethodSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SteinMethodSchemasBudgetCertificate.controlled,
      sampleSteinMethodSchemasBudgetCertificate]
  · norm_num [SteinMethodSchemasBudgetCertificate.budgetControlled,
      sampleSteinMethodSchemasBudgetCertificate]

example : sampleSteinMethodSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [SteinMethodSchemasBudgetCertificate.controlled,
      sampleSteinMethodSchemasBudgetCertificate]
  · norm_num [SteinMethodSchemasBudgetCertificate.budgetControlled,
      sampleSteinMethodSchemasBudgetCertificate]

example :
    sampleSteinMethodSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSteinMethodSchemasBudgetCertificate.size := by
  apply steinMethodSchemas_budgetCertificate_le_size
  constructor
  · norm_num [SteinMethodSchemasBudgetCertificate.controlled,
      sampleSteinMethodSchemasBudgetCertificate]
  · norm_num [SteinMethodSchemasBudgetCertificate.budgetControlled,
      sampleSteinMethodSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleSteinMethodSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleSteinMethodSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SteinMethodSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSteinMethodSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSteinMethodSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.SteinMethodSchemas
