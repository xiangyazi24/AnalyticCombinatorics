import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Hankel window schemas.

The finite schema records loop radius, branch margin, and error slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.HankelWindowSchemas

structure HankelWindowData where
  loopRadius : ℕ
  branchMargin : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def branchMarginPositive (d : HankelWindowData) : Prop :=
  0 < d.branchMargin

def loopRadiusControlled (d : HankelWindowData) : Prop :=
  d.loopRadius ≤ d.branchMargin + d.errorSlack

def hankelWindowReady (d : HankelWindowData) : Prop :=
  branchMarginPositive d ∧ loopRadiusControlled d

def hankelWindowBudget (d : HankelWindowData) : ℕ :=
  d.loopRadius + d.branchMargin + d.errorSlack

theorem hankelWindowReady.branch {d : HankelWindowData}
    (h : hankelWindowReady d) :
    branchMarginPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem loopRadius_le_hankelWindowBudget (d : HankelWindowData) :
    d.loopRadius ≤ hankelWindowBudget d := by
  unfold hankelWindowBudget
  omega

def sampleHankelWindowData : HankelWindowData :=
  { loopRadius := 6, branchMargin := 4, errorSlack := 3 }

example : hankelWindowReady sampleHankelWindowData := by
  norm_num [hankelWindowReady, branchMarginPositive]
  norm_num [loopRadiusControlled, sampleHankelWindowData]

example : hankelWindowBudget sampleHankelWindowData = 13 := by
  native_decide

structure HankelTransferWindow where
  loopRadius : ℕ
  branchMargin : ℕ
  localOrder : ℕ
  errorSlack : ℕ
  coefficientBudget : ℕ
deriving DecidableEq, Repr

def HankelTransferWindow.loopControlled (w : HankelTransferWindow) : Prop :=
  w.loopRadius ≤ w.branchMargin + w.errorSlack

def HankelTransferWindow.coefficientControlled (w : HankelTransferWindow) : Prop :=
  w.coefficientBudget ≤ w.loopRadius + w.branchMargin + w.errorSlack

def hankelTransferWindowReady (w : HankelTransferWindow) : Prop :=
  0 < w.branchMargin ∧
    0 < w.localOrder ∧
    w.loopControlled ∧
    w.coefficientControlled

def HankelTransferWindow.certificate (w : HankelTransferWindow) : ℕ :=
  w.loopRadius + w.branchMargin + w.errorSlack

theorem hankel_coefficientBudget_le_certificate {w : HankelTransferWindow}
    (h : hankelTransferWindowReady w) :
    w.coefficientBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hcoeff⟩
  exact hcoeff

def sampleHankelTransferWindow : HankelTransferWindow :=
  { loopRadius := 6, branchMargin := 4, localOrder := 2, errorSlack := 3,
    coefficientBudget := 8 }

example : hankelTransferWindowReady sampleHankelTransferWindow := by
  norm_num [hankelTransferWindowReady, HankelTransferWindow.loopControlled,
    HankelTransferWindow.coefficientControlled, sampleHankelTransferWindow]

example : sampleHankelTransferWindow.certificate = 13 := by
  native_decide


structure HankelWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HankelWindowSchemasBudgetCertificate.controlled
    (c : HankelWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HankelWindowSchemasBudgetCertificate.budgetControlled
    (c : HankelWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HankelWindowSchemasBudgetCertificate.Ready
    (c : HankelWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HankelWindowSchemasBudgetCertificate.size
    (c : HankelWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hankelWindowSchemas_budgetCertificate_le_size
    (c : HankelWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHankelWindowSchemasBudgetCertificate :
    HankelWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHankelWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelWindowSchemasBudgetCertificate.controlled,
      sampleHankelWindowSchemasBudgetCertificate]
  · norm_num [HankelWindowSchemasBudgetCertificate.budgetControlled,
      sampleHankelWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHankelWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHankelWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HankelWindowSchemasBudgetCertificate.controlled,
      sampleHankelWindowSchemasBudgetCertificate]
  · norm_num [HankelWindowSchemasBudgetCertificate.budgetControlled,
      sampleHankelWindowSchemasBudgetCertificate]

example :
    sampleHankelWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHankelWindowSchemasBudgetCertificate.size := by
  apply hankelWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HankelWindowSchemasBudgetCertificate.controlled,
      sampleHankelWindowSchemasBudgetCertificate]
  · norm_num [HankelWindowSchemasBudgetCertificate.budgetControlled,
      sampleHankelWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HankelWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHankelWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHankelWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.HankelWindowSchemas
