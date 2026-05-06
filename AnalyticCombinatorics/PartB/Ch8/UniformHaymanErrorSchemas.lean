import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Hayman error schemas.

This module records finite bookkeeping for Hayman error windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.UniformHaymanErrorSchemas

structure HaymanErrorData where
  admissibilityScale : ℕ
  errorWindow : ℕ
  gaussianSlack : ℕ
deriving DecidableEq, Repr

def hasAdmissibilityScale (d : HaymanErrorData) : Prop :=
  0 < d.admissibilityScale

def errorWindowControlled (d : HaymanErrorData) : Prop :=
  d.errorWindow ≤ d.admissibilityScale + d.gaussianSlack

def haymanErrorReady (d : HaymanErrorData) : Prop :=
  hasAdmissibilityScale d ∧ errorWindowControlled d

def haymanErrorBudget (d : HaymanErrorData) : ℕ :=
  d.admissibilityScale + d.errorWindow + d.gaussianSlack

theorem haymanErrorReady.hasAdmissibilityScale {d : HaymanErrorData}
    (h : haymanErrorReady d) :
    hasAdmissibilityScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem errorWindow_le_budget (d : HaymanErrorData) :
    d.errorWindow ≤ haymanErrorBudget d := by
  unfold haymanErrorBudget
  omega

def sampleHaymanErrorData : HaymanErrorData :=
  { admissibilityScale := 6, errorWindow := 8, gaussianSlack := 3 }

example : haymanErrorReady sampleHaymanErrorData := by
  norm_num [haymanErrorReady, hasAdmissibilityScale]
  norm_num [errorWindowControlled, sampleHaymanErrorData]

example : haymanErrorBudget sampleHaymanErrorData = 17 := by
  native_decide

structure HaymanErrorWindow where
  admissibilityScale : ℕ
  errorWindow : ℕ
  gaussianSlack : ℕ
  saddleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HaymanErrorWindow.errorControlled (w : HaymanErrorWindow) : Prop :=
  w.errorWindow ≤ w.admissibilityScale + w.gaussianSlack + w.slack

def HaymanErrorWindow.saddleControlled (w : HaymanErrorWindow) : Prop :=
  w.saddleBudget ≤ w.admissibilityScale + w.errorWindow + w.gaussianSlack + w.slack

def haymanErrorWindowReady (w : HaymanErrorWindow) : Prop :=
  0 < w.admissibilityScale ∧
    w.errorControlled ∧
    w.saddleControlled

def HaymanErrorWindow.certificate (w : HaymanErrorWindow) : ℕ :=
  w.admissibilityScale + w.errorWindow + w.gaussianSlack + w.slack

theorem haymanError_saddleBudget_le_certificate {w : HaymanErrorWindow}
    (h : haymanErrorWindowReady w) :
    w.saddleBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hsaddle⟩
  exact hsaddle

def sampleHaymanErrorWindow : HaymanErrorWindow :=
  { admissibilityScale := 6, errorWindow := 8, gaussianSlack := 3, saddleBudget := 16,
    slack := 0 }

example : haymanErrorWindowReady sampleHaymanErrorWindow := by
  norm_num [haymanErrorWindowReady, HaymanErrorWindow.errorControlled,
    HaymanErrorWindow.saddleControlled, sampleHaymanErrorWindow]

example : sampleHaymanErrorWindow.certificate = 17 := by
  native_decide


structure UniformHaymanErrorSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformHaymanErrorSchemasBudgetCertificate.controlled
    (c : UniformHaymanErrorSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformHaymanErrorSchemasBudgetCertificate.budgetControlled
    (c : UniformHaymanErrorSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformHaymanErrorSchemasBudgetCertificate.Ready
    (c : UniformHaymanErrorSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformHaymanErrorSchemasBudgetCertificate.size
    (c : UniformHaymanErrorSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformHaymanErrorSchemas_budgetCertificate_le_size
    (c : UniformHaymanErrorSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformHaymanErrorSchemasBudgetCertificate :
    UniformHaymanErrorSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformHaymanErrorSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.controlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.budgetControlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformHaymanErrorSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHaymanErrorSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformHaymanErrorSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.controlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.budgetControlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]

example :
    sampleUniformHaymanErrorSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformHaymanErrorSchemasBudgetCertificate.size := by
  apply uniformHaymanErrorSchemas_budgetCertificate_le_size
  constructor
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.controlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]
  · norm_num [UniformHaymanErrorSchemasBudgetCertificate.budgetControlled,
      sampleUniformHaymanErrorSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List UniformHaymanErrorSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformHaymanErrorSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUniformHaymanErrorSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch8.UniformHaymanErrorSchemas
