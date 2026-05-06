import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Gaussian saddle window schemas.

The finite schema records Gaussian width, saddle scale, and truncation
budget.
-/

namespace AnalyticCombinatorics.PartB.Ch8.GaussianSaddleWindowSchemas

structure GaussianSaddleWindowData where
  gaussianWidth : ℕ
  saddleScale : ℕ
  truncationBudget : ℕ
deriving DecidableEq, Repr

def saddleScalePositive (d : GaussianSaddleWindowData) : Prop :=
  0 < d.saddleScale

def widthControlled (d : GaussianSaddleWindowData) : Prop :=
  d.gaussianWidth ≤ d.saddleScale + d.truncationBudget

def gaussianSaddleWindowReady (d : GaussianSaddleWindowData) : Prop :=
  saddleScalePositive d ∧ widthControlled d

def gaussianSaddleWindowBudget (d : GaussianSaddleWindowData) : ℕ :=
  d.gaussianWidth + d.saddleScale + d.truncationBudget

theorem gaussianSaddleWindowReady.scale
    {d : GaussianSaddleWindowData}
    (h : gaussianSaddleWindowReady d) :
    saddleScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem gaussianWidth_le_saddleWindowBudget
    (d : GaussianSaddleWindowData) :
    d.gaussianWidth ≤ gaussianSaddleWindowBudget d := by
  unfold gaussianSaddleWindowBudget
  omega

def sampleGaussianSaddleWindowData : GaussianSaddleWindowData :=
  { gaussianWidth := 7, saddleScale := 5, truncationBudget := 3 }

example : gaussianSaddleWindowReady sampleGaussianSaddleWindowData := by
  norm_num [gaussianSaddleWindowReady, saddleScalePositive]
  norm_num [widthControlled, sampleGaussianSaddleWindowData]

example :
    gaussianSaddleWindowBudget sampleGaussianSaddleWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for Gaussian saddle windows. -/
def gaussianSaddleWindowListReady
    (windows : List GaussianSaddleWindowData) : Bool :=
  windows.all fun d =>
    0 < d.saddleScale && d.gaussianWidth ≤ d.saddleScale + d.truncationBudget

theorem gaussianSaddleWindowList_readyWindow :
    gaussianSaddleWindowListReady
      [{ gaussianWidth := 4, saddleScale := 3, truncationBudget := 1 },
       { gaussianWidth := 7, saddleScale := 5, truncationBudget := 3 }] = true := by
  unfold gaussianSaddleWindowListReady
  native_decide

structure GaussianSaddleWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GaussianSaddleWindowSchemasBudgetCertificate.controlled
    (c : GaussianSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GaussianSaddleWindowSchemasBudgetCertificate.budgetControlled
    (c : GaussianSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GaussianSaddleWindowSchemasBudgetCertificate.Ready
    (c : GaussianSaddleWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GaussianSaddleWindowSchemasBudgetCertificate.size
    (c : GaussianSaddleWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem gaussianSaddleWindowSchemas_budgetCertificate_le_size
    (c : GaussianSaddleWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGaussianSaddleWindowSchemasBudgetCertificate :
    GaussianSaddleWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGaussianSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.controlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGaussianSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianSaddleWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGaussianSaddleWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.controlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]

example :
    sampleGaussianSaddleWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianSaddleWindowSchemasBudgetCertificate.size := by
  apply gaussianSaddleWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.controlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]
  · norm_num [GaussianSaddleWindowSchemasBudgetCertificate.budgetControlled,
      sampleGaussianSaddleWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List GaussianSaddleWindowSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGaussianSaddleWindowSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleGaussianSaddleWindowSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch8.GaussianSaddleWindowSchemas
