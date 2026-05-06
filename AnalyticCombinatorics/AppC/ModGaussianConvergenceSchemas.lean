import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mod-Gaussian convergence schemas.

The finite schema stores variance scale, residual transform budget, and
uniformity slack.
-/

namespace AnalyticCombinatorics.AppC.ModGaussianConvergenceSchemas

structure ModGaussianData where
  varianceScale : ℕ
  residualBudget : ℕ
  uniformitySlack : ℕ
deriving DecidableEq, Repr

def varianceScalePositive (d : ModGaussianData) : Prop :=
  0 < d.varianceScale

def residualControlled (d : ModGaussianData) : Prop :=
  d.residualBudget ≤ d.varianceScale + d.uniformitySlack

def modGaussianReady (d : ModGaussianData) : Prop :=
  varianceScalePositive d ∧ residualControlled d

def modGaussianBudget (d : ModGaussianData) : ℕ :=
  d.varianceScale + d.residualBudget + d.uniformitySlack

theorem modGaussianReady.variance {d : ModGaussianData}
    (h : modGaussianReady d) :
    varianceScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem residualBudget_le_modGaussianBudget (d : ModGaussianData) :
    d.residualBudget ≤ modGaussianBudget d := by
  unfold modGaussianBudget
  omega

def sampleModGaussianData : ModGaussianData :=
  { varianceScale := 9, residualBudget := 11, uniformitySlack := 3 }

example : modGaussianReady sampleModGaussianData := by
  norm_num [modGaussianReady, varianceScalePositive]
  norm_num [residualControlled, sampleModGaussianData]

example : modGaussianBudget sampleModGaussianData = 23 := by
  native_decide

structure ModGaussianWindow where
  varianceScale : ℕ
  residualBudget : ℕ
  uniformitySlack : ℕ
  transformBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModGaussianWindow.residualControlled (w : ModGaussianWindow) : Prop :=
  w.residualBudget ≤ w.varianceScale + w.uniformitySlack + w.slack

def ModGaussianWindow.transformControlled (w : ModGaussianWindow) : Prop :=
  w.transformBudget ≤ w.varianceScale + w.residualBudget + w.uniformitySlack + w.slack

def modGaussianWindowReady (w : ModGaussianWindow) : Prop :=
  0 < w.varianceScale ∧
    w.residualControlled ∧
    w.transformControlled

def ModGaussianWindow.certificate (w : ModGaussianWindow) : ℕ :=
  w.varianceScale + w.residualBudget + w.uniformitySlack + w.slack

theorem modGaussian_transformBudget_le_certificate {w : ModGaussianWindow}
    (h : modGaussianWindowReady w) :
    w.transformBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransform⟩
  exact htransform

def sampleModGaussianWindow : ModGaussianWindow :=
  { varianceScale := 9, residualBudget := 11, uniformitySlack := 3, transformBudget := 22,
    slack := 0 }

example : modGaussianWindowReady sampleModGaussianWindow := by
  norm_num [modGaussianWindowReady, ModGaussianWindow.residualControlled,
    ModGaussianWindow.transformControlled, sampleModGaussianWindow]

example : sampleModGaussianWindow.certificate = 23 := by
  native_decide


structure ModGaussianConvergenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ModGaussianConvergenceSchemasBudgetCertificate.controlled
    (c : ModGaussianConvergenceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ModGaussianConvergenceSchemasBudgetCertificate.budgetControlled
    (c : ModGaussianConvergenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ModGaussianConvergenceSchemasBudgetCertificate.Ready
    (c : ModGaussianConvergenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ModGaussianConvergenceSchemasBudgetCertificate.size
    (c : ModGaussianConvergenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem modGaussianConvergenceSchemas_budgetCertificate_le_size
    (c : ModGaussianConvergenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleModGaussianConvergenceSchemasBudgetCertificate :
    ModGaussianConvergenceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleModGaussianConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.controlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]

example : sampleModGaussianConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.controlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]

example :
    sampleModGaussianConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModGaussianConvergenceSchemasBudgetCertificate.size := by
  apply modGaussianConvergenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.controlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]
  · norm_num [ModGaussianConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleModGaussianConvergenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleModGaussianConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleModGaussianConvergenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ModGaussianConvergenceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleModGaussianConvergenceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleModGaussianConvergenceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ModGaussianConvergenceSchemas
