import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Gaussian comparison schemas.

The finite abstraction records variance scale, comparison budget, and
moment slack.
-/

namespace AnalyticCombinatorics.AppC.GaussianComparisonSchemas

structure GaussianComparisonData where
  varianceScale : ℕ
  comparisonBudget : ℕ
  momentSlack : ℕ
deriving DecidableEq, Repr

def varianceScalePositive (d : GaussianComparisonData) : Prop :=
  0 < d.varianceScale

def comparisonControlled (d : GaussianComparisonData) : Prop :=
  d.comparisonBudget ≤ d.varianceScale + d.momentSlack

def gaussianComparisonReady (d : GaussianComparisonData) : Prop :=
  varianceScalePositive d ∧ comparisonControlled d

def gaussianComparisonBudget (d : GaussianComparisonData) : ℕ :=
  d.varianceScale + d.comparisonBudget + d.momentSlack

theorem gaussianComparisonReady.variance {d : GaussianComparisonData}
    (h : gaussianComparisonReady d) :
    varianceScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem comparisonBudget_le_gaussianComparisonBudget
    (d : GaussianComparisonData) :
    d.comparisonBudget ≤ gaussianComparisonBudget d := by
  unfold gaussianComparisonBudget
  omega

def sampleGaussianComparisonData : GaussianComparisonData :=
  { varianceScale := 7, comparisonBudget := 9, momentSlack := 3 }

example : gaussianComparisonReady sampleGaussianComparisonData := by
  norm_num [gaussianComparisonReady, varianceScalePositive]
  norm_num [comparisonControlled, sampleGaussianComparisonData]

example : gaussianComparisonBudget sampleGaussianComparisonData = 19 := by
  native_decide

structure GaussianComparisonWindow where
  varianceWindow : ℕ
  comparisonWindow : ℕ
  momentSlack : ℕ
  gaussianBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GaussianComparisonWindow.comparisonControlled
    (w : GaussianComparisonWindow) : Prop :=
  w.comparisonWindow ≤ w.varianceWindow + w.momentSlack + w.slack

def gaussianComparisonWindowReady (w : GaussianComparisonWindow) : Prop :=
  0 < w.varianceWindow ∧ w.comparisonControlled ∧
    w.gaussianBudget ≤ w.varianceWindow + w.comparisonWindow + w.slack

def GaussianComparisonWindow.certificate (w : GaussianComparisonWindow) : ℕ :=
  w.varianceWindow + w.comparisonWindow + w.momentSlack + w.gaussianBudget + w.slack

theorem gaussianComparison_gaussianBudget_le_certificate (w : GaussianComparisonWindow) :
    w.gaussianBudget ≤ w.certificate := by
  unfold GaussianComparisonWindow.certificate
  omega

def sampleGaussianComparisonWindow : GaussianComparisonWindow :=
  { varianceWindow := 7, comparisonWindow := 9, momentSlack := 2,
    gaussianBudget := 17, slack := 1 }

example : gaussianComparisonWindowReady sampleGaussianComparisonWindow := by
  norm_num [gaussianComparisonWindowReady, GaussianComparisonWindow.comparisonControlled,
    sampleGaussianComparisonWindow]


structure GaussianComparisonSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GaussianComparisonSchemasBudgetCertificate.controlled
    (c : GaussianComparisonSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GaussianComparisonSchemasBudgetCertificate.budgetControlled
    (c : GaussianComparisonSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GaussianComparisonSchemasBudgetCertificate.Ready
    (c : GaussianComparisonSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GaussianComparisonSchemasBudgetCertificate.size
    (c : GaussianComparisonSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem gaussianComparisonSchemas_budgetCertificate_le_size
    (c : GaussianComparisonSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGaussianComparisonSchemasBudgetCertificate :
    GaussianComparisonSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGaussianComparisonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianComparisonSchemasBudgetCertificate.controlled,
      sampleGaussianComparisonSchemasBudgetCertificate]
  · norm_num [GaussianComparisonSchemasBudgetCertificate.budgetControlled,
      sampleGaussianComparisonSchemasBudgetCertificate]

example : sampleGaussianComparisonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [GaussianComparisonSchemasBudgetCertificate.controlled,
      sampleGaussianComparisonSchemasBudgetCertificate]
  · norm_num [GaussianComparisonSchemasBudgetCertificate.budgetControlled,
      sampleGaussianComparisonSchemasBudgetCertificate]

example :
    sampleGaussianComparisonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianComparisonSchemasBudgetCertificate.size := by
  apply gaussianComparisonSchemas_budgetCertificate_le_size
  constructor
  · norm_num [GaussianComparisonSchemasBudgetCertificate.controlled,
      sampleGaussianComparisonSchemasBudgetCertificate]
  · norm_num [GaussianComparisonSchemasBudgetCertificate.budgetControlled,
      sampleGaussianComparisonSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleGaussianComparisonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleGaussianComparisonSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List GaussianComparisonSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGaussianComparisonSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGaussianComparisonSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.GaussianComparisonSchemas
