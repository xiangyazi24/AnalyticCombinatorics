import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poisson convergence schemas.

The finite record stores intensity scale, dependency budget, and error
slack for Poisson convergence templates.
-/

namespace AnalyticCombinatorics.AppC.PoissonConvergenceSchemas

structure PoissonConvergenceData where
  intensityScale : ℕ
  dependencyBudget : ℕ
  errorSlack : ℕ
deriving DecidableEq, Repr

def intensityScalePositive (d : PoissonConvergenceData) : Prop :=
  0 < d.intensityScale

def dependencyControlled (d : PoissonConvergenceData) : Prop :=
  d.dependencyBudget ≤ d.intensityScale + d.errorSlack

def poissonConvergenceReady (d : PoissonConvergenceData) : Prop :=
  intensityScalePositive d ∧ dependencyControlled d

def poissonConvergenceBudget (d : PoissonConvergenceData) : ℕ :=
  d.intensityScale + d.dependencyBudget + d.errorSlack

theorem poissonConvergenceReady.intensity
    {d : PoissonConvergenceData}
    (h : poissonConvergenceReady d) :
    intensityScalePositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem dependencyBudget_le_poissonBudget
    (d : PoissonConvergenceData) :
    d.dependencyBudget ≤ poissonConvergenceBudget d := by
  unfold poissonConvergenceBudget
  omega

def samplePoissonConvergenceData : PoissonConvergenceData :=
  { intensityScale := 6, dependencyBudget := 8, errorSlack := 3 }

example : poissonConvergenceReady samplePoissonConvergenceData := by
  norm_num [poissonConvergenceReady, intensityScalePositive]
  norm_num [dependencyControlled, samplePoissonConvergenceData]

example : poissonConvergenceBudget samplePoissonConvergenceData = 17 := by
  native_decide

structure PoissonConvergenceWindow where
  intensityWindow : ℕ
  dependencyWindow : ℕ
  errorSlack : ℕ
  poissonBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonConvergenceWindow.dependencyControlled
    (w : PoissonConvergenceWindow) : Prop :=
  w.dependencyWindow ≤ w.intensityWindow + w.errorSlack + w.slack

def poissonConvergenceWindowReady (w : PoissonConvergenceWindow) : Prop :=
  0 < w.intensityWindow ∧ w.dependencyControlled ∧
    w.poissonBudget ≤ w.intensityWindow + w.dependencyWindow + w.slack

def PoissonConvergenceWindow.certificate (w : PoissonConvergenceWindow) : ℕ :=
  w.intensityWindow + w.dependencyWindow + w.errorSlack + w.poissonBudget + w.slack

theorem poissonConvergence_poissonBudget_le_certificate
    (w : PoissonConvergenceWindow) :
    w.poissonBudget ≤ w.certificate := by
  unfold PoissonConvergenceWindow.certificate
  omega

def samplePoissonConvergenceWindow : PoissonConvergenceWindow :=
  { intensityWindow := 5, dependencyWindow := 7, errorSlack := 2,
    poissonBudget := 14, slack := 2 }

example : poissonConvergenceWindowReady samplePoissonConvergenceWindow := by
  norm_num [poissonConvergenceWindowReady,
    PoissonConvergenceWindow.dependencyControlled, samplePoissonConvergenceWindow]


structure PoissonConvergenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonConvergenceSchemasBudgetCertificate.controlled
    (c : PoissonConvergenceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonConvergenceSchemasBudgetCertificate.budgetControlled
    (c : PoissonConvergenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonConvergenceSchemasBudgetCertificate.Ready
    (c : PoissonConvergenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonConvergenceSchemasBudgetCertificate.size
    (c : PoissonConvergenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonConvergenceSchemas_budgetCertificate_le_size
    (c : PoissonConvergenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonConvergenceSchemasBudgetCertificate :
    PoissonConvergenceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoissonConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.controlled,
      samplePoissonConvergenceSchemasBudgetCertificate]
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.budgetControlled,
      samplePoissonConvergenceSchemasBudgetCertificate]

example : samplePoissonConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.controlled,
      samplePoissonConvergenceSchemasBudgetCertificate]
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.budgetControlled,
      samplePoissonConvergenceSchemasBudgetCertificate]

example :
    samplePoissonConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonConvergenceSchemasBudgetCertificate.size := by
  apply poissonConvergenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.controlled,
      samplePoissonConvergenceSchemasBudgetCertificate]
  · norm_num [PoissonConvergenceSchemasBudgetCertificate.budgetControlled,
      samplePoissonConvergenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    samplePoissonConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonConvergenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PoissonConvergenceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonConvergenceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonConvergenceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.PoissonConvergenceSchemas
