import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Compound Poisson schemas.

The finite record stores cluster intensity, jump budget, and dependency
slack.
-/

namespace AnalyticCombinatorics.AppC.CompoundPoissonSchemas

structure CompoundPoissonData where
  clusterIntensity : ℕ
  jumpBudget : ℕ
  dependencySlack : ℕ
deriving DecidableEq, Repr

def clusterIntensityPositive (d : CompoundPoissonData) : Prop :=
  0 < d.clusterIntensity

def jumpsControlled (d : CompoundPoissonData) : Prop :=
  d.jumpBudget ≤ d.clusterIntensity + d.dependencySlack

def compoundPoissonReady (d : CompoundPoissonData) : Prop :=
  clusterIntensityPositive d ∧ jumpsControlled d

def compoundPoissonBudget (d : CompoundPoissonData) : ℕ :=
  d.clusterIntensity + d.jumpBudget + d.dependencySlack

theorem compoundPoissonReady.intensity {d : CompoundPoissonData}
    (h : compoundPoissonReady d) :
    clusterIntensityPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem jumpBudget_le_compoundPoissonBudget (d : CompoundPoissonData) :
    d.jumpBudget ≤ compoundPoissonBudget d := by
  unfold compoundPoissonBudget
  omega

def sampleCompoundPoissonData : CompoundPoissonData :=
  { clusterIntensity := 6, jumpBudget := 8, dependencySlack := 3 }

example : compoundPoissonReady sampleCompoundPoissonData := by
  norm_num [compoundPoissonReady, clusterIntensityPositive]
  norm_num [jumpsControlled, sampleCompoundPoissonData]

example : compoundPoissonBudget sampleCompoundPoissonData = 17 := by
  native_decide

structure CompoundPoissonWindow where
  clusterIntensity : ℕ
  jumpBudget : ℕ
  dependencySlack : ℕ
  clusterBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompoundPoissonWindow.jumpsControlled (w : CompoundPoissonWindow) : Prop :=
  w.jumpBudget ≤ w.clusterIntensity + w.dependencySlack + w.slack

def CompoundPoissonWindow.clusterControlled (w : CompoundPoissonWindow) : Prop :=
  w.clusterBudget ≤ w.clusterIntensity + w.jumpBudget + w.dependencySlack + w.slack

def compoundPoissonWindowReady (w : CompoundPoissonWindow) : Prop :=
  0 < w.clusterIntensity ∧
    w.jumpsControlled ∧
    w.clusterControlled

def CompoundPoissonWindow.certificate (w : CompoundPoissonWindow) : ℕ :=
  w.clusterIntensity + w.jumpBudget + w.dependencySlack + w.slack

theorem compoundPoisson_clusterBudget_le_certificate {w : CompoundPoissonWindow}
    (h : compoundPoissonWindowReady w) :
    w.clusterBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcluster⟩
  exact hcluster

def sampleCompoundPoissonWindow : CompoundPoissonWindow :=
  { clusterIntensity := 6, jumpBudget := 8, dependencySlack := 3, clusterBudget := 16,
    slack := 0 }

example : compoundPoissonWindowReady sampleCompoundPoissonWindow := by
  norm_num [compoundPoissonWindowReady, CompoundPoissonWindow.jumpsControlled,
    CompoundPoissonWindow.clusterControlled, sampleCompoundPoissonWindow]

example : sampleCompoundPoissonWindow.certificate = 17 := by
  native_decide


structure CompoundPoissonSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompoundPoissonSchemasBudgetCertificate.controlled
    (c : CompoundPoissonSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompoundPoissonSchemasBudgetCertificate.budgetControlled
    (c : CompoundPoissonSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompoundPoissonSchemasBudgetCertificate.Ready
    (c : CompoundPoissonSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompoundPoissonSchemasBudgetCertificate.size
    (c : CompoundPoissonSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compoundPoissonSchemas_budgetCertificate_le_size
    (c : CompoundPoissonSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompoundPoissonSchemasBudgetCertificate :
    CompoundPoissonSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCompoundPoissonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompoundPoissonSchemasBudgetCertificate.controlled,
      sampleCompoundPoissonSchemasBudgetCertificate]
  · norm_num [CompoundPoissonSchemasBudgetCertificate.budgetControlled,
      sampleCompoundPoissonSchemasBudgetCertificate]

example : sampleCompoundPoissonSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CompoundPoissonSchemasBudgetCertificate.controlled,
      sampleCompoundPoissonSchemasBudgetCertificate]
  · norm_num [CompoundPoissonSchemasBudgetCertificate.budgetControlled,
      sampleCompoundPoissonSchemasBudgetCertificate]

example :
    sampleCompoundPoissonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompoundPoissonSchemasBudgetCertificate.size := by
  apply compoundPoissonSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CompoundPoissonSchemasBudgetCertificate.controlled,
      sampleCompoundPoissonSchemasBudgetCertificate]
  · norm_num [CompoundPoissonSchemasBudgetCertificate.budgetControlled,
      sampleCompoundPoissonSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleCompoundPoissonSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCompoundPoissonSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompoundPoissonSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompoundPoissonSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompoundPoissonSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.CompoundPoissonSchemas
