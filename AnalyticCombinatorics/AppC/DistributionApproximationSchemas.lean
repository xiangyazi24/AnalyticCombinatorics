import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Distribution approximation schemas.

The finite fields record a metric error, scale budget, and moment budget
for approximation statements.
-/

namespace AnalyticCombinatorics.AppC.DistributionApproximationSchemas

structure DistributionApproximationData where
  metricError : ℕ
  scaleBudget : ℕ
  momentBudget : ℕ
deriving DecidableEq, Repr

def scaleAvailable (d : DistributionApproximationData) : Prop :=
  0 < d.scaleBudget

def metricErrorControlled (d : DistributionApproximationData) : Prop :=
  d.metricError ≤ d.scaleBudget + d.momentBudget

def distributionApproximationReady (d : DistributionApproximationData) : Prop :=
  scaleAvailable d ∧ metricErrorControlled d

def distributionApproximationBudget (d : DistributionApproximationData) : ℕ :=
  d.metricError + d.scaleBudget + d.momentBudget

theorem distributionApproximationReady.scale {d : DistributionApproximationData}
    (h : distributionApproximationReady d) :
    scaleAvailable d ∧ metricErrorControlled d ∧
      d.metricError ≤ distributionApproximationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold distributionApproximationBudget
  omega

theorem metricError_le_approximationBudget (d : DistributionApproximationData) :
    d.metricError ≤ distributionApproximationBudget d := by
  unfold distributionApproximationBudget
  omega

def sampleDistributionApproximationData : DistributionApproximationData :=
  { metricError := 4, scaleBudget := 7, momentBudget := 2 }

example : distributionApproximationReady sampleDistributionApproximationData := by
  norm_num [distributionApproximationReady, scaleAvailable]
  norm_num [metricErrorControlled, sampleDistributionApproximationData]

example : distributionApproximationBudget sampleDistributionApproximationData = 13 := by
  native_decide

structure DistributionApproximationWindow where
  metricWindow : ℕ
  scaleWindow : ℕ
  momentWindow : ℕ
  approximationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DistributionApproximationWindow.metricControlled
    (w : DistributionApproximationWindow) : Prop :=
  w.metricWindow ≤ w.scaleWindow + w.momentWindow + w.slack

def distributionApproximationWindowReady (w : DistributionApproximationWindow) : Prop :=
  0 < w.scaleWindow ∧ w.metricControlled ∧
    w.approximationBudget ≤ w.metricWindow + w.scaleWindow + w.momentWindow + w.slack

def DistributionApproximationWindow.certificate (w : DistributionApproximationWindow) : ℕ :=
  w.metricWindow + w.scaleWindow + w.momentWindow + w.approximationBudget + w.slack

theorem distributionApproximation_budget_le_certificate
    (w : DistributionApproximationWindow) :
    w.approximationBudget ≤ w.certificate := by
  unfold DistributionApproximationWindow.certificate
  omega

def sampleDistributionApproximationWindow : DistributionApproximationWindow :=
  { metricWindow := 4, scaleWindow := 7, momentWindow := 2,
    approximationBudget := 14, slack := 1 }

example : distributionApproximationWindowReady sampleDistributionApproximationWindow := by
  norm_num [distributionApproximationWindowReady,
    DistributionApproximationWindow.metricControlled, sampleDistributionApproximationWindow]


structure DistributionApproximationSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DistributionApproximationSchemasBudgetCertificate.controlled
    (c : DistributionApproximationSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def DistributionApproximationSchemasBudgetCertificate.budgetControlled
    (c : DistributionApproximationSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DistributionApproximationSchemasBudgetCertificate.Ready
    (c : DistributionApproximationSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DistributionApproximationSchemasBudgetCertificate.size
    (c : DistributionApproximationSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem distributionApproximationSchemas_budgetCertificate_le_size
    (c : DistributionApproximationSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDistributionApproximationSchemasBudgetCertificate :
    DistributionApproximationSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDistributionApproximationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionApproximationSchemasBudgetCertificate.controlled,
      sampleDistributionApproximationSchemasBudgetCertificate]
  · norm_num [DistributionApproximationSchemasBudgetCertificate.budgetControlled,
      sampleDistributionApproximationSchemasBudgetCertificate]

example : sampleDistributionApproximationSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DistributionApproximationSchemasBudgetCertificate.controlled,
      sampleDistributionApproximationSchemasBudgetCertificate]
  · norm_num [DistributionApproximationSchemasBudgetCertificate.budgetControlled,
      sampleDistributionApproximationSchemasBudgetCertificate]

example :
    sampleDistributionApproximationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionApproximationSchemasBudgetCertificate.size := by
  apply distributionApproximationSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DistributionApproximationSchemasBudgetCertificate.controlled,
      sampleDistributionApproximationSchemasBudgetCertificate]
  · norm_num [DistributionApproximationSchemasBudgetCertificate.budgetControlled,
      sampleDistributionApproximationSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleDistributionApproximationSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDistributionApproximationSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DistributionApproximationSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDistributionApproximationSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleDistributionApproximationSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.DistributionApproximationSchemas
