import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Periodic dominant singularity schemas.

The finite data records how many conjugate singularities share a modulus and
whether their period has been isolated.
-/

namespace AnalyticCombinatorics.PartB.Ch6.PeriodicSingularitiesSchemas

structure PeriodicSingularityData where
  dominantCount : ℕ
  period : ℕ
  localOrder : ℕ
deriving DecidableEq, Repr

def periodicSingularitiesReady (d : PeriodicSingularityData) : Prop :=
  0 < d.dominantCount ∧ 0 < d.period ∧ 0 < d.localOrder

def contributionBudget (d : PeriodicSingularityData) : ℕ :=
  d.dominantCount * d.localOrder

theorem periodicSingularitiesReady.period_pos {d : PeriodicSingularityData}
    (h : periodicSingularitiesReady d) :
    0 < d.period := h.2.1

theorem contributionBudget_positive {d : PeriodicSingularityData}
    (h : periodicSingularitiesReady d) :
    0 < contributionBudget d := by
  unfold contributionBudget
  exact Nat.mul_pos h.1 h.2.2

def samplePeriodicSingularity : PeriodicSingularityData :=
  { dominantCount := 4, period := 4, localOrder := 2 }

example : periodicSingularitiesReady samplePeriodicSingularity := by
  norm_num [periodicSingularitiesReady, samplePeriodicSingularity]

example : contributionBudget samplePeriodicSingularity = 8 := by
  native_decide

structure PeriodicContributionWindow where
  period : ℕ
  residueClasses : ℕ
  localOrder : ℕ
  contributionMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicContributionWindow.periodReady (w : PeriodicContributionWindow) : Prop :=
  0 < w.period

def PeriodicContributionWindow.residueControlled (w : PeriodicContributionWindow) : Prop :=
  w.residueClasses ≤ w.period + w.slack

def PeriodicContributionWindow.contributionControlled (w : PeriodicContributionWindow) : Prop :=
  w.contributionMass ≤ w.residueClasses * w.localOrder + w.slack

def PeriodicContributionWindow.ready (w : PeriodicContributionWindow) : Prop :=
  w.periodReady ∧ w.residueControlled ∧ w.contributionControlled

def PeriodicContributionWindow.certificate (w : PeriodicContributionWindow) : ℕ :=
  w.period + w.residueClasses + w.localOrder + w.contributionMass + w.slack

theorem contributionMass_le_certificate (w : PeriodicContributionWindow) :
    w.contributionMass ≤ w.certificate := by
  unfold PeriodicContributionWindow.certificate
  omega

def samplePeriodicContributionWindow : PeriodicContributionWindow :=
  { period := 4, residueClasses := 4, localOrder := 2, contributionMass := 8, slack := 0 }

example : samplePeriodicContributionWindow.ready := by
  norm_num [samplePeriodicContributionWindow, PeriodicContributionWindow.ready,
    PeriodicContributionWindow.periodReady, PeriodicContributionWindow.residueControlled,
    PeriodicContributionWindow.contributionControlled]


structure PeriodicSingularitiesSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicSingularitiesSchemasBudgetCertificate.controlled
    (c : PeriodicSingularitiesSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PeriodicSingularitiesSchemasBudgetCertificate.budgetControlled
    (c : PeriodicSingularitiesSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PeriodicSingularitiesSchemasBudgetCertificate.Ready
    (c : PeriodicSingularitiesSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PeriodicSingularitiesSchemasBudgetCertificate.size
    (c : PeriodicSingularitiesSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem periodicSingularitiesSchemas_budgetCertificate_le_size
    (c : PeriodicSingularitiesSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePeriodicSingularitiesSchemasBudgetCertificate :
    PeriodicSingularitiesSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePeriodicSingularitiesSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.controlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.budgetControlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePeriodicSingularitiesSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicSingularitiesSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePeriodicSingularitiesSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.controlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.budgetControlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]

example :
    samplePeriodicSingularitiesSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicSingularitiesSchemasBudgetCertificate.size := by
  apply periodicSingularitiesSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.controlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]
  · norm_num [PeriodicSingularitiesSchemasBudgetCertificate.budgetControlled,
      samplePeriodicSingularitiesSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PeriodicSingularitiesSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePeriodicSingularitiesSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePeriodicSingularitiesSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.PeriodicSingularitiesSchemas
