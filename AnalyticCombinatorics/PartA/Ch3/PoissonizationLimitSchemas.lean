import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poissonization limit schema bookkeeping.

The finite record tracks Poisson parameter, depoissonization error, and
variance budgets.
-/

namespace AnalyticCombinatorics.PartA.Ch3.PoissonizationLimitSchemas

structure PoissonizationData where
  parameterBudget : ℕ
  varianceBudget : ℕ
  depoissonizationError : ℕ
deriving DecidableEq, Repr

def positiveParameter (d : PoissonizationData) : Prop :=
  0 < d.parameterBudget

def positiveVariance (d : PoissonizationData) : Prop :=
  0 < d.varianceBudget

def poissonizationReady (d : PoissonizationData) : Prop :=
  positiveParameter d ∧ positiveVariance d

def totalPoissonBudget (d : PoissonizationData) : ℕ :=
  d.parameterBudget + d.varianceBudget + d.depoissonizationError

theorem poissonizationReady.parameter {d : PoissonizationData}
    (h : poissonizationReady d) :
    positiveParameter d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem parameterBudget_le_total (d : PoissonizationData) :
    d.parameterBudget ≤ totalPoissonBudget d := by
  unfold totalPoissonBudget
  omega

def samplePoissonization : PoissonizationData :=
  { parameterBudget := 5, varianceBudget := 6, depoissonizationError := 2 }

example : poissonizationReady samplePoissonization := by
  norm_num [poissonizationReady, positiveParameter, positiveVariance, samplePoissonization]

example : totalPoissonBudget samplePoissonization = 13 := by
  native_decide

structure PoissonizationWindow where
  parameterBudget : ℕ
  varianceBudget : ℕ
  depoissonizationError : ℕ
  poissonMass : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonizationWindow.errorControlled (w : PoissonizationWindow) : Prop :=
  w.depoissonizationError ≤ w.parameterBudget + w.varianceBudget + w.slack

def PoissonizationWindow.massControlled (w : PoissonizationWindow) : Prop :=
  w.poissonMass ≤ w.parameterBudget + w.varianceBudget + w.depoissonizationError + w.slack

def poissonizationWindowReady (w : PoissonizationWindow) : Prop :=
  0 < w.parameterBudget ∧
    0 < w.varianceBudget ∧
    w.errorControlled ∧
    w.massControlled

def PoissonizationWindow.certificate (w : PoissonizationWindow) : ℕ :=
  w.parameterBudget + w.varianceBudget + w.depoissonizationError + w.slack

theorem poissonMass_le_certificate {w : PoissonizationWindow}
    (h : poissonizationWindowReady w) :
    w.poissonMass ≤ w.certificate := by
  rcases h with ⟨_, _, _, hmass⟩
  exact hmass

def samplePoissonizationWindow : PoissonizationWindow :=
  { parameterBudget := 5, varianceBudget := 6, depoissonizationError := 2, poissonMass := 10,
    slack := 0 }

example : poissonizationWindowReady samplePoissonizationWindow := by
  norm_num [poissonizationWindowReady, PoissonizationWindow.errorControlled,
    PoissonizationWindow.massControlled, samplePoissonizationWindow]

example : samplePoissonizationWindow.certificate = 13 := by
  native_decide


structure PoissonizationLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonizationLimitSchemasBudgetCertificate.controlled
    (c : PoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonizationLimitSchemasBudgetCertificate.budgetControlled
    (c : PoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonizationLimitSchemasBudgetCertificate.Ready
    (c : PoissonizationLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonizationLimitSchemasBudgetCertificate.size
    (c : PoissonizationLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonizationLimitSchemas_budgetCertificate_le_size
    (c : PoissonizationLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonizationLimitSchemasBudgetCertificate :
    PoissonizationLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoissonizationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.controlled,
      samplePoissonizationLimitSchemasBudgetCertificate]
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePoissonizationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonizationLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePoissonizationLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.controlled,
      samplePoissonizationLimitSchemasBudgetCertificate]
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationLimitSchemasBudgetCertificate]

example :
    samplePoissonizationLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonizationLimitSchemasBudgetCertificate.size := by
  apply poissonizationLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.controlled,
      samplePoissonizationLimitSchemasBudgetCertificate]
  · norm_num [PoissonizationLimitSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PoissonizationLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonizationLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonizationLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.PoissonizationLimitSchemas
