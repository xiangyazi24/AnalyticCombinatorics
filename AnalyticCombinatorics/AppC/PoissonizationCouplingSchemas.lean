import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Poissonization coupling schemas.

This module records finite bookkeeping for Poissonization couplings.
-/

namespace AnalyticCombinatorics.AppC.PoissonizationCouplingSchemas

structure PoissonizationCouplingData where
  poissonScale : ℕ
  couplingWindow : ℕ
  poissonSlack : ℕ
deriving DecidableEq, Repr

def hasPoissonScale (d : PoissonizationCouplingData) : Prop :=
  0 < d.poissonScale

def couplingWindowControlled (d : PoissonizationCouplingData) : Prop :=
  d.couplingWindow ≤ d.poissonScale + d.poissonSlack

def poissonizationCouplingReady
    (d : PoissonizationCouplingData) : Prop :=
  hasPoissonScale d ∧ couplingWindowControlled d

def poissonizationCouplingBudget
    (d : PoissonizationCouplingData) : ℕ :=
  d.poissonScale + d.couplingWindow + d.poissonSlack

theorem poissonizationCouplingReady.hasPoissonScale
    {d : PoissonizationCouplingData}
    (h : poissonizationCouplingReady d) :
    hasPoissonScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : PoissonizationCouplingData) :
    d.couplingWindow ≤ poissonizationCouplingBudget d := by
  unfold poissonizationCouplingBudget
  omega

def samplePoissonizationCouplingData : PoissonizationCouplingData :=
  { poissonScale := 6, couplingWindow := 8, poissonSlack := 3 }

example : poissonizationCouplingReady samplePoissonizationCouplingData := by
  norm_num [poissonizationCouplingReady, hasPoissonScale]
  norm_num [couplingWindowControlled, samplePoissonizationCouplingData]

example :
    poissonizationCouplingBudget samplePoissonizationCouplingData = 17 := by
  native_decide

structure PoissonizationCouplingWindow where
  poissonWindow : ℕ
  couplingWindow : ℕ
  poissonSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonizationCouplingWindow.couplingControlled
    (w : PoissonizationCouplingWindow) : Prop :=
  w.couplingWindow ≤ w.poissonWindow + w.poissonSlack + w.slack

def poissonizationCouplingWindowReady (w : PoissonizationCouplingWindow) : Prop :=
  0 < w.poissonWindow ∧ w.couplingControlled ∧
    w.couplingBudget ≤ w.poissonWindow + w.couplingWindow + w.slack

def PoissonizationCouplingWindow.certificate
    (w : PoissonizationCouplingWindow) : ℕ :=
  w.poissonWindow + w.couplingWindow + w.poissonSlack + w.couplingBudget + w.slack

theorem poissonizationCoupling_couplingBudget_le_certificate
    (w : PoissonizationCouplingWindow) :
    w.couplingBudget ≤ w.certificate := by
  unfold PoissonizationCouplingWindow.certificate
  omega

def samplePoissonizationCouplingWindow : PoissonizationCouplingWindow :=
  { poissonWindow := 5, couplingWindow := 7, poissonSlack := 2,
    couplingBudget := 14, slack := 2 }

example : poissonizationCouplingWindowReady samplePoissonizationCouplingWindow := by
  norm_num [poissonizationCouplingWindowReady,
    PoissonizationCouplingWindow.couplingControlled, samplePoissonizationCouplingWindow]


structure PoissonizationCouplingSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PoissonizationCouplingSchemasBudgetCertificate.controlled
    (c : PoissonizationCouplingSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PoissonizationCouplingSchemasBudgetCertificate.budgetControlled
    (c : PoissonizationCouplingSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PoissonizationCouplingSchemasBudgetCertificate.Ready
    (c : PoissonizationCouplingSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PoissonizationCouplingSchemasBudgetCertificate.size
    (c : PoissonizationCouplingSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem poissonizationCouplingSchemas_budgetCertificate_le_size
    (c : PoissonizationCouplingSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePoissonizationCouplingSchemasBudgetCertificate :
    PoissonizationCouplingSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePoissonizationCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.controlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]

example : samplePoissonizationCouplingSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.controlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]

example :
    samplePoissonizationCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonizationCouplingSchemasBudgetCertificate.size := by
  apply poissonizationCouplingSchemas_budgetCertificate_le_size
  constructor
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.controlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]
  · norm_num [PoissonizationCouplingSchemasBudgetCertificate.budgetControlled,
      samplePoissonizationCouplingSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    samplePoissonizationCouplingSchemasBudgetCertificate.certificateBudgetWindow ≤
      samplePoissonizationCouplingSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List PoissonizationCouplingSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePoissonizationCouplingSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePoissonizationCouplingSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.PoissonizationCouplingSchemas
