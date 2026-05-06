import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bivariate quasi-power remainder schemas.

This module records finite bookkeeping for bivariate quasi-power remainders.
-/

namespace AnalyticCombinatorics.PartA.Ch3.BivariateQuasiPowerRemainderSchemas

structure BivariateQuasiPowerRemainderData where
  parameterScale : ℕ
  remainderWindow : ℕ
  quasiPowerSlack : ℕ
deriving DecidableEq, Repr

def hasParameterScale
    (d : BivariateQuasiPowerRemainderData) : Prop :=
  0 < d.parameterScale

def remainderWindowControlled
    (d : BivariateQuasiPowerRemainderData) : Prop :=
  d.remainderWindow ≤ d.parameterScale + d.quasiPowerSlack

def bivariateQuasiPowerRemainderReady
    (d : BivariateQuasiPowerRemainderData) : Prop :=
  hasParameterScale d ∧ remainderWindowControlled d

def bivariateQuasiPowerRemainderBudget
    (d : BivariateQuasiPowerRemainderData) : ℕ :=
  d.parameterScale + d.remainderWindow + d.quasiPowerSlack

theorem bivariateQuasiPowerRemainderReady.hasParameterScale
    {d : BivariateQuasiPowerRemainderData}
    (h : bivariateQuasiPowerRemainderReady d) :
    hasParameterScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : BivariateQuasiPowerRemainderData) :
    d.remainderWindow ≤ bivariateQuasiPowerRemainderBudget d := by
  unfold bivariateQuasiPowerRemainderBudget
  omega

def sampleBivariateQuasiPowerRemainderData :
    BivariateQuasiPowerRemainderData :=
  { parameterScale := 7, remainderWindow := 9, quasiPowerSlack := 3 }

example : bivariateQuasiPowerRemainderReady
    sampleBivariateQuasiPowerRemainderData := by
  norm_num [bivariateQuasiPowerRemainderReady, hasParameterScale]
  norm_num [remainderWindowControlled, sampleBivariateQuasiPowerRemainderData]

example :
    bivariateQuasiPowerRemainderBudget sampleBivariateQuasiPowerRemainderData = 19 := by
  native_decide


structure BivariateQuasiPowerRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BivariateQuasiPowerRemainderSchemasBudgetCertificate.controlled
    (c : BivariateQuasiPowerRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BivariateQuasiPowerRemainderSchemasBudgetCertificate.budgetControlled
    (c : BivariateQuasiPowerRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BivariateQuasiPowerRemainderSchemasBudgetCertificate.Ready
    (c : BivariateQuasiPowerRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BivariateQuasiPowerRemainderSchemasBudgetCertificate.size
    (c : BivariateQuasiPowerRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem bivariateQuasiPowerRemainderSchemas_budgetCertificate_le_size
    (c : BivariateQuasiPowerRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate :
    BivariateQuasiPowerRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.controlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.controlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]

example :
    sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate.size := by
  apply bivariateQuasiPowerRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.controlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]
  · norm_num [BivariateQuasiPowerRemainderSchemasBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BivariateQuasiPowerRemainderSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBivariateQuasiPowerRemainderSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.BivariateQuasiPowerRemainderSchemas
