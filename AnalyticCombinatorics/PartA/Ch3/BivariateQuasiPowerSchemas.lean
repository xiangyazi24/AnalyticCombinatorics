import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bivariate quasi-power schemas.

This module records finite bookkeeping for bivariate quasi-power windows.
-/

namespace AnalyticCombinatorics.PartA.Ch3.BivariateQuasiPowerSchemas

structure BivariateQuasiPowerData where
  variablePairs : ℕ
  cumulantWindow : ℕ
  analyticSlack : ℕ
deriving DecidableEq, Repr

def hasVariablePairs (d : BivariateQuasiPowerData) : Prop :=
  0 < d.variablePairs

def cumulantWindowControlled (d : BivariateQuasiPowerData) : Prop :=
  d.cumulantWindow ≤ d.variablePairs + d.analyticSlack

def bivariateQuasiPowerReady (d : BivariateQuasiPowerData) : Prop :=
  hasVariablePairs d ∧ cumulantWindowControlled d

def bivariateQuasiPowerBudget (d : BivariateQuasiPowerData) : ℕ :=
  d.variablePairs + d.cumulantWindow + d.analyticSlack

theorem bivariateQuasiPowerReady.hasVariablePairs
    {d : BivariateQuasiPowerData}
    (h : bivariateQuasiPowerReady d) :
    hasVariablePairs d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem cumulantWindow_le_budget (d : BivariateQuasiPowerData) :
    d.cumulantWindow ≤ bivariateQuasiPowerBudget d := by
  unfold bivariateQuasiPowerBudget
  omega

def sampleBivariateQuasiPowerData : BivariateQuasiPowerData :=
  { variablePairs := 6, cumulantWindow := 8, analyticSlack := 3 }

example : bivariateQuasiPowerReady sampleBivariateQuasiPowerData := by
  norm_num [bivariateQuasiPowerReady, hasVariablePairs]
  norm_num [cumulantWindowControlled, sampleBivariateQuasiPowerData]

example : bivariateQuasiPowerBudget sampleBivariateQuasiPowerData = 17 := by
  native_decide

structure BivariateQuasiPowerBudgetCertificate where
  variablePairWindow : ℕ
  cumulantWindow : ℕ
  analyticSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BivariateQuasiPowerBudgetCertificate.controlled
    (c : BivariateQuasiPowerBudgetCertificate) : Prop :=
  0 < c.variablePairWindow ∧
    c.cumulantWindow ≤ c.variablePairWindow + c.analyticSlackWindow + c.slack

def BivariateQuasiPowerBudgetCertificate.budgetControlled
    (c : BivariateQuasiPowerBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.variablePairWindow + c.cumulantWindow + c.analyticSlackWindow + c.slack

def BivariateQuasiPowerBudgetCertificate.Ready
    (c : BivariateQuasiPowerBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BivariateQuasiPowerBudgetCertificate.size
    (c : BivariateQuasiPowerBudgetCertificate) : ℕ :=
  c.variablePairWindow + c.cumulantWindow + c.analyticSlackWindow + c.slack

theorem bivariateQuasiPower_budgetCertificate_le_size
    (c : BivariateQuasiPowerBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBivariateQuasiPowerBudgetCertificate :
    BivariateQuasiPowerBudgetCertificate :=
  { variablePairWindow := 6
    cumulantWindow := 8
    analyticSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBivariateQuasiPowerBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateQuasiPowerBudgetCertificate.controlled,
      sampleBivariateQuasiPowerBudgetCertificate]
  · norm_num [BivariateQuasiPowerBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBivariateQuasiPowerBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateQuasiPowerBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBivariateQuasiPowerBudgetCertificate.Ready := by
  constructor
  · norm_num [BivariateQuasiPowerBudgetCertificate.controlled,
      sampleBivariateQuasiPowerBudgetCertificate]
  · norm_num [BivariateQuasiPowerBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerBudgetCertificate]

example :
    sampleBivariateQuasiPowerBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateQuasiPowerBudgetCertificate.size := by
  apply bivariateQuasiPower_budgetCertificate_le_size
  constructor
  · norm_num [BivariateQuasiPowerBudgetCertificate.controlled,
      sampleBivariateQuasiPowerBudgetCertificate]
  · norm_num [BivariateQuasiPowerBudgetCertificate.budgetControlled,
      sampleBivariateQuasiPowerBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List BivariateQuasiPowerBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBivariateQuasiPowerBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBivariateQuasiPowerBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.BivariateQuasiPowerSchemas
