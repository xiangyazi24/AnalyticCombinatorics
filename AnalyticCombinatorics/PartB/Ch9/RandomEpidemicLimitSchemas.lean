import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random epidemic limit schemas.

This module records finite bookkeeping for epidemic-limit windows: a positive
population size controls infection budget with scaling slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomEpidemicLimitSchemas

structure RandomEpidemicLimitData where
  populationSize : ℕ
  infectionBudget : ℕ
  scalingSlack : ℕ
deriving DecidableEq, Repr

def hasPopulationSize (d : RandomEpidemicLimitData) : Prop :=
  0 < d.populationSize

def infectionBudgetControlled (d : RandomEpidemicLimitData) : Prop :=
  d.infectionBudget ≤ d.populationSize + d.scalingSlack

def randomEpidemicLimitReady (d : RandomEpidemicLimitData) : Prop :=
  hasPopulationSize d ∧ infectionBudgetControlled d

def randomEpidemicLimitBudget (d : RandomEpidemicLimitData) : ℕ :=
  d.populationSize + d.infectionBudget + d.scalingSlack

theorem randomEpidemicLimitReady.hasPopulationSize
    {d : RandomEpidemicLimitData}
    (h : randomEpidemicLimitReady d) :
    hasPopulationSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem infectionBudget_le_budget (d : RandomEpidemicLimitData) :
    d.infectionBudget ≤ randomEpidemicLimitBudget d := by
  unfold randomEpidemicLimitBudget
  omega

def sampleRandomEpidemicLimitData : RandomEpidemicLimitData :=
  { populationSize := 7, infectionBudget := 9, scalingSlack := 3 }

example : randomEpidemicLimitReady sampleRandomEpidemicLimitData := by
  norm_num [randomEpidemicLimitReady, hasPopulationSize]
  norm_num [infectionBudgetControlled, sampleRandomEpidemicLimitData]

example : randomEpidemicLimitBudget sampleRandomEpidemicLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for epidemic-limit windows. -/
def randomEpidemicLimitListReady
    (windows : List RandomEpidemicLimitData) : Bool :=
  windows.all fun d =>
    0 < d.populationSize && d.infectionBudget ≤ d.populationSize + d.scalingSlack

theorem randomEpidemicLimitList_readyWindow :
    randomEpidemicLimitListReady
      [{ populationSize := 4, infectionBudget := 5, scalingSlack := 1 },
       { populationSize := 7, infectionBudget := 9, scalingSlack := 3 }] = true := by
  unfold randomEpidemicLimitListReady
  native_decide

structure RandomEpidemicLimitBudgetCertificate where
  populationSizeWindow : ℕ
  infectionBudgetWindow : ℕ
  scalingSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomEpidemicLimitBudgetCertificate.controlled
    (c : RandomEpidemicLimitBudgetCertificate) : Prop :=
  0 < c.populationSizeWindow ∧
    c.infectionBudgetWindow ≤
      c.populationSizeWindow + c.scalingSlackWindow + c.slack

def RandomEpidemicLimitBudgetCertificate.budgetControlled
    (c : RandomEpidemicLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.populationSizeWindow + c.infectionBudgetWindow + c.scalingSlackWindow +
      c.slack

def RandomEpidemicLimitBudgetCertificate.Ready
    (c : RandomEpidemicLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomEpidemicLimitBudgetCertificate.size
    (c : RandomEpidemicLimitBudgetCertificate) : ℕ :=
  c.populationSizeWindow + c.infectionBudgetWindow + c.scalingSlackWindow +
    c.slack

theorem randomEpidemicLimit_budgetCertificate_le_size
    (c : RandomEpidemicLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomEpidemicLimitBudgetCertificate :
    RandomEpidemicLimitBudgetCertificate :=
  { populationSizeWindow := 7
    infectionBudgetWindow := 9
    scalingSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomEpidemicLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomEpidemicLimitBudgetCertificate.controlled,
      sampleRandomEpidemicLimitBudgetCertificate]
  · norm_num [RandomEpidemicLimitBudgetCertificate.budgetControlled,
      sampleRandomEpidemicLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomEpidemicLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomEpidemicLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomEpidemicLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomEpidemicLimitBudgetCertificate.controlled,
      sampleRandomEpidemicLimitBudgetCertificate]
  · norm_num [RandomEpidemicLimitBudgetCertificate.budgetControlled,
      sampleRandomEpidemicLimitBudgetCertificate]

example :
    sampleRandomEpidemicLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomEpidemicLimitBudgetCertificate.size := by
  apply randomEpidemicLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomEpidemicLimitBudgetCertificate.controlled,
      sampleRandomEpidemicLimitBudgetCertificate]
  · norm_num [RandomEpidemicLimitBudgetCertificate.budgetControlled,
      sampleRandomEpidemicLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomEpidemicLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomEpidemicLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomEpidemicLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomEpidemicLimitSchemas
