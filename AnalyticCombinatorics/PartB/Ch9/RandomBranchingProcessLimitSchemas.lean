import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random branching process limit schemas.

The finite record stores generation count, offspring budget, and
extinction slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomBranchingProcessLimitSchemas

structure RandomBranchingProcessLimitData where
  generationCount : ℕ
  offspringBudget : ℕ
  extinctionSlack : ℕ
deriving DecidableEq, Repr

def generationCountPositive (d : RandomBranchingProcessLimitData) : Prop :=
  0 < d.generationCount

def offspringBudgetControlled
    (d : RandomBranchingProcessLimitData) : Prop :=
  d.offspringBudget ≤ d.generationCount + d.extinctionSlack

def randomBranchingProcessLimitReady
    (d : RandomBranchingProcessLimitData) : Prop :=
  generationCountPositive d ∧ offspringBudgetControlled d

def randomBranchingProcessLimitBudget
    (d : RandomBranchingProcessLimitData) : ℕ :=
  d.generationCount + d.offspringBudget + d.extinctionSlack

theorem randomBranchingProcessLimitReady.generations
    {d : RandomBranchingProcessLimitData}
    (h : randomBranchingProcessLimitReady d) :
    generationCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem offspringBudget_le_branchingProcessBudget
    (d : RandomBranchingProcessLimitData) :
    d.offspringBudget ≤ randomBranchingProcessLimitBudget d := by
  unfold randomBranchingProcessLimitBudget
  omega

def sampleRandomBranchingProcessLimitData :
    RandomBranchingProcessLimitData :=
  { generationCount := 6, offspringBudget := 8, extinctionSlack := 3 }

example :
    randomBranchingProcessLimitReady
      sampleRandomBranchingProcessLimitData := by
  norm_num [randomBranchingProcessLimitReady, generationCountPositive]
  norm_num [offspringBudgetControlled, sampleRandomBranchingProcessLimitData]

example :
    randomBranchingProcessLimitBudget
      sampleRandomBranchingProcessLimitData = 17 := by
  native_decide

/-- Finite executable readiness audit for random branching-process windows. -/
def randomBranchingProcessLimitListReady
    (windows : List RandomBranchingProcessLimitData) : Bool :=
  windows.all fun d =>
    0 < d.generationCount &&
      d.offspringBudget ≤ d.generationCount + d.extinctionSlack

theorem randomBranchingProcessLimitList_readyWindow :
    randomBranchingProcessLimitListReady
      [{ generationCount := 4, offspringBudget := 5, extinctionSlack := 1 },
       { generationCount := 6, offspringBudget := 8, extinctionSlack := 3 }] =
      true := by
  unfold randomBranchingProcessLimitListReady
  native_decide

structure RandomBranchingProcessLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomBranchingProcessLimitSchemasBudgetCertificate.controlled
    (c : RandomBranchingProcessLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomBranchingProcessLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomBranchingProcessLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomBranchingProcessLimitSchemasBudgetCertificate.Ready
    (c : RandomBranchingProcessLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomBranchingProcessLimitSchemasBudgetCertificate.size
    (c : RandomBranchingProcessLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomBranchingProcessLimitSchemas_budgetCertificate_le_size
    (c : RandomBranchingProcessLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomBranchingProcessLimitSchemasBudgetCertificate :
    RandomBranchingProcessLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomBranchingProcessLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.controlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomBranchingProcessLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomBranchingProcessLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.controlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]

example :
    sampleRandomBranchingProcessLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate.size := by
  apply randomBranchingProcessLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.controlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]
  · norm_num [RandomBranchingProcessLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomBranchingProcessLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomBranchingProcessLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomBranchingProcessLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomBranchingProcessLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomBranchingProcessLimitSchemas
