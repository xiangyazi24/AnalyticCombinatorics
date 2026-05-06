import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random coalescent process schemas.

The finite record stores block count, merger budget, and scaling slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomCoalescentProcessSchemas

structure RandomCoalescentProcessData where
  blockCount : ℕ
  mergerBudget : ℕ
  scalingSlack : ℕ
deriving DecidableEq, Repr

def blockCountPositive (d : RandomCoalescentProcessData) : Prop :=
  0 < d.blockCount

def mergerBudgetControlled (d : RandomCoalescentProcessData) : Prop :=
  d.mergerBudget ≤ d.blockCount + d.scalingSlack

def randomCoalescentProcessReady (d : RandomCoalescentProcessData) : Prop :=
  blockCountPositive d ∧ mergerBudgetControlled d

def randomCoalescentProcessBudget (d : RandomCoalescentProcessData) : ℕ :=
  d.blockCount + d.mergerBudget + d.scalingSlack

theorem randomCoalescentProcessReady.blocks
    {d : RandomCoalescentProcessData}
    (h : randomCoalescentProcessReady d) :
    blockCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem mergerBudget_le_coalescentProcessBudget
    (d : RandomCoalescentProcessData) :
    d.mergerBudget ≤ randomCoalescentProcessBudget d := by
  unfold randomCoalescentProcessBudget
  omega

def sampleRandomCoalescentProcessData :
    RandomCoalescentProcessData :=
  { blockCount := 7, mergerBudget := 9, scalingSlack := 3 }

example :
    randomCoalescentProcessReady sampleRandomCoalescentProcessData := by
  norm_num [randomCoalescentProcessReady, blockCountPositive]
  norm_num [mergerBudgetControlled, sampleRandomCoalescentProcessData]

example :
    randomCoalescentProcessBudget
      sampleRandomCoalescentProcessData = 19 := by
  native_decide

/-- Finite executable readiness audit for random coalescent-process windows. -/
def randomCoalescentProcessListReady
    (windows : List RandomCoalescentProcessData) : Bool :=
  windows.all fun d =>
    0 < d.blockCount && d.mergerBudget ≤ d.blockCount + d.scalingSlack

theorem randomCoalescentProcessList_readyWindow :
    randomCoalescentProcessListReady
      [{ blockCount := 4, mergerBudget := 5, scalingSlack := 1 },
       { blockCount := 7, mergerBudget := 9, scalingSlack := 3 }] = true := by
  unfold randomCoalescentProcessListReady
  native_decide

structure RandomCoalescentProcessSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomCoalescentProcessSchemasBudgetCertificate.controlled
    (c : RandomCoalescentProcessSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomCoalescentProcessSchemasBudgetCertificate.budgetControlled
    (c : RandomCoalescentProcessSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomCoalescentProcessSchemasBudgetCertificate.Ready
    (c : RandomCoalescentProcessSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomCoalescentProcessSchemasBudgetCertificate.size
    (c : RandomCoalescentProcessSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomCoalescentProcessSchemas_budgetCertificate_le_size
    (c : RandomCoalescentProcessSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomCoalescentProcessSchemasBudgetCertificate :
    RandomCoalescentProcessSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomCoalescentProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.controlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomCoalescentProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomCoalescentProcessSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomCoalescentProcessSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.controlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]

example :
    sampleRandomCoalescentProcessSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomCoalescentProcessSchemasBudgetCertificate.size := by
  apply randomCoalescentProcessSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.controlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]
  · norm_num [RandomCoalescentProcessSchemasBudgetCertificate.budgetControlled,
      sampleRandomCoalescentProcessSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomCoalescentProcessSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomCoalescentProcessSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomCoalescentProcessSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomCoalescentProcessSchemas
