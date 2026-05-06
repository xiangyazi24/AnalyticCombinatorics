import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random suffix array limit schemas.

This module records finite bookkeeping for random suffix array limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomSuffixArrayLimitSchemas

structure RandomSuffixArrayLimitData where
  suffixCount : ℕ
  arrayWindow : ℕ
  comparisonSlack : ℕ
deriving DecidableEq, Repr

def hasSuffixCount (d : RandomSuffixArrayLimitData) : Prop :=
  0 < d.suffixCount

def arrayWindowControlled (d : RandomSuffixArrayLimitData) : Prop :=
  d.arrayWindow ≤ d.suffixCount + d.comparisonSlack

def randomSuffixArrayLimitReady
    (d : RandomSuffixArrayLimitData) : Prop :=
  hasSuffixCount d ∧ arrayWindowControlled d

def randomSuffixArrayLimitBudget
    (d : RandomSuffixArrayLimitData) : ℕ :=
  d.suffixCount + d.arrayWindow + d.comparisonSlack

theorem randomSuffixArrayLimitReady.hasSuffixCount
    {d : RandomSuffixArrayLimitData}
    (h : randomSuffixArrayLimitReady d) :
    hasSuffixCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem arrayWindow_le_budget (d : RandomSuffixArrayLimitData) :
    d.arrayWindow ≤ randomSuffixArrayLimitBudget d := by
  unfold randomSuffixArrayLimitBudget
  omega

def sampleRandomSuffixArrayLimitData : RandomSuffixArrayLimitData :=
  { suffixCount := 7, arrayWindow := 9, comparisonSlack := 3 }

example : randomSuffixArrayLimitReady sampleRandomSuffixArrayLimitData := by
  norm_num [randomSuffixArrayLimitReady, hasSuffixCount]
  norm_num [arrayWindowControlled, sampleRandomSuffixArrayLimitData]

example : randomSuffixArrayLimitBudget sampleRandomSuffixArrayLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for suffix-array limit windows. -/
def randomSuffixArrayLimitListReady (windows : List RandomSuffixArrayLimitData) : Bool :=
  windows.all fun d =>
    0 < d.suffixCount && d.arrayWindow ≤ d.suffixCount + d.comparisonSlack

theorem randomSuffixArrayLimitList_readyWindow :
    randomSuffixArrayLimitListReady
      [{ suffixCount := 4, arrayWindow := 5, comparisonSlack := 1 },
       { suffixCount := 7, arrayWindow := 9, comparisonSlack := 3 }] = true := by
  unfold randomSuffixArrayLimitListReady
  native_decide


structure RandomSuffixArrayLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomSuffixArrayLimitSchemasBudgetCertificate.controlled
    (c : RandomSuffixArrayLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomSuffixArrayLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomSuffixArrayLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomSuffixArrayLimitSchemasBudgetCertificate.Ready
    (c : RandomSuffixArrayLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomSuffixArrayLimitSchemasBudgetCertificate.size
    (c : RandomSuffixArrayLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomSuffixArrayLimitSchemas_budgetCertificate_le_size
    (c : RandomSuffixArrayLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomSuffixArrayLimitSchemasBudgetCertificate :
    RandomSuffixArrayLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomSuffixArrayLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.controlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomSuffixArrayLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomSuffixArrayLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.controlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]

example :
    sampleRandomSuffixArrayLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate.size := by
  apply randomSuffixArrayLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.controlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]
  · norm_num [RandomSuffixArrayLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomSuffixArrayLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomSuffixArrayLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomSuffixArrayLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomSuffixArrayLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomSuffixArrayLimitSchemas
