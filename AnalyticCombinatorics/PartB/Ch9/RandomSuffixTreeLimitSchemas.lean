import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random suffix tree limit schemas.

This module records finite bookkeeping for random suffix tree limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomSuffixTreeLimitSchemas

structure RandomSuffixTreeLimitData where
  suffixBudget : ℕ
  pathWindow : ℕ
  depthSlack : ℕ
deriving DecidableEq, Repr

def hasSuffixBudget (d : RandomSuffixTreeLimitData) : Prop :=
  0 < d.suffixBudget

def pathWindowControlled (d : RandomSuffixTreeLimitData) : Prop :=
  d.pathWindow ≤ d.suffixBudget + d.depthSlack

def randomSuffixTreeLimitReady (d : RandomSuffixTreeLimitData) : Prop :=
  hasSuffixBudget d ∧ pathWindowControlled d

def randomSuffixTreeLimitBudget (d : RandomSuffixTreeLimitData) : ℕ :=
  d.suffixBudget + d.pathWindow + d.depthSlack

theorem randomSuffixTreeLimitReady.hasSuffixBudget
    {d : RandomSuffixTreeLimitData}
    (h : randomSuffixTreeLimitReady d) :
    hasSuffixBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pathWindow_le_budget (d : RandomSuffixTreeLimitData) :
    d.pathWindow ≤ randomSuffixTreeLimitBudget d := by
  unfold randomSuffixTreeLimitBudget
  omega

def sampleRandomSuffixTreeLimitData : RandomSuffixTreeLimitData :=
  { suffixBudget := 7, pathWindow := 9, depthSlack := 3 }

example : randomSuffixTreeLimitReady sampleRandomSuffixTreeLimitData := by
  norm_num [randomSuffixTreeLimitReady, hasSuffixBudget]
  norm_num [pathWindowControlled, sampleRandomSuffixTreeLimitData]

example : randomSuffixTreeLimitBudget sampleRandomSuffixTreeLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for suffix-tree limit windows. -/
def randomSuffixTreeLimitListReady (windows : List RandomSuffixTreeLimitData) : Bool :=
  windows.all fun d =>
    0 < d.suffixBudget && d.pathWindow ≤ d.suffixBudget + d.depthSlack

theorem randomSuffixTreeLimitList_readyWindow :
    randomSuffixTreeLimitListReady
      [{ suffixBudget := 4, pathWindow := 5, depthSlack := 1 },
       { suffixBudget := 7, pathWindow := 9, depthSlack := 3 }] = true := by
  unfold randomSuffixTreeLimitListReady
  native_decide

structure RandomSuffixTreeLimitBudgetCertificate where
  suffixBudgetWindow : ℕ
  pathWindow : ℕ
  depthSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomSuffixTreeLimitBudgetCertificate.controlled
    (c : RandomSuffixTreeLimitBudgetCertificate) : Prop :=
  0 < c.suffixBudgetWindow ∧
    c.pathWindow ≤ c.suffixBudgetWindow + c.depthSlackWindow + c.slack

def RandomSuffixTreeLimitBudgetCertificate.budgetControlled
    (c : RandomSuffixTreeLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.suffixBudgetWindow + c.pathWindow + c.depthSlackWindow + c.slack

def RandomSuffixTreeLimitBudgetCertificate.Ready
    (c : RandomSuffixTreeLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomSuffixTreeLimitBudgetCertificate.size
    (c : RandomSuffixTreeLimitBudgetCertificate) : ℕ :=
  c.suffixBudgetWindow + c.pathWindow + c.depthSlackWindow + c.slack

theorem randomSuffixTreeLimit_budgetCertificate_le_size
    (c : RandomSuffixTreeLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomSuffixTreeLimitBudgetCertificate :
    RandomSuffixTreeLimitBudgetCertificate :=
  { suffixBudgetWindow := 7
    pathWindow := 9
    depthSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomSuffixTreeLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.controlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomSuffixTreeLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixTreeLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomSuffixTreeLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.controlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]

example :
    sampleRandomSuffixTreeLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixTreeLimitBudgetCertificate.size := by
  apply randomSuffixTreeLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.controlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]
  · norm_num [RandomSuffixTreeLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTreeLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomSuffixTreeLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomSuffixTreeLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomSuffixTreeLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomSuffixTreeLimitSchemas
