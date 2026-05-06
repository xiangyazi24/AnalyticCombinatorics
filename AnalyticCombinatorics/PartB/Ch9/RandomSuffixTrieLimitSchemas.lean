import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random suffix trie limit schemas.

This module records finite bookkeeping for suffix trie limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomSuffixTrieLimitSchemas

structure RandomSuffixTrieLimitData where
  suffixNodes : ℕ
  profileWindow : ℕ
  suffixSlack : ℕ
deriving DecidableEq, Repr

def hasSuffixNodes (d : RandomSuffixTrieLimitData) : Prop :=
  0 < d.suffixNodes

def profileWindowControlled (d : RandomSuffixTrieLimitData) : Prop :=
  d.profileWindow ≤ d.suffixNodes + d.suffixSlack

def randomSuffixTrieLimitReady (d : RandomSuffixTrieLimitData) : Prop :=
  hasSuffixNodes d ∧ profileWindowControlled d

def randomSuffixTrieLimitBudget (d : RandomSuffixTrieLimitData) : ℕ :=
  d.suffixNodes + d.profileWindow + d.suffixSlack

theorem randomSuffixTrieLimitReady.hasSuffixNodes
    {d : RandomSuffixTrieLimitData}
    (h : randomSuffixTrieLimitReady d) :
    hasSuffixNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWindow_le_budget (d : RandomSuffixTrieLimitData) :
    d.profileWindow ≤ randomSuffixTrieLimitBudget d := by
  unfold randomSuffixTrieLimitBudget
  omega

def sampleRandomSuffixTrieLimitData : RandomSuffixTrieLimitData :=
  { suffixNodes := 7, profileWindow := 9, suffixSlack := 3 }

example : randomSuffixTrieLimitReady sampleRandomSuffixTrieLimitData := by
  norm_num [randomSuffixTrieLimitReady, hasSuffixNodes]
  norm_num [profileWindowControlled, sampleRandomSuffixTrieLimitData]

example : randomSuffixTrieLimitBudget sampleRandomSuffixTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for suffix-trie limit windows. -/
def randomSuffixTrieLimitListReady
    (windows : List RandomSuffixTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.suffixNodes && d.profileWindow ≤ d.suffixNodes + d.suffixSlack

theorem randomSuffixTrieLimitList_readyWindow :
    randomSuffixTrieLimitListReady
      [{ suffixNodes := 4, profileWindow := 5, suffixSlack := 1 },
       { suffixNodes := 7, profileWindow := 9, suffixSlack := 3 }] = true := by
  unfold randomSuffixTrieLimitListReady
  native_decide

structure RandomSuffixTrieLimitBudgetCertificate where
  suffixNodesWindow : ℕ
  profileWindow : ℕ
  suffixSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomSuffixTrieLimitBudgetCertificate.controlled
    (c : RandomSuffixTrieLimitBudgetCertificate) : Prop :=
  0 < c.suffixNodesWindow ∧
    c.profileWindow ≤ c.suffixNodesWindow + c.suffixSlackWindow + c.slack

def RandomSuffixTrieLimitBudgetCertificate.budgetControlled
    (c : RandomSuffixTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.suffixNodesWindow + c.profileWindow + c.suffixSlackWindow + c.slack

def RandomSuffixTrieLimitBudgetCertificate.Ready
    (c : RandomSuffixTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomSuffixTrieLimitBudgetCertificate.size
    (c : RandomSuffixTrieLimitBudgetCertificate) : ℕ :=
  c.suffixNodesWindow + c.profileWindow + c.suffixSlackWindow + c.slack

theorem randomSuffixTrieLimit_budgetCertificate_le_size
    (c : RandomSuffixTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomSuffixTrieLimitBudgetCertificate :
    RandomSuffixTrieLimitBudgetCertificate :=
  { suffixNodesWindow := 7
    profileWindow := 9
    suffixSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomSuffixTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.controlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomSuffixTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomSuffixTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.controlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]

example :
    sampleRandomSuffixTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSuffixTrieLimitBudgetCertificate.size := by
  apply randomSuffixTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.controlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]
  · norm_num [RandomSuffixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSuffixTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomSuffixTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomSuffixTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomSuffixTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomSuffixTrieLimitSchemas
