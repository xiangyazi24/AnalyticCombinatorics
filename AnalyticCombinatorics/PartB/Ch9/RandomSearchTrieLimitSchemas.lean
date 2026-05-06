import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random search trie limit schemas.

This module records finite bookkeeping for search trie limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomSearchTrieLimitSchemas

structure RandomSearchTrieLimitData where
  searchNodes : ℕ
  trieWindow : ℕ
  searchSlack : ℕ
deriving DecidableEq, Repr

def hasSearchNodes (d : RandomSearchTrieLimitData) : Prop :=
  0 < d.searchNodes

def trieWindowControlled (d : RandomSearchTrieLimitData) : Prop :=
  d.trieWindow ≤ d.searchNodes + d.searchSlack

def randomSearchTrieLimitReady (d : RandomSearchTrieLimitData) : Prop :=
  hasSearchNodes d ∧ trieWindowControlled d

def randomSearchTrieLimitBudget (d : RandomSearchTrieLimitData) : ℕ :=
  d.searchNodes + d.trieWindow + d.searchSlack

theorem randomSearchTrieLimitReady.hasSearchNodes
    {d : RandomSearchTrieLimitData}
    (h : randomSearchTrieLimitReady d) :
    hasSearchNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem trieWindow_le_budget (d : RandomSearchTrieLimitData) :
    d.trieWindow ≤ randomSearchTrieLimitBudget d := by
  unfold randomSearchTrieLimitBudget
  omega

def sampleRandomSearchTrieLimitData : RandomSearchTrieLimitData :=
  { searchNodes := 7, trieWindow := 9, searchSlack := 3 }

example : randomSearchTrieLimitReady sampleRandomSearchTrieLimitData := by
  norm_num [randomSearchTrieLimitReady, hasSearchNodes]
  norm_num [trieWindowControlled, sampleRandomSearchTrieLimitData]

example : randomSearchTrieLimitBudget sampleRandomSearchTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for search-trie limit windows. -/
def randomSearchTrieLimitListReady (windows : List RandomSearchTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.searchNodes && d.trieWindow ≤ d.searchNodes + d.searchSlack

theorem randomSearchTrieLimitList_readyWindow :
    randomSearchTrieLimitListReady
      [{ searchNodes := 4, trieWindow := 5, searchSlack := 1 },
       { searchNodes := 7, trieWindow := 9, searchSlack := 3 }] = true := by
  unfold randomSearchTrieLimitListReady
  native_decide

structure RandomSearchTrieLimitBudgetCertificate where
  searchNodesWindow : ℕ
  trieWindow : ℕ
  searchSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomSearchTrieLimitBudgetCertificate.controlled
    (c : RandomSearchTrieLimitBudgetCertificate) : Prop :=
  0 < c.searchNodesWindow ∧
    c.trieWindow ≤ c.searchNodesWindow + c.searchSlackWindow + c.slack

def RandomSearchTrieLimitBudgetCertificate.budgetControlled
    (c : RandomSearchTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.searchNodesWindow + c.trieWindow + c.searchSlackWindow + c.slack

def RandomSearchTrieLimitBudgetCertificate.Ready
    (c : RandomSearchTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomSearchTrieLimitBudgetCertificate.size
    (c : RandomSearchTrieLimitBudgetCertificate) : ℕ :=
  c.searchNodesWindow + c.trieWindow + c.searchSlackWindow + c.slack

theorem randomSearchTrieLimit_budgetCertificate_le_size
    (c : RandomSearchTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomSearchTrieLimitBudgetCertificate :
    RandomSearchTrieLimitBudgetCertificate :=
  { searchNodesWindow := 7
    trieWindow := 9
    searchSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomSearchTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSearchTrieLimitBudgetCertificate.controlled,
      sampleRandomSearchTrieLimitBudgetCertificate]
  · norm_num [RandomSearchTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSearchTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomSearchTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSearchTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomSearchTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomSearchTrieLimitBudgetCertificate.controlled,
      sampleRandomSearchTrieLimitBudgetCertificate]
  · norm_num [RandomSearchTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSearchTrieLimitBudgetCertificate]

example :
    sampleRandomSearchTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomSearchTrieLimitBudgetCertificate.size := by
  apply randomSearchTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomSearchTrieLimitBudgetCertificate.controlled,
      sampleRandomSearchTrieLimitBudgetCertificate]
  · norm_num [RandomSearchTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomSearchTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomSearchTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomSearchTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomSearchTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomSearchTrieLimitSchemas
