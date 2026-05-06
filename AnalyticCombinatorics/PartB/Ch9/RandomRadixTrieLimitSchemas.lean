import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random radix trie limit schemas.

This module records finite bookkeeping for radix trie limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomRadixTrieLimitSchemas

structure RandomRadixTrieLimitData where
  radixNodes : ℕ
  trieWindow : ℕ
  radixSlack : ℕ
deriving DecidableEq, Repr

def hasRadixNodes (d : RandomRadixTrieLimitData) : Prop :=
  0 < d.radixNodes

def trieWindowControlled (d : RandomRadixTrieLimitData) : Prop :=
  d.trieWindow ≤ d.radixNodes + d.radixSlack

def randomRadixTrieLimitReady (d : RandomRadixTrieLimitData) : Prop :=
  hasRadixNodes d ∧ trieWindowControlled d

def randomRadixTrieLimitBudget (d : RandomRadixTrieLimitData) : ℕ :=
  d.radixNodes + d.trieWindow + d.radixSlack

theorem randomRadixTrieLimitReady.hasRadixNodes
    {d : RandomRadixTrieLimitData}
    (h : randomRadixTrieLimitReady d) :
    hasRadixNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem trieWindow_le_budget (d : RandomRadixTrieLimitData) :
    d.trieWindow ≤ randomRadixTrieLimitBudget d := by
  unfold randomRadixTrieLimitBudget
  omega

def sampleRandomRadixTrieLimitData : RandomRadixTrieLimitData :=
  { radixNodes := 7, trieWindow := 9, radixSlack := 3 }

example : randomRadixTrieLimitReady sampleRandomRadixTrieLimitData := by
  norm_num [randomRadixTrieLimitReady, hasRadixNodes]
  norm_num [trieWindowControlled, sampleRandomRadixTrieLimitData]

example : randomRadixTrieLimitBudget sampleRandomRadixTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for radix-trie limit windows. -/
def randomRadixTrieLimitListReady (windows : List RandomRadixTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.radixNodes && d.trieWindow ≤ d.radixNodes + d.radixSlack

theorem randomRadixTrieLimitList_readyWindow :
    randomRadixTrieLimitListReady
      [{ radixNodes := 4, trieWindow := 5, radixSlack := 1 },
       { radixNodes := 7, trieWindow := 9, radixSlack := 3 }] = true := by
  unfold randomRadixTrieLimitListReady
  native_decide

structure RandomRadixTrieLimitBudgetCertificate where
  radixNodesWindow : ℕ
  trieWindow : ℕ
  radixSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomRadixTrieLimitBudgetCertificate.controlled
    (c : RandomRadixTrieLimitBudgetCertificate) : Prop :=
  0 < c.radixNodesWindow ∧
    c.trieWindow ≤ c.radixNodesWindow + c.radixSlackWindow + c.slack

def RandomRadixTrieLimitBudgetCertificate.budgetControlled
    (c : RandomRadixTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.radixNodesWindow + c.trieWindow + c.radixSlackWindow + c.slack

def RandomRadixTrieLimitBudgetCertificate.Ready
    (c : RandomRadixTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomRadixTrieLimitBudgetCertificate.size
    (c : RandomRadixTrieLimitBudgetCertificate) : ℕ :=
  c.radixNodesWindow + c.trieWindow + c.radixSlackWindow + c.slack

theorem randomRadixTrieLimit_budgetCertificate_le_size
    (c : RandomRadixTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomRadixTrieLimitBudgetCertificate :
    RandomRadixTrieLimitBudgetCertificate :=
  { radixNodesWindow := 7
    trieWindow := 9
    radixSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomRadixTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomRadixTrieLimitBudgetCertificate.controlled,
      sampleRandomRadixTrieLimitBudgetCertificate]
  · norm_num [RandomRadixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomRadixTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomRadixTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomRadixTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomRadixTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomRadixTrieLimitBudgetCertificate.controlled,
      sampleRandomRadixTrieLimitBudgetCertificate]
  · norm_num [RandomRadixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomRadixTrieLimitBudgetCertificate]

example :
    sampleRandomRadixTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomRadixTrieLimitBudgetCertificate.size := by
  apply randomRadixTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomRadixTrieLimitBudgetCertificate.controlled,
      sampleRandomRadixTrieLimitBudgetCertificate]
  · norm_num [RandomRadixTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomRadixTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomRadixTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomRadixTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomRadixTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomRadixTrieLimitSchemas
