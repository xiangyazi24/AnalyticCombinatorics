import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random ternary search trie schemas.

This module records finite bookkeeping for ternary search trie limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomTernarySearchTrieSchemas

structure RandomTernarySearchTrieData where
  ternaryNodes : ℕ
  profileWindow : ℕ
  trieSlack : ℕ
deriving DecidableEq, Repr

def hasTernaryNodes (d : RandomTernarySearchTrieData) : Prop :=
  0 < d.ternaryNodes

def profileWindowControlled (d : RandomTernarySearchTrieData) : Prop :=
  d.profileWindow ≤ d.ternaryNodes + d.trieSlack

def randomTernarySearchTrieReady
    (d : RandomTernarySearchTrieData) : Prop :=
  hasTernaryNodes d ∧ profileWindowControlled d

def randomTernarySearchTrieBudget
    (d : RandomTernarySearchTrieData) : ℕ :=
  d.ternaryNodes + d.profileWindow + d.trieSlack

theorem randomTernarySearchTrieReady.hasTernaryNodes
    {d : RandomTernarySearchTrieData}
    (h : randomTernarySearchTrieReady d) :
    hasTernaryNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWindow_le_budget (d : RandomTernarySearchTrieData) :
    d.profileWindow ≤ randomTernarySearchTrieBudget d := by
  unfold randomTernarySearchTrieBudget
  omega

def sampleRandomTernarySearchTrieData : RandomTernarySearchTrieData :=
  { ternaryNodes := 7, profileWindow := 9, trieSlack := 3 }

example : randomTernarySearchTrieReady sampleRandomTernarySearchTrieData := by
  norm_num [randomTernarySearchTrieReady, hasTernaryNodes]
  norm_num [profileWindowControlled, sampleRandomTernarySearchTrieData]

example :
    randomTernarySearchTrieBudget sampleRandomTernarySearchTrieData = 19 := by
  native_decide

/-- Finite executable readiness audit for ternary search trie windows. -/
def randomTernarySearchTrieListReady
    (windows : List RandomTernarySearchTrieData) : Bool :=
  windows.all fun d =>
    0 < d.ternaryNodes && d.profileWindow ≤ d.ternaryNodes + d.trieSlack

theorem randomTernarySearchTrieList_readyWindow :
    randomTernarySearchTrieListReady
      [{ ternaryNodes := 4, profileWindow := 5, trieSlack := 1 },
       { ternaryNodes := 7, profileWindow := 9, trieSlack := 3 }] = true := by
  unfold randomTernarySearchTrieListReady
  native_decide

structure RandomTernarySearchTrieSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomTernarySearchTrieSchemasBudgetCertificate.controlled
    (c : RandomTernarySearchTrieSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomTernarySearchTrieSchemasBudgetCertificate.budgetControlled
    (c : RandomTernarySearchTrieSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomTernarySearchTrieSchemasBudgetCertificate.Ready
    (c : RandomTernarySearchTrieSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomTernarySearchTrieSchemasBudgetCertificate.size
    (c : RandomTernarySearchTrieSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomTernarySearchTrieSchemas_budgetCertificate_le_size
    (c : RandomTernarySearchTrieSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomTernarySearchTrieSchemasBudgetCertificate :
    RandomTernarySearchTrieSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomTernarySearchTrieSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.controlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.budgetControlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomTernarySearchTrieSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTernarySearchTrieSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomTernarySearchTrieSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.controlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.budgetControlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]

example :
    sampleRandomTernarySearchTrieSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTernarySearchTrieSchemasBudgetCertificate.size := by
  apply randomTernarySearchTrieSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.controlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]
  · norm_num [RandomTernarySearchTrieSchemasBudgetCertificate.budgetControlled,
      sampleRandomTernarySearchTrieSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomTernarySearchTrieSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomTernarySearchTrieSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomTernarySearchTrieSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomTernarySearchTrieSchemas
