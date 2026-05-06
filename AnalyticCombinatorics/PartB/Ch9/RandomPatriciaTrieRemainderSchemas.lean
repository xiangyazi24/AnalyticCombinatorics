import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random Patricia trie remainder schemas.

This module records finite bookkeeping for Patricia trie remainders.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomPatriciaTrieRemainderSchemas

structure RandomPatriciaTrieRemainderData where
  patriciaNodes : ℕ
  remainderWindow : ℕ
  trieSlack : ℕ
deriving DecidableEq, Repr

def hasPatriciaNodes (d : RandomPatriciaTrieRemainderData) : Prop :=
  0 < d.patriciaNodes

def remainderWindowControlled
    (d : RandomPatriciaTrieRemainderData) : Prop :=
  d.remainderWindow ≤ d.patriciaNodes + d.trieSlack

def randomPatriciaTrieRemainderReady
    (d : RandomPatriciaTrieRemainderData) : Prop :=
  hasPatriciaNodes d ∧ remainderWindowControlled d

def randomPatriciaTrieRemainderBudget
    (d : RandomPatriciaTrieRemainderData) : ℕ :=
  d.patriciaNodes + d.remainderWindow + d.trieSlack

theorem randomPatriciaTrieRemainderReady.hasPatriciaNodes
    {d : RandomPatriciaTrieRemainderData}
    (h : randomPatriciaTrieRemainderReady d) :
    hasPatriciaNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem remainderWindow_le_budget
    (d : RandomPatriciaTrieRemainderData) :
    d.remainderWindow ≤ randomPatriciaTrieRemainderBudget d := by
  unfold randomPatriciaTrieRemainderBudget
  omega

def sampleRandomPatriciaTrieRemainderData :
    RandomPatriciaTrieRemainderData :=
  { patriciaNodes := 7, remainderWindow := 9, trieSlack := 3 }

example : randomPatriciaTrieRemainderReady
    sampleRandomPatriciaTrieRemainderData := by
  norm_num [randomPatriciaTrieRemainderReady, hasPatriciaNodes]
  norm_num [remainderWindowControlled, sampleRandomPatriciaTrieRemainderData]

example :
    randomPatriciaTrieRemainderBudget sampleRandomPatriciaTrieRemainderData = 19 := by
  native_decide

/-- Finite executable readiness audit for Patricia trie remainder windows. -/
def randomPatriciaTrieRemainderListReady
    (windows : List RandomPatriciaTrieRemainderData) : Bool :=
  windows.all fun d =>
    0 < d.patriciaNodes && d.remainderWindow ≤ d.patriciaNodes + d.trieSlack

theorem randomPatriciaTrieRemainderList_readyWindow :
    randomPatriciaTrieRemainderListReady
      [{ patriciaNodes := 4, remainderWindow := 5, trieSlack := 1 },
       { patriciaNodes := 7, remainderWindow := 9, trieSlack := 3 }] = true := by
  unfold randomPatriciaTrieRemainderListReady
  native_decide

structure RandomPatriciaTrieRemainderSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPatriciaTrieRemainderSchemasBudgetCertificate.controlled
    (c : RandomPatriciaTrieRemainderSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomPatriciaTrieRemainderSchemasBudgetCertificate.budgetControlled
    (c : RandomPatriciaTrieRemainderSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomPatriciaTrieRemainderSchemasBudgetCertificate.Ready
    (c : RandomPatriciaTrieRemainderSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomPatriciaTrieRemainderSchemasBudgetCertificate.size
    (c : RandomPatriciaTrieRemainderSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomPatriciaTrieRemainderSchemas_budgetCertificate_le_size
    (c : RandomPatriciaTrieRemainderSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate :
    RandomPatriciaTrieRemainderSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]

example :
    sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate.size := by
  apply randomPatriciaTrieRemainderSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieRemainderSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomPatriciaTrieRemainderSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomPatriciaTrieRemainderSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomPatriciaTrieRemainderSchemas
