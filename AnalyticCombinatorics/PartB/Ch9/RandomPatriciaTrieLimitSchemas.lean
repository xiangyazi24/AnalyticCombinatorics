import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random Patricia trie limit schemas.

This module records finite bookkeeping for Patricia trie limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomPatriciaTrieLimitSchemas

structure RandomPatriciaTrieLimitData where
  compressedNodes : ℕ
  profileWindow : ℕ
  trieSlack : ℕ
deriving DecidableEq, Repr

def hasCompressedNodes (d : RandomPatriciaTrieLimitData) : Prop :=
  0 < d.compressedNodes

def profileWindowControlled (d : RandomPatriciaTrieLimitData) : Prop :=
  d.profileWindow ≤ d.compressedNodes + d.trieSlack

def randomPatriciaTrieLimitReady
    (d : RandomPatriciaTrieLimitData) : Prop :=
  hasCompressedNodes d ∧ profileWindowControlled d

def randomPatriciaTrieLimitBudget
    (d : RandomPatriciaTrieLimitData) : ℕ :=
  d.compressedNodes + d.profileWindow + d.trieSlack

theorem randomPatriciaTrieLimitReady.hasCompressedNodes
    {d : RandomPatriciaTrieLimitData}
    (h : randomPatriciaTrieLimitReady d) :
    hasCompressedNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWindow_le_budget (d : RandomPatriciaTrieLimitData) :
    d.profileWindow ≤ randomPatriciaTrieLimitBudget d := by
  unfold randomPatriciaTrieLimitBudget
  omega

def sampleRandomPatriciaTrieLimitData : RandomPatriciaTrieLimitData :=
  { compressedNodes := 7, profileWindow := 9, trieSlack := 3 }

example : randomPatriciaTrieLimitReady
    sampleRandomPatriciaTrieLimitData := by
  norm_num [randomPatriciaTrieLimitReady, hasCompressedNodes]
  norm_num [profileWindowControlled, sampleRandomPatriciaTrieLimitData]

example :
    randomPatriciaTrieLimitBudget sampleRandomPatriciaTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for Patricia trie limit windows. -/
def randomPatriciaTrieLimitListReady
    (windows : List RandomPatriciaTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.compressedNodes && d.profileWindow ≤ d.compressedNodes + d.trieSlack

theorem randomPatriciaTrieLimitList_readyWindow :
    randomPatriciaTrieLimitListReady
      [{ compressedNodes := 4, profileWindow := 5, trieSlack := 1 },
       { compressedNodes := 7, profileWindow := 9, trieSlack := 3 }] = true := by
  unfold randomPatriciaTrieLimitListReady
  native_decide

structure RandomPatriciaTrieLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPatriciaTrieLimitSchemasBudgetCertificate.controlled
    (c : RandomPatriciaTrieLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomPatriciaTrieLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomPatriciaTrieLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomPatriciaTrieLimitSchemasBudgetCertificate.Ready
    (c : RandomPatriciaTrieLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomPatriciaTrieLimitSchemasBudgetCertificate.size
    (c : RandomPatriciaTrieLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomPatriciaTrieLimitSchemas_budgetCertificate_le_size
    (c : RandomPatriciaTrieLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomPatriciaTrieLimitSchemasBudgetCertificate :
    RandomPatriciaTrieLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]

example :
    sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate.size := by
  apply randomPatriciaTrieLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomPatriciaTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomPatriciaTrieLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomPatriciaTrieLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomPatriciaTrieLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomPatriciaTrieLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomPatriciaTrieLimitSchemas
