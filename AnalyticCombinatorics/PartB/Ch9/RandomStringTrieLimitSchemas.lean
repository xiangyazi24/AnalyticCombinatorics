import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random string trie limit schemas.

This module records finite bookkeeping for random string trie limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomStringTrieLimitSchemas

structure RandomStringTrieLimitData where
  stringCount : ℕ
  trieProfile : ℕ
  alphabetSlack : ℕ
deriving DecidableEq, Repr

def hasStringCount (d : RandomStringTrieLimitData) : Prop :=
  0 < d.stringCount

def trieProfileControlled (d : RandomStringTrieLimitData) : Prop :=
  d.trieProfile ≤ d.stringCount + d.alphabetSlack

def randomStringTrieLimitReady (d : RandomStringTrieLimitData) : Prop :=
  hasStringCount d ∧ trieProfileControlled d

def randomStringTrieLimitBudget (d : RandomStringTrieLimitData) : ℕ :=
  d.stringCount + d.trieProfile + d.alphabetSlack

theorem randomStringTrieLimitReady.hasStringCount
    {d : RandomStringTrieLimitData}
    (h : randomStringTrieLimitReady d) :
    hasStringCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem trieProfile_le_budget (d : RandomStringTrieLimitData) :
    d.trieProfile ≤ randomStringTrieLimitBudget d := by
  unfold randomStringTrieLimitBudget
  omega

def sampleRandomStringTrieLimitData : RandomStringTrieLimitData :=
  { stringCount := 7, trieProfile := 9, alphabetSlack := 3 }

example : randomStringTrieLimitReady sampleRandomStringTrieLimitData := by
  norm_num [randomStringTrieLimitReady, hasStringCount]
  norm_num [trieProfileControlled, sampleRandomStringTrieLimitData]

example : randomStringTrieLimitBudget sampleRandomStringTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for string-trie limit windows. -/
def randomStringTrieLimitListReady (windows : List RandomStringTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.stringCount && d.trieProfile ≤ d.stringCount + d.alphabetSlack

theorem randomStringTrieLimitList_readyWindow :
    randomStringTrieLimitListReady
      [{ stringCount := 4, trieProfile := 5, alphabetSlack := 1 },
       { stringCount := 7, trieProfile := 9, alphabetSlack := 3 }] = true := by
  unfold randomStringTrieLimitListReady
  native_decide

structure RandomStringTrieLimitBudgetCertificate where
  stringCountWindow : ℕ
  trieProfileWindow : ℕ
  alphabetSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomStringTrieLimitBudgetCertificate.controlled
    (c : RandomStringTrieLimitBudgetCertificate) : Prop :=
  0 < c.stringCountWindow ∧
    c.trieProfileWindow ≤ c.stringCountWindow + c.alphabetSlackWindow + c.slack

def RandomStringTrieLimitBudgetCertificate.budgetControlled
    (c : RandomStringTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stringCountWindow + c.trieProfileWindow + c.alphabetSlackWindow + c.slack

def RandomStringTrieLimitBudgetCertificate.Ready
    (c : RandomStringTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomStringTrieLimitBudgetCertificate.size
    (c : RandomStringTrieLimitBudgetCertificate) : ℕ :=
  c.stringCountWindow + c.trieProfileWindow + c.alphabetSlackWindow + c.slack

theorem randomStringTrieLimit_budgetCertificate_le_size
    (c : RandomStringTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomStringTrieLimitBudgetCertificate :
    RandomStringTrieLimitBudgetCertificate :=
  { stringCountWindow := 7
    trieProfileWindow := 9
    alphabetSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomStringTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomStringTrieLimitBudgetCertificate.controlled,
      sampleRandomStringTrieLimitBudgetCertificate]
  · norm_num [RandomStringTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomStringTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomStringTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomStringTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomStringTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomStringTrieLimitBudgetCertificate.controlled,
      sampleRandomStringTrieLimitBudgetCertificate]
  · norm_num [RandomStringTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomStringTrieLimitBudgetCertificate]

example :
    sampleRandomStringTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomStringTrieLimitBudgetCertificate.size := by
  apply randomStringTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomStringTrieLimitBudgetCertificate.controlled,
      sampleRandomStringTrieLimitBudgetCertificate]
  · norm_num [RandomStringTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomStringTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomStringTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomStringTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomStringTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomStringTrieLimitSchemas
