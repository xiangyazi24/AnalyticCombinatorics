import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random hash trie limit schemas.

This module records finite bookkeeping for random hash trie limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomHashTrieLimitSchemas

structure RandomHashTrieLimitData where
  hashBuckets : ℕ
  trieDepth : ℕ
  hashingSlack : ℕ
deriving DecidableEq, Repr

def hasHashBuckets (d : RandomHashTrieLimitData) : Prop :=
  0 < d.hashBuckets

def trieDepthControlled (d : RandomHashTrieLimitData) : Prop :=
  d.trieDepth ≤ d.hashBuckets + d.hashingSlack

def randomHashTrieLimitReady (d : RandomHashTrieLimitData) : Prop :=
  hasHashBuckets d ∧ trieDepthControlled d

def randomHashTrieLimitBudget (d : RandomHashTrieLimitData) : ℕ :=
  d.hashBuckets + d.trieDepth + d.hashingSlack

theorem randomHashTrieLimitReady.hasHashBuckets
    {d : RandomHashTrieLimitData}
    (h : randomHashTrieLimitReady d) :
    hasHashBuckets d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem trieDepth_le_budget (d : RandomHashTrieLimitData) :
    d.trieDepth ≤ randomHashTrieLimitBudget d := by
  unfold randomHashTrieLimitBudget
  omega

def sampleRandomHashTrieLimitData : RandomHashTrieLimitData :=
  { hashBuckets := 7, trieDepth := 9, hashingSlack := 3 }

example : randomHashTrieLimitReady sampleRandomHashTrieLimitData := by
  norm_num [randomHashTrieLimitReady, hasHashBuckets]
  norm_num [trieDepthControlled, sampleRandomHashTrieLimitData]

example : randomHashTrieLimitBudget sampleRandomHashTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for hash-trie limit windows. -/
def randomHashTrieLimitListReady (windows : List RandomHashTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.hashBuckets && d.trieDepth ≤ d.hashBuckets + d.hashingSlack

theorem randomHashTrieLimitList_readyWindow :
    randomHashTrieLimitListReady
      [{ hashBuckets := 4, trieDepth := 5, hashingSlack := 1 },
       { hashBuckets := 7, trieDepth := 9, hashingSlack := 3 }] = true := by
  unfold randomHashTrieLimitListReady
  native_decide

structure RandomHashTrieLimitBudgetCertificate where
  hashBucketsWindow : ℕ
  trieDepthWindow : ℕ
  hashingSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomHashTrieLimitBudgetCertificate.controlled
    (c : RandomHashTrieLimitBudgetCertificate) : Prop :=
  0 < c.hashBucketsWindow ∧
    c.trieDepthWindow ≤ c.hashBucketsWindow + c.hashingSlackWindow + c.slack

def RandomHashTrieLimitBudgetCertificate.budgetControlled
    (c : RandomHashTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.hashBucketsWindow + c.trieDepthWindow + c.hashingSlackWindow + c.slack

def RandomHashTrieLimitBudgetCertificate.Ready
    (c : RandomHashTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomHashTrieLimitBudgetCertificate.size
    (c : RandomHashTrieLimitBudgetCertificate) : ℕ :=
  c.hashBucketsWindow + c.trieDepthWindow + c.hashingSlackWindow + c.slack

theorem randomHashTrieLimit_budgetCertificate_le_size
    (c : RandomHashTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomHashTrieLimitBudgetCertificate :
    RandomHashTrieLimitBudgetCertificate :=
  { hashBucketsWindow := 7
    trieDepthWindow := 9
    hashingSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomHashTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomHashTrieLimitBudgetCertificate.controlled,
      sampleRandomHashTrieLimitBudgetCertificate]
  · norm_num [RandomHashTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomHashTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomHashTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomHashTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomHashTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomHashTrieLimitBudgetCertificate.controlled,
      sampleRandomHashTrieLimitBudgetCertificate]
  · norm_num [RandomHashTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomHashTrieLimitBudgetCertificate]

example :
    sampleRandomHashTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomHashTrieLimitBudgetCertificate.size := by
  apply randomHashTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomHashTrieLimitBudgetCertificate.controlled,
      sampleRandomHashTrieLimitBudgetCertificate]
  · norm_num [RandomHashTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomHashTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomHashTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomHashTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomHashTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomHashTrieLimitSchemas
