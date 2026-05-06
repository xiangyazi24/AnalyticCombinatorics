import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random bucket trie limit schemas.

This module records finite bookkeeping for bucket trie limit windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomBucketTrieLimitSchemas

structure RandomBucketTrieLimitData where
  bucketCount : ℕ
  trieWindow : ℕ
  bucketSlack : ℕ
deriving DecidableEq, Repr

def hasBucketCount (d : RandomBucketTrieLimitData) : Prop :=
  0 < d.bucketCount

def trieWindowControlled (d : RandomBucketTrieLimitData) : Prop :=
  d.trieWindow ≤ d.bucketCount + d.bucketSlack

def randomBucketTrieLimitReady (d : RandomBucketTrieLimitData) : Prop :=
  hasBucketCount d ∧ trieWindowControlled d

def randomBucketTrieLimitBudget (d : RandomBucketTrieLimitData) : ℕ :=
  d.bucketCount + d.trieWindow + d.bucketSlack

theorem randomBucketTrieLimitReady.hasBucketCount
    {d : RandomBucketTrieLimitData}
    (h : randomBucketTrieLimitReady d) :
    hasBucketCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem trieWindow_le_budget (d : RandomBucketTrieLimitData) :
    d.trieWindow ≤ randomBucketTrieLimitBudget d := by
  unfold randomBucketTrieLimitBudget
  omega

def sampleRandomBucketTrieLimitData : RandomBucketTrieLimitData :=
  { bucketCount := 7, trieWindow := 9, bucketSlack := 3 }

example : randomBucketTrieLimitReady sampleRandomBucketTrieLimitData := by
  norm_num [randomBucketTrieLimitReady, hasBucketCount]
  norm_num [trieWindowControlled, sampleRandomBucketTrieLimitData]

example : randomBucketTrieLimitBudget sampleRandomBucketTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for bucket-trie limit windows. -/
def randomBucketTrieLimitListReady (windows : List RandomBucketTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.bucketCount && d.trieWindow ≤ d.bucketCount + d.bucketSlack

theorem randomBucketTrieLimitList_readyWindow :
    randomBucketTrieLimitListReady
      [{ bucketCount := 4, trieWindow := 5, bucketSlack := 1 },
       { bucketCount := 7, trieWindow := 9, bucketSlack := 3 }] = true := by
  unfold randomBucketTrieLimitListReady
  native_decide

structure RandomBucketTrieLimitBudgetCertificate where
  bucketCountWindow : ℕ
  trieWindow : ℕ
  bucketSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomBucketTrieLimitBudgetCertificate.controlled
    (c : RandomBucketTrieLimitBudgetCertificate) : Prop :=
  0 < c.bucketCountWindow ∧
    c.trieWindow ≤ c.bucketCountWindow + c.bucketSlackWindow + c.slack

def RandomBucketTrieLimitBudgetCertificate.budgetControlled
    (c : RandomBucketTrieLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.bucketCountWindow + c.trieWindow + c.bucketSlackWindow + c.slack

def RandomBucketTrieLimitBudgetCertificate.Ready
    (c : RandomBucketTrieLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomBucketTrieLimitBudgetCertificate.size
    (c : RandomBucketTrieLimitBudgetCertificate) : ℕ :=
  c.bucketCountWindow + c.trieWindow + c.bucketSlackWindow + c.slack

theorem randomBucketTrieLimit_budgetCertificate_le_size
    (c : RandomBucketTrieLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomBucketTrieLimitBudgetCertificate :
    RandomBucketTrieLimitBudgetCertificate :=
  { bucketCountWindow := 7
    trieWindow := 9
    bucketSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomBucketTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomBucketTrieLimitBudgetCertificate.controlled,
      sampleRandomBucketTrieLimitBudgetCertificate]
  · norm_num [RandomBucketTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomBucketTrieLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomBucketTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomBucketTrieLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomBucketTrieLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomBucketTrieLimitBudgetCertificate.controlled,
      sampleRandomBucketTrieLimitBudgetCertificate]
  · norm_num [RandomBucketTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomBucketTrieLimitBudgetCertificate]

example :
    sampleRandomBucketTrieLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomBucketTrieLimitBudgetCertificate.size := by
  apply randomBucketTrieLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomBucketTrieLimitBudgetCertificate.controlled,
      sampleRandomBucketTrieLimitBudgetCertificate]
  · norm_num [RandomBucketTrieLimitBudgetCertificate.budgetControlled,
      sampleRandomBucketTrieLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomBucketTrieLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomBucketTrieLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomBucketTrieLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomBucketTrieLimitSchemas
