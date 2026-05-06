import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random trie profile schemas.

This module records finite bookkeeping for random trie profiles: a positive
node budget controls profile width with depth slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomTrieProfileSchemas

structure RandomTrieProfileData where
  nodeBudget : ℕ
  profileWidth : ℕ
  depthSlack : ℕ
deriving DecidableEq, Repr

def hasNodeBudget (d : RandomTrieProfileData) : Prop :=
  0 < d.nodeBudget

def profileWidthControlled (d : RandomTrieProfileData) : Prop :=
  d.profileWidth ≤ d.nodeBudget + d.depthSlack

def randomTrieProfileReady (d : RandomTrieProfileData) : Prop :=
  hasNodeBudget d ∧ profileWidthControlled d

def randomTrieProfileBudget (d : RandomTrieProfileData) : ℕ :=
  d.nodeBudget + d.profileWidth + d.depthSlack

theorem randomTrieProfileReady.hasNodeBudget {d : RandomTrieProfileData}
    (h : randomTrieProfileReady d) :
    hasNodeBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWidth_le_budget (d : RandomTrieProfileData) :
    d.profileWidth ≤ randomTrieProfileBudget d := by
  unfold randomTrieProfileBudget
  omega

def sampleRandomTrieProfileData : RandomTrieProfileData :=
  { nodeBudget := 7, profileWidth := 9, depthSlack := 3 }

example : randomTrieProfileReady sampleRandomTrieProfileData := by
  norm_num [randomTrieProfileReady, hasNodeBudget]
  norm_num [profileWidthControlled, sampleRandomTrieProfileData]

example : randomTrieProfileBudget sampleRandomTrieProfileData = 19 := by
  native_decide

/-- Finite executable readiness audit for trie-profile windows. -/
def randomTrieProfileListReady (windows : List RandomTrieProfileData) : Bool :=
  windows.all fun d =>
    0 < d.nodeBudget && d.profileWidth ≤ d.nodeBudget + d.depthSlack

theorem randomTrieProfileList_readyWindow :
    randomTrieProfileListReady
      [{ nodeBudget := 4, profileWidth := 5, depthSlack := 1 },
       { nodeBudget := 7, profileWidth := 9, depthSlack := 3 }] = true := by
  unfold randomTrieProfileListReady
  native_decide

structure RandomTrieProfileBudgetCertificate where
  nodeBudgetWindow : ℕ
  profileWidthWindow : ℕ
  depthSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomTrieProfileBudgetCertificate.controlled
    (c : RandomTrieProfileBudgetCertificate) : Prop :=
  0 < c.nodeBudgetWindow ∧
    c.profileWidthWindow ≤ c.nodeBudgetWindow + c.depthSlackWindow + c.slack

def RandomTrieProfileBudgetCertificate.budgetControlled
    (c : RandomTrieProfileBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.nodeBudgetWindow + c.profileWidthWindow + c.depthSlackWindow + c.slack

def RandomTrieProfileBudgetCertificate.Ready
    (c : RandomTrieProfileBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomTrieProfileBudgetCertificate.size
    (c : RandomTrieProfileBudgetCertificate) : ℕ :=
  c.nodeBudgetWindow + c.profileWidthWindow + c.depthSlackWindow + c.slack

theorem randomTrieProfile_budgetCertificate_le_size
    (c : RandomTrieProfileBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomTrieProfileBudgetCertificate :
    RandomTrieProfileBudgetCertificate :=
  { nodeBudgetWindow := 7
    profileWidthWindow := 9
    depthSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomTrieProfileBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTrieProfileBudgetCertificate.controlled,
      sampleRandomTrieProfileBudgetCertificate]
  · norm_num [RandomTrieProfileBudgetCertificate.budgetControlled,
      sampleRandomTrieProfileBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomTrieProfileBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTrieProfileBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomTrieProfileBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTrieProfileBudgetCertificate.controlled,
      sampleRandomTrieProfileBudgetCertificate]
  · norm_num [RandomTrieProfileBudgetCertificate.budgetControlled,
      sampleRandomTrieProfileBudgetCertificate]

example :
    sampleRandomTrieProfileBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTrieProfileBudgetCertificate.size := by
  apply randomTrieProfile_budgetCertificate_le_size
  constructor
  · norm_num [RandomTrieProfileBudgetCertificate.controlled,
      sampleRandomTrieProfileBudgetCertificate]
  · norm_num [RandomTrieProfileBudgetCertificate.budgetControlled,
      sampleRandomTrieProfileBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomTrieProfileBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomTrieProfileBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomTrieProfileBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomTrieProfileSchemas
