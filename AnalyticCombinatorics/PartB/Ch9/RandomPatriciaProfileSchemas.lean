import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random Patricia profile schemas.

This module records finite bookkeeping for Patricia trie profile windows.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomPatriciaProfileSchemas

structure RandomPatriciaProfileData where
  patriciaNodes : ℕ
  profileWindow : ℕ
  compressionSlack : ℕ
deriving DecidableEq, Repr

def hasPatriciaNodes (d : RandomPatriciaProfileData) : Prop :=
  0 < d.patriciaNodes

def profileWindowControlled (d : RandomPatriciaProfileData) : Prop :=
  d.profileWindow ≤ d.patriciaNodes + d.compressionSlack

def randomPatriciaProfileReady (d : RandomPatriciaProfileData) : Prop :=
  hasPatriciaNodes d ∧ profileWindowControlled d

def randomPatriciaProfileBudget (d : RandomPatriciaProfileData) : ℕ :=
  d.patriciaNodes + d.profileWindow + d.compressionSlack

theorem randomPatriciaProfileReady.hasPatriciaNodes
    {d : RandomPatriciaProfileData}
    (h : randomPatriciaProfileReady d) :
    hasPatriciaNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWindow_le_budget (d : RandomPatriciaProfileData) :
    d.profileWindow ≤ randomPatriciaProfileBudget d := by
  unfold randomPatriciaProfileBudget
  omega

def sampleRandomPatriciaProfileData : RandomPatriciaProfileData :=
  { patriciaNodes := 7, profileWindow := 9, compressionSlack := 3 }

example : randomPatriciaProfileReady sampleRandomPatriciaProfileData := by
  norm_num [randomPatriciaProfileReady, hasPatriciaNodes]
  norm_num [profileWindowControlled, sampleRandomPatriciaProfileData]

example : randomPatriciaProfileBudget sampleRandomPatriciaProfileData = 19 := by
  native_decide

/-- Finite executable readiness audit for Patricia-profile windows. -/
def randomPatriciaProfileListReady (windows : List RandomPatriciaProfileData) : Bool :=
  windows.all fun d =>
    0 < d.patriciaNodes && d.profileWindow ≤ d.patriciaNodes + d.compressionSlack

theorem randomPatriciaProfileList_readyWindow :
    randomPatriciaProfileListReady
      [{ patriciaNodes := 4, profileWindow := 5, compressionSlack := 1 },
       { patriciaNodes := 7, profileWindow := 9, compressionSlack := 3 }] = true := by
  unfold randomPatriciaProfileListReady
  native_decide

structure RandomPatriciaProfileBudgetCertificate where
  patriciaNodesWindow : ℕ
  profileWindow : ℕ
  compressionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomPatriciaProfileBudgetCertificate.controlled
    (c : RandomPatriciaProfileBudgetCertificate) : Prop :=
  0 < c.patriciaNodesWindow ∧
    c.profileWindow ≤ c.patriciaNodesWindow + c.compressionSlackWindow + c.slack

def RandomPatriciaProfileBudgetCertificate.budgetControlled
    (c : RandomPatriciaProfileBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.patriciaNodesWindow + c.profileWindow + c.compressionSlackWindow + c.slack

def RandomPatriciaProfileBudgetCertificate.Ready
    (c : RandomPatriciaProfileBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomPatriciaProfileBudgetCertificate.size
    (c : RandomPatriciaProfileBudgetCertificate) : ℕ :=
  c.patriciaNodesWindow + c.profileWindow + c.compressionSlackWindow + c.slack

theorem randomPatriciaProfile_budgetCertificate_le_size
    (c : RandomPatriciaProfileBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomPatriciaProfileBudgetCertificate :
    RandomPatriciaProfileBudgetCertificate :=
  { patriciaNodesWindow := 7
    profileWindow := 9
    compressionSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomPatriciaProfileBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaProfileBudgetCertificate.controlled,
      sampleRandomPatriciaProfileBudgetCertificate]
  · norm_num [RandomPatriciaProfileBudgetCertificate.budgetControlled,
      sampleRandomPatriciaProfileBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomPatriciaProfileBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaProfileBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomPatriciaProfileBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomPatriciaProfileBudgetCertificate.controlled,
      sampleRandomPatriciaProfileBudgetCertificate]
  · norm_num [RandomPatriciaProfileBudgetCertificate.budgetControlled,
      sampleRandomPatriciaProfileBudgetCertificate]

example :
    sampleRandomPatriciaProfileBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomPatriciaProfileBudgetCertificate.size := by
  apply randomPatriciaProfile_budgetCertificate_le_size
  constructor
  · norm_num [RandomPatriciaProfileBudgetCertificate.controlled,
      sampleRandomPatriciaProfileBudgetCertificate]
  · norm_num [RandomPatriciaProfileBudgetCertificate.budgetControlled,
      sampleRandomPatriciaProfileBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomPatriciaProfileBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomPatriciaProfileBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomPatriciaProfileBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomPatriciaProfileSchemas
