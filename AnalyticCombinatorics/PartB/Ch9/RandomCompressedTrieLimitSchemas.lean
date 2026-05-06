import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random compressed trie limit schemas.

This module records finite bookkeeping for compressed trie limits.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomCompressedTrieLimitSchemas

structure RandomCompressedTrieLimitData where
  compressedEdges : ℕ
  profileWindow : ℕ
  compressionSlack : ℕ
deriving DecidableEq, Repr

def hasCompressedEdges (d : RandomCompressedTrieLimitData) : Prop :=
  0 < d.compressedEdges

def profileWindowControlled (d : RandomCompressedTrieLimitData) : Prop :=
  d.profileWindow ≤ d.compressedEdges + d.compressionSlack

def randomCompressedTrieLimitReady
    (d : RandomCompressedTrieLimitData) : Prop :=
  hasCompressedEdges d ∧ profileWindowControlled d

def randomCompressedTrieLimitBudget
    (d : RandomCompressedTrieLimitData) : ℕ :=
  d.compressedEdges + d.profileWindow + d.compressionSlack

theorem randomCompressedTrieLimitReady.hasCompressedEdges
    {d : RandomCompressedTrieLimitData}
    (h : randomCompressedTrieLimitReady d) :
    hasCompressedEdges d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileWindow_le_budget (d : RandomCompressedTrieLimitData) :
    d.profileWindow ≤ randomCompressedTrieLimitBudget d := by
  unfold randomCompressedTrieLimitBudget
  omega

def sampleRandomCompressedTrieLimitData : RandomCompressedTrieLimitData :=
  { compressedEdges := 7, profileWindow := 9, compressionSlack := 3 }

example : randomCompressedTrieLimitReady
    sampleRandomCompressedTrieLimitData := by
  norm_num [randomCompressedTrieLimitReady, hasCompressedEdges]
  norm_num [profileWindowControlled, sampleRandomCompressedTrieLimitData]

example :
    randomCompressedTrieLimitBudget sampleRandomCompressedTrieLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for compressed-trie limit windows. -/
def randomCompressedTrieLimitListReady
    (windows : List RandomCompressedTrieLimitData) : Bool :=
  windows.all fun d =>
    0 < d.compressedEdges &&
      d.profileWindow ≤ d.compressedEdges + d.compressionSlack

theorem randomCompressedTrieLimitList_readyWindow :
    randomCompressedTrieLimitListReady
      [{ compressedEdges := 4, profileWindow := 5, compressionSlack := 1 },
       { compressedEdges := 7, profileWindow := 9, compressionSlack := 3 }] =
      true := by
  unfold randomCompressedTrieLimitListReady
  native_decide

structure RandomCompressedTrieLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomCompressedTrieLimitSchemasBudgetCertificate.controlled
    (c : RandomCompressedTrieLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomCompressedTrieLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomCompressedTrieLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomCompressedTrieLimitSchemasBudgetCertificate.Ready
    (c : RandomCompressedTrieLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomCompressedTrieLimitSchemasBudgetCertificate.size
    (c : RandomCompressedTrieLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomCompressedTrieLimitSchemas_budgetCertificate_le_size
    (c : RandomCompressedTrieLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomCompressedTrieLimitSchemasBudgetCertificate :
    RandomCompressedTrieLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomCompressedTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomCompressedTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomCompressedTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]

example :
    sampleRandomCompressedTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate.size := by
  apply randomCompressedTrieLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.controlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]
  · norm_num [RandomCompressedTrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomCompressedTrieLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomCompressedTrieLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomCompressedTrieLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomCompressedTrieLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomCompressedTrieLimitSchemas
