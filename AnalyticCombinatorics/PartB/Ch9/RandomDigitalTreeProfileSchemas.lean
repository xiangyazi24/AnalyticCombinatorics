import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random digital tree profile schemas.

This module records finite bookkeeping for random digital tree profiles.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomDigitalTreeProfileSchemas

structure RandomDigitalTreeProfileData where
  digitalNodes : ℕ
  profileDepth : ℕ
  branchingSlack : ℕ
deriving DecidableEq, Repr

def hasDigitalNodes (d : RandomDigitalTreeProfileData) : Prop :=
  0 < d.digitalNodes

def profileDepthControlled (d : RandomDigitalTreeProfileData) : Prop :=
  d.profileDepth ≤ d.digitalNodes + d.branchingSlack

def randomDigitalTreeProfileReady
    (d : RandomDigitalTreeProfileData) : Prop :=
  hasDigitalNodes d ∧ profileDepthControlled d

def randomDigitalTreeProfileBudget
    (d : RandomDigitalTreeProfileData) : ℕ :=
  d.digitalNodes + d.profileDepth + d.branchingSlack

theorem randomDigitalTreeProfileReady.hasDigitalNodes
    {d : RandomDigitalTreeProfileData}
    (h : randomDigitalTreeProfileReady d) :
    hasDigitalNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem profileDepth_le_budget (d : RandomDigitalTreeProfileData) :
    d.profileDepth ≤ randomDigitalTreeProfileBudget d := by
  unfold randomDigitalTreeProfileBudget
  omega

def sampleRandomDigitalTreeProfileData : RandomDigitalTreeProfileData :=
  { digitalNodes := 7, profileDepth := 9, branchingSlack := 3 }

example : randomDigitalTreeProfileReady
    sampleRandomDigitalTreeProfileData := by
  norm_num [randomDigitalTreeProfileReady, hasDigitalNodes]
  norm_num [profileDepthControlled, sampleRandomDigitalTreeProfileData]

example :
    randomDigitalTreeProfileBudget sampleRandomDigitalTreeProfileData = 19 := by
  native_decide

/-- Finite executable readiness audit for digital-tree profile windows. -/
def randomDigitalTreeProfileListReady
    (windows : List RandomDigitalTreeProfileData) : Bool :=
  windows.all fun d =>
    0 < d.digitalNodes && d.profileDepth ≤ d.digitalNodes + d.branchingSlack

theorem randomDigitalTreeProfileList_readyWindow :
    randomDigitalTreeProfileListReady
      [{ digitalNodes := 4, profileDepth := 5, branchingSlack := 1 },
       { digitalNodes := 7, profileDepth := 9, branchingSlack := 3 }] = true := by
  unfold randomDigitalTreeProfileListReady
  native_decide

structure RandomDigitalTreeProfileSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomDigitalTreeProfileSchemasBudgetCertificate.controlled
    (c : RandomDigitalTreeProfileSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomDigitalTreeProfileSchemasBudgetCertificate.budgetControlled
    (c : RandomDigitalTreeProfileSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomDigitalTreeProfileSchemasBudgetCertificate.Ready
    (c : RandomDigitalTreeProfileSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomDigitalTreeProfileSchemasBudgetCertificate.size
    (c : RandomDigitalTreeProfileSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomDigitalTreeProfileSchemas_budgetCertificate_le_size
    (c : RandomDigitalTreeProfileSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomDigitalTreeProfileSchemasBudgetCertificate :
    RandomDigitalTreeProfileSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomDigitalTreeProfileSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.controlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.budgetControlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomDigitalTreeProfileSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomDigitalTreeProfileSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.controlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.budgetControlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]

example :
    sampleRandomDigitalTreeProfileSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate.size := by
  apply randomDigitalTreeProfileSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.controlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]
  · norm_num [RandomDigitalTreeProfileSchemasBudgetCertificate.budgetControlled,
      sampleRandomDigitalTreeProfileSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomDigitalTreeProfileSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomDigitalTreeProfileSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomDigitalTreeProfileSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomDigitalTreeProfileSchemas
