import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform normal family models.

This module records finite bookkeeping for normal-family windows: a positive
compact cover controls a family bound with uniform slack.
-/

namespace AnalyticCombinatorics.AppB.UniformNormalFamilyModels

structure NormalFamilyData where
  compactCover : ℕ
  familyBound : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasCompactCover (d : NormalFamilyData) : Prop :=
  0 < d.compactCover

def familyBoundControlled (d : NormalFamilyData) : Prop :=
  d.familyBound ≤ d.compactCover + d.uniformSlack

def normalFamilyReady (d : NormalFamilyData) : Prop :=
  hasCompactCover d ∧ familyBoundControlled d

def normalFamilyBudget (d : NormalFamilyData) : ℕ :=
  d.compactCover + d.familyBound + d.uniformSlack

theorem normalFamilyReady.hasCompactCover {d : NormalFamilyData}
    (h : normalFamilyReady d) :
    hasCompactCover d ∧ familyBoundControlled d ∧
      d.familyBound ≤ normalFamilyBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold normalFamilyBudget
  omega

theorem familyBound_le_budget (d : NormalFamilyData) :
    d.familyBound ≤ normalFamilyBudget d := by
  unfold normalFamilyBudget
  omega

def sampleNormalFamilyData : NormalFamilyData :=
  { compactCover := 6, familyBound := 8, uniformSlack := 3 }

example : normalFamilyReady sampleNormalFamilyData := by
  norm_num [normalFamilyReady, hasCompactCover]
  norm_num [familyBoundControlled, sampleNormalFamilyData]

example : normalFamilyBudget sampleNormalFamilyData = 17 := by
  native_decide

/-- Finite executable readiness audit for normal-family windows. -/
def normalFamilyListReady (windows : List NormalFamilyData) : Bool :=
  windows.all fun d =>
    0 < d.compactCover && d.familyBound ≤ d.compactCover + d.uniformSlack

theorem normalFamilyList_readyWindow :
    normalFamilyListReady
      [{ compactCover := 4, familyBound := 5, uniformSlack := 1 },
       { compactCover := 6, familyBound := 8, uniformSlack := 3 }] = true := by
  unfold normalFamilyListReady
  native_decide


structure UniformNormalFamilyModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformNormalFamilyModelsBudgetCertificate.controlled
    (c : UniformNormalFamilyModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformNormalFamilyModelsBudgetCertificate.budgetControlled
    (c : UniformNormalFamilyModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformNormalFamilyModelsBudgetCertificate.Ready
    (c : UniformNormalFamilyModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformNormalFamilyModelsBudgetCertificate.size
    (c : UniformNormalFamilyModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformNormalFamilyModels_budgetCertificate_le_size
    (c : UniformNormalFamilyModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformNormalFamilyModelsBudgetCertificate :
    UniformNormalFamilyModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformNormalFamilyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.controlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.budgetControlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformNormalFamilyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformNormalFamilyModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformNormalFamilyModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.controlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.budgetControlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]

example :
    sampleUniformNormalFamilyModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformNormalFamilyModelsBudgetCertificate.size := by
  apply uniformNormalFamilyModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.controlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]
  · norm_num [UniformNormalFamilyModelsBudgetCertificate.budgetControlled,
      sampleUniformNormalFamilyModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformNormalFamilyModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformNormalFamilyModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformNormalFamilyModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformNormalFamilyModels
