import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Additional random-tree limit schemas.

This module records finite branching, height, and variance budgets for
random tree limit laws not covered by the earlier tree modules.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomTreeLimitSchemas2

structure RandomTreeLimitData where
  branchingBudget : ℕ
  heightScale : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveBranching (d : RandomTreeLimitData) : Prop :=
  0 < d.branchingBudget

def positiveHeightScale (d : RandomTreeLimitData) : Prop :=
  0 < d.heightScale

def randomTreeLimitReady (d : RandomTreeLimitData) : Prop :=
  positiveBranching d ∧ positiveHeightScale d ∧ 0 < d.varianceBudget

def randomTreeBudget (d : RandomTreeLimitData) : ℕ :=
  d.branchingBudget + d.heightScale + d.varianceBudget

theorem randomTreeLimitReady.branching {d : RandomTreeLimitData}
    (h : randomTreeLimitReady d) :
    positiveBranching d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem branchingBudget_le_total (d : RandomTreeLimitData) :
    d.branchingBudget ≤ randomTreeBudget d := by
  unfold randomTreeBudget
  omega

def sampleRandomTreeLimit : RandomTreeLimitData :=
  { branchingBudget := 3, heightScale := 8, varianceBudget := 5 }

example : randomTreeLimitReady sampleRandomTreeLimit := by
  norm_num
    [randomTreeLimitReady, positiveBranching, positiveHeightScale, sampleRandomTreeLimit]

example : randomTreeBudget sampleRandomTreeLimit = 16 := by
  native_decide

structure RandomTreeLimitWindow where
  branchingBudget : ℕ
  heightScale : ℕ
  varianceBudget : ℕ
  profileBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomTreeLimitWindow.profileControlled (w : RandomTreeLimitWindow) : Prop :=
  w.profileBudget ≤ w.branchingBudget + w.heightScale + w.varianceBudget + w.slack

def randomTreeLimitWindowReady (w : RandomTreeLimitWindow) : Prop :=
  0 < w.branchingBudget ∧
    0 < w.heightScale ∧
    0 < w.varianceBudget ∧
    w.profileControlled

def RandomTreeLimitWindow.certificate (w : RandomTreeLimitWindow) : ℕ :=
  w.branchingBudget + w.heightScale + w.varianceBudget + w.slack

theorem randomTree_profileBudget_le_certificate {w : RandomTreeLimitWindow}
    (h : randomTreeLimitWindowReady w) :
    w.profileBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hprofile⟩
  exact hprofile

def sampleRandomTreeLimitWindow : RandomTreeLimitWindow :=
  { branchingBudget := 3, heightScale := 8, varianceBudget := 5, profileBudget := 15, slack := 0 }

example : randomTreeLimitWindowReady sampleRandomTreeLimitWindow := by
  norm_num [randomTreeLimitWindowReady, RandomTreeLimitWindow.profileControlled,
    sampleRandomTreeLimitWindow]

example : sampleRandomTreeLimitWindow.certificate = 16 := by
  native_decide


structure RandomTreeLimitSchemas2BudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomTreeLimitSchemas2BudgetCertificate.controlled
    (c : RandomTreeLimitSchemas2BudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomTreeLimitSchemas2BudgetCertificate.budgetControlled
    (c : RandomTreeLimitSchemas2BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomTreeLimitSchemas2BudgetCertificate.Ready
    (c : RandomTreeLimitSchemas2BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomTreeLimitSchemas2BudgetCertificate.size
    (c : RandomTreeLimitSchemas2BudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomTreeLimitSchemas2_budgetCertificate_le_size
    (c : RandomTreeLimitSchemas2BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomTreeLimitSchemas2BudgetCertificate :
    RandomTreeLimitSchemas2BudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomTreeLimitSchemas2BudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.controlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.budgetControlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomTreeLimitSchemas2BudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTreeLimitSchemas2BudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomTreeLimitSchemas2BudgetCertificate.Ready := by
  constructor
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.controlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.budgetControlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]

example :
    sampleRandomTreeLimitSchemas2BudgetCertificate.certificateBudgetWindow ≤
      sampleRandomTreeLimitSchemas2BudgetCertificate.size := by
  apply randomTreeLimitSchemas2_budgetCertificate_le_size
  constructor
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.controlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]
  · norm_num [RandomTreeLimitSchemas2BudgetCertificate.budgetControlled,
      sampleRandomTreeLimitSchemas2BudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RandomTreeLimitSchemas2BudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomTreeLimitSchemas2BudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomTreeLimitSchemas2BudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.RandomTreeLimitSchemas2
