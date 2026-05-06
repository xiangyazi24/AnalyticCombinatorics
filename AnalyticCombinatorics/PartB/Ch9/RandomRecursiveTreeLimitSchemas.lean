import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random recursive tree limit schema bookkeeping.

The finite data tracks growth steps, height budget, and variance budget for
recursive tree asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomRecursiveTreeLimitSchemas

structure RecursiveTreeLimitData where
  growthSteps : ℕ
  heightBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def nonzeroGrowth (d : RecursiveTreeLimitData) : Prop :=
  0 < d.growthSteps

def positiveVariance (d : RecursiveTreeLimitData) : Prop :=
  0 < d.varianceBudget

def recursiveTreeLimitReady (d : RecursiveTreeLimitData) : Prop :=
  nonzeroGrowth d ∧ positiveVariance d

def treeLimitBudget (d : RecursiveTreeLimitData) : ℕ :=
  d.growthSteps + d.heightBudget + d.varianceBudget

theorem recursiveTreeLimitReady.growth {d : RecursiveTreeLimitData}
    (h : recursiveTreeLimitReady d) :
    nonzeroGrowth d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem growthSteps_le_treeLimitBudget (d : RecursiveTreeLimitData) :
    d.growthSteps ≤ treeLimitBudget d := by
  unfold treeLimitBudget
  omega

def sampleRecursiveTreeLimit : RecursiveTreeLimitData :=
  { growthSteps := 8, heightBudget := 4, varianceBudget := 3 }

example : recursiveTreeLimitReady sampleRecursiveTreeLimit := by
  norm_num [recursiveTreeLimitReady, nonzeroGrowth, positiveVariance, sampleRecursiveTreeLimit]

example : treeLimitBudget sampleRecursiveTreeLimit = 15 := by
  native_decide

/-- Finite executable readiness audit for recursive-tree limit data. -/
def recursiveTreeLimitDataListReady
    (data : List RecursiveTreeLimitData) : Bool :=
  data.all fun d =>
    0 < d.growthSteps &&
      0 < d.varianceBudget &&
        d.heightBudget ≤ d.growthSteps

theorem recursiveTreeLimitDataList_readyWindow :
    recursiveTreeLimitDataListReady
      [{ growthSteps := 5, heightBudget := 3, varianceBudget := 2 },
       { growthSteps := 8, heightBudget := 4, varianceBudget := 3 }] = true := by
  unfold recursiveTreeLimitDataListReady
  native_decide

structure RecursiveTreeWindow where
  growthSteps : ℕ
  heightBudget : ℕ
  varianceBudget : ℕ
  profileBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveTreeWindow.heightControlled (w : RecursiveTreeWindow) : Prop :=
  w.heightBudget ≤ w.growthSteps + w.slack

def RecursiveTreeWindow.profileControlled (w : RecursiveTreeWindow) : Prop :=
  w.profileBudget ≤ w.growthSteps + w.heightBudget + w.varianceBudget + w.slack

def recursiveTreeWindowReady (w : RecursiveTreeWindow) : Prop :=
  0 < w.growthSteps ∧
    0 < w.varianceBudget ∧
    w.heightControlled ∧
    w.profileControlled

def RecursiveTreeWindow.certificate (w : RecursiveTreeWindow) : ℕ :=
  w.growthSteps + w.heightBudget + w.varianceBudget + w.slack

theorem recursiveTree_profileBudget_le_certificate {w : RecursiveTreeWindow}
    (h : recursiveTreeWindowReady w) :
    w.profileBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hprofile⟩
  exact hprofile

def sampleRecursiveTreeWindow : RecursiveTreeWindow :=
  { growthSteps := 8, heightBudget := 4, varianceBudget := 3, profileBudget := 12, slack := 0 }

example : recursiveTreeWindowReady sampleRecursiveTreeWindow := by
  norm_num [recursiveTreeWindowReady, RecursiveTreeWindow.heightControlled,
    RecursiveTreeWindow.profileControlled, sampleRecursiveTreeWindow]

example : sampleRecursiveTreeWindow.certificate = 15 := by
  native_decide


structure RandomRecursiveTreeLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomRecursiveTreeLimitSchemasBudgetCertificate.controlled
    (c : RandomRecursiveTreeLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomRecursiveTreeLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomRecursiveTreeLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomRecursiveTreeLimitSchemasBudgetCertificate.Ready
    (c : RandomRecursiveTreeLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomRecursiveTreeLimitSchemasBudgetCertificate.size
    (c : RandomRecursiveTreeLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomRecursiveTreeLimitSchemas_budgetCertificate_le_size
    (c : RandomRecursiveTreeLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomRecursiveTreeLimitSchemasBudgetCertificate :
    RandomRecursiveTreeLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.controlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]

example :
    sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.size := by
  apply randomRecursiveTreeLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.controlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.controlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]
  · norm_num [RandomRecursiveTreeLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomRecursiveTreeLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomRecursiveTreeLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomRecursiveTreeLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomRecursiveTreeLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomRecursiveTreeLimitSchemas
