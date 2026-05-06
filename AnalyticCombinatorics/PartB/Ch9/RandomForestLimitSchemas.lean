import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random forest limit schema bookkeeping.

The finite data records component counts, tree budgets, and variance lower
bounds for random forest asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomForestLimitSchemas

structure RandomForestData where
  componentCount : ℕ
  treeBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def nonemptyForest (d : RandomForestData) : Prop :=
  0 < d.componentCount

def positiveVariance (d : RandomForestData) : Prop :=
  0 < d.varianceBudget

def randomForestLimitReady (d : RandomForestData) : Prop :=
  nonemptyForest d ∧ positiveVariance d

def forestBudget (d : RandomForestData) : ℕ :=
  d.componentCount + d.treeBudget + d.varianceBudget

theorem randomForestLimitReady.nonempty {d : RandomForestData}
    (h : randomForestLimitReady d) :
    nonemptyForest d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem componentCount_le_forestBudget (d : RandomForestData) :
    d.componentCount ≤ forestBudget d := by
  unfold forestBudget
  omega

def sampleForest : RandomForestData :=
  { componentCount := 5, treeBudget := 9, varianceBudget := 4 }

example : randomForestLimitReady sampleForest := by
  norm_num [randomForestLimitReady, nonemptyForest, positiveVariance, sampleForest]

example : forestBudget sampleForest = 18 := by
  native_decide

/-- Finite executable readiness audit for random forest limit data. -/
def randomForestDataListReady
    (data : List RandomForestData) : Bool :=
  data.all fun d =>
    0 < d.componentCount &&
      0 < d.varianceBudget &&
        d.componentCount ≤ d.treeBudget

theorem randomForestDataList_readyWindow :
    randomForestDataListReady
      [{ componentCount := 3, treeBudget := 5, varianceBudget := 2 },
       { componentCount := 5, treeBudget := 9, varianceBudget := 4 }] = true := by
  unfold randomForestDataListReady
  native_decide

structure RandomForestWindow where
  componentCount : ℕ
  treeBudget : ℕ
  varianceBudget : ℕ
  heightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomForestWindow.treeControlled (w : RandomForestWindow) : Prop :=
  w.componentCount ≤ w.treeBudget + w.slack

def RandomForestWindow.heightControlled (w : RandomForestWindow) : Prop :=
  w.heightBudget ≤ w.treeBudget + w.varianceBudget + w.slack

def randomForestWindowReady (w : RandomForestWindow) : Prop :=
  0 < w.componentCount ∧
    0 < w.varianceBudget ∧
    w.treeControlled ∧
    w.heightControlled

def RandomForestWindow.certificate (w : RandomForestWindow) : ℕ :=
  w.treeBudget + w.varianceBudget + w.slack

theorem randomForest_heightBudget_le_certificate {w : RandomForestWindow}
    (h : randomForestWindowReady w) :
    w.heightBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hheight⟩
  exact hheight

def sampleRandomForestWindow : RandomForestWindow :=
  { componentCount := 5, treeBudget := 9, varianceBudget := 4, heightBudget := 11, slack := 0 }

example : randomForestWindowReady sampleRandomForestWindow := by
  norm_num [randomForestWindowReady, RandomForestWindow.treeControlled,
    RandomForestWindow.heightControlled, sampleRandomForestWindow]

example : sampleRandomForestWindow.certificate = 13 := by
  native_decide


structure RandomForestLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomForestLimitSchemasBudgetCertificate.controlled
    (c : RandomForestLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomForestLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomForestLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomForestLimitSchemasBudgetCertificate.Ready
    (c : RandomForestLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomForestLimitSchemasBudgetCertificate.size
    (c : RandomForestLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomForestLimitSchemas_budgetCertificate_le_size
    (c : RandomForestLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomForestLimitSchemasBudgetCertificate :
    RandomForestLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomForestLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomForestLimitSchemasBudgetCertificate.controlled,
      sampleRandomForestLimitSchemasBudgetCertificate]
  · norm_num [RandomForestLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomForestLimitSchemasBudgetCertificate]

example :
    sampleRandomForestLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomForestLimitSchemasBudgetCertificate.size := by
  apply randomForestLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomForestLimitSchemasBudgetCertificate.controlled,
      sampleRandomForestLimitSchemasBudgetCertificate]
  · norm_num [RandomForestLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomForestLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomForestLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomForestLimitSchemasBudgetCertificate.controlled,
      sampleRandomForestLimitSchemasBudgetCertificate]
  · norm_num [RandomForestLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomForestLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomForestLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomForestLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomForestLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomForestLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomForestLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomForestLimitSchemas
