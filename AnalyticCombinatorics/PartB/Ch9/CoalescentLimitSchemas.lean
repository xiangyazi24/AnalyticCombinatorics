import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Coalescent limit schema bookkeeping.

The finite data records merge rate, active components, and variance budget
for coalescent-type limit laws.
-/

namespace AnalyticCombinatorics.PartB.Ch9.CoalescentLimitSchemas

structure CoalescentData where
  activeComponents : ℕ
  mergeRate : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def nontrivialCoalescent (d : CoalescentData) : Prop :=
  1 < d.activeComponents

def positiveMergeRate (d : CoalescentData) : Prop :=
  0 < d.mergeRate

def coalescentReady (d : CoalescentData) : Prop :=
  nontrivialCoalescent d ∧ positiveMergeRate d ∧ 0 < d.varianceBudget

def componentBudgetAfterMerge (d : CoalescentData) : ℕ :=
  d.activeComponents - 1

theorem coalescentReady.nontrivial {d : CoalescentData}
    (h : coalescentReady d) :
    nontrivialCoalescent d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem componentBudgetAfterMerge_positive {d : CoalescentData}
    (h : nontrivialCoalescent d) :
    0 < componentBudgetAfterMerge d := by
  unfold nontrivialCoalescent componentBudgetAfterMerge at *
  omega

def sampleCoalescent : CoalescentData :=
  { activeComponents := 5, mergeRate := 2, varianceBudget := 4 }

example : coalescentReady sampleCoalescent := by
  norm_num [coalescentReady, nontrivialCoalescent, positiveMergeRate, sampleCoalescent]

example : componentBudgetAfterMerge sampleCoalescent = 4 := by
  native_decide

/-- Finite executable readiness audit for coalescent limit data. -/
def coalescentDataListReady (data : List CoalescentData) : Bool :=
  data.all fun d =>
    1 < d.activeComponents && 0 < d.mergeRate && 0 < d.varianceBudget

theorem coalescentDataList_readyWindow :
    coalescentDataListReady
      [{ activeComponents := 3, mergeRate := 1, varianceBudget := 2 },
       { activeComponents := 5, mergeRate := 2, varianceBudget := 4 }] = true := by
  unfold coalescentDataListReady
  native_decide

structure CoalescentWindow where
  activeComponents : ℕ
  mergeRate : ℕ
  varianceBudget : ℕ
  trajectoryBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoalescentWindow.trajectoryControlled (w : CoalescentWindow) : Prop :=
  w.trajectoryBudget ≤ w.activeComponents + w.mergeRate + w.varianceBudget + w.slack

def coalescentWindowReady (w : CoalescentWindow) : Prop :=
  1 < w.activeComponents ∧
    0 < w.mergeRate ∧
    0 < w.varianceBudget ∧
    w.trajectoryControlled

def CoalescentWindow.certificate (w : CoalescentWindow) : ℕ :=
  w.activeComponents + w.mergeRate + w.varianceBudget + w.slack

theorem coalescent_trajectoryBudget_le_certificate {w : CoalescentWindow}
    (h : coalescentWindowReady w) :
    w.trajectoryBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, htraj⟩
  exact htraj

def sampleCoalescentWindow : CoalescentWindow :=
  { activeComponents := 5, mergeRate := 2, varianceBudget := 4, trajectoryBudget := 10,
    slack := 0 }

example : coalescentWindowReady sampleCoalescentWindow := by
  norm_num [coalescentWindowReady, CoalescentWindow.trajectoryControlled, sampleCoalescentWindow]

example : sampleCoalescentWindow.certificate = 11 := by
  native_decide


structure CoalescentLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoalescentLimitSchemasBudgetCertificate.controlled
    (c : CoalescentLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CoalescentLimitSchemasBudgetCertificate.budgetControlled
    (c : CoalescentLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CoalescentLimitSchemasBudgetCertificate.Ready
    (c : CoalescentLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoalescentLimitSchemasBudgetCertificate.size
    (c : CoalescentLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coalescentLimitSchemas_budgetCertificate_le_size
    (c : CoalescentLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoalescentLimitSchemasBudgetCertificate :
    CoalescentLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCoalescentLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescentLimitSchemasBudgetCertificate.controlled,
      sampleCoalescentLimitSchemasBudgetCertificate]
  · norm_num [CoalescentLimitSchemasBudgetCertificate.budgetControlled,
      sampleCoalescentLimitSchemasBudgetCertificate]

example :
    sampleCoalescentLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescentLimitSchemasBudgetCertificate.size := by
  apply coalescentLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [CoalescentLimitSchemasBudgetCertificate.controlled,
      sampleCoalescentLimitSchemasBudgetCertificate]
  · norm_num [CoalescentLimitSchemasBudgetCertificate.budgetControlled,
      sampleCoalescentLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoalescentLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [CoalescentLimitSchemasBudgetCertificate.controlled,
      sampleCoalescentLimitSchemasBudgetCertificate]
  · norm_num [CoalescentLimitSchemasBudgetCertificate.budgetControlled,
      sampleCoalescentLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoalescentLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleCoalescentLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CoalescentLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoalescentLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCoalescentLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.CoalescentLimitSchemas
