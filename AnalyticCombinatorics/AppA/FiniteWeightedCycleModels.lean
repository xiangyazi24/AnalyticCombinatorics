import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted cycle models.

This module records a finite weighted-cycle schema where a positive cycle
length controls total weight with an explicit weight slack.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedCycleModels

structure WeightedCycleData where
  cycleLength : ℕ
  totalWeight : ℕ
  weightSlack : ℕ
deriving DecidableEq, Repr

def hasCycleLength (d : WeightedCycleData) : Prop :=
  0 < d.cycleLength

def totalWeightControlled (d : WeightedCycleData) : Prop :=
  d.totalWeight ≤ d.cycleLength + d.weightSlack

def weightedCycleReady (d : WeightedCycleData) : Prop :=
  hasCycleLength d ∧ totalWeightControlled d

def weightedCycleBudget (d : WeightedCycleData) : ℕ :=
  d.cycleLength + d.totalWeight + d.weightSlack

theorem weightedCycleReady.hasCycleLength {d : WeightedCycleData}
    (h : weightedCycleReady d) :
    hasCycleLength d ∧ totalWeightControlled d ∧ d.totalWeight ≤ weightedCycleBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold weightedCycleBudget
  omega

theorem totalWeight_le_budget (d : WeightedCycleData) :
    d.totalWeight ≤ weightedCycleBudget d := by
  unfold weightedCycleBudget
  omega

def sampleWeightedCycleData : WeightedCycleData :=
  { cycleLength := 7, totalWeight := 9, weightSlack := 3 }

example : weightedCycleReady sampleWeightedCycleData := by
  norm_num [weightedCycleReady, hasCycleLength]
  norm_num [totalWeightControlled, sampleWeightedCycleData]

example : weightedCycleBudget sampleWeightedCycleData = 19 := by
  native_decide

structure WeightedCycleWindow where
  cycleLength : ℕ
  totalWeight : ℕ
  weightSlack : ℕ
  orbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedCycleWindow.weightControlled (w : WeightedCycleWindow) : Prop :=
  w.totalWeight ≤ w.cycleLength + w.weightSlack + w.slack

def WeightedCycleWindow.orbitControlled (w : WeightedCycleWindow) : Prop :=
  w.orbitBudget ≤ w.cycleLength + w.totalWeight + w.weightSlack + w.slack

def weightedCycleWindowReady (w : WeightedCycleWindow) : Prop :=
  0 < w.cycleLength ∧
    w.weightControlled ∧
    w.orbitControlled

def WeightedCycleWindow.certificate (w : WeightedCycleWindow) : ℕ :=
  w.cycleLength + w.totalWeight + w.weightSlack + w.slack

theorem weightedCycle_orbitBudget_le_certificate {w : WeightedCycleWindow}
    (h : weightedCycleWindowReady w) :
    w.orbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def sampleWeightedCycleWindow : WeightedCycleWindow :=
  { cycleLength := 7, totalWeight := 9, weightSlack := 3, orbitBudget := 18, slack := 0 }

example : weightedCycleWindowReady sampleWeightedCycleWindow := by
  norm_num [weightedCycleWindowReady, WeightedCycleWindow.weightControlled,
    WeightedCycleWindow.orbitControlled, sampleWeightedCycleWindow]

example : sampleWeightedCycleWindow.certificate = 19 := by
  native_decide


structure FiniteWeightedCycleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedCycleModelsBudgetCertificate.controlled
    (c : FiniteWeightedCycleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedCycleModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedCycleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedCycleModelsBudgetCertificate.Ready
    (c : FiniteWeightedCycleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedCycleModelsBudgetCertificate.size
    (c : FiniteWeightedCycleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedCycleModels_budgetCertificate_le_size
    (c : FiniteWeightedCycleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedCycleModelsBudgetCertificate :
    FiniteWeightedCycleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedCycleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedCycleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedCycleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedCycleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]

example :
    sampleFiniteWeightedCycleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedCycleModelsBudgetCertificate.size := by
  apply finiteWeightedCycleModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.controlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]
  · norm_num [FiniteWeightedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedCycleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteWeightedCycleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedCycleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedCycleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedCycleModels
