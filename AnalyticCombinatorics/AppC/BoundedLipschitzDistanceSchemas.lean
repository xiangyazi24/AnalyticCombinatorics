import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bounded Lipschitz distance schemas.

This module records finite bookkeeping for bounded Lipschitz distances.
-/

namespace AnalyticCombinatorics.AppC.BoundedLipschitzDistanceSchemas

structure BoundedLipschitzDistanceData where
  testFunctions : ℕ
  distanceWindow : ℕ
  lipschitzSlack : ℕ
deriving DecidableEq, Repr

def hasTestFunctions (d : BoundedLipschitzDistanceData) : Prop :=
  0 < d.testFunctions

def distanceWindowControlled
    (d : BoundedLipschitzDistanceData) : Prop :=
  d.distanceWindow ≤ d.testFunctions + d.lipschitzSlack

def boundedLipschitzDistanceReady
    (d : BoundedLipschitzDistanceData) : Prop :=
  hasTestFunctions d ∧ distanceWindowControlled d

def boundedLipschitzDistanceBudget
    (d : BoundedLipschitzDistanceData) : ℕ :=
  d.testFunctions + d.distanceWindow + d.lipschitzSlack

theorem boundedLipschitzDistanceReady.hasTestFunctions
    {d : BoundedLipschitzDistanceData}
    (h : boundedLipschitzDistanceReady d) :
    hasTestFunctions d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem distanceWindow_le_budget
    (d : BoundedLipschitzDistanceData) :
    d.distanceWindow ≤ boundedLipschitzDistanceBudget d := by
  unfold boundedLipschitzDistanceBudget
  omega

def sampleBoundedLipschitzDistanceData :
    BoundedLipschitzDistanceData :=
  { testFunctions := 7, distanceWindow := 9, lipschitzSlack := 3 }

example : boundedLipschitzDistanceReady
    sampleBoundedLipschitzDistanceData := by
  norm_num [boundedLipschitzDistanceReady, hasTestFunctions]
  norm_num [distanceWindowControlled, sampleBoundedLipschitzDistanceData]

example :
    boundedLipschitzDistanceBudget sampleBoundedLipschitzDistanceData = 19 := by
  native_decide

structure BoundedLipschitzDistanceWindow where
  testWindow : ℕ
  distanceWindow : ℕ
  lipschitzSlack : ℕ
  distanceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedLipschitzDistanceWindow.distanceControlled
    (w : BoundedLipschitzDistanceWindow) : Prop :=
  w.distanceWindow ≤ w.testWindow + w.lipschitzSlack + w.slack

def boundedLipschitzDistanceWindowReady
    (w : BoundedLipschitzDistanceWindow) : Prop :=
  0 < w.testWindow ∧ w.distanceControlled ∧
    w.distanceBudget ≤ w.testWindow + w.distanceWindow + w.slack

def BoundedLipschitzDistanceWindow.certificate
    (w : BoundedLipschitzDistanceWindow) : ℕ :=
  w.testWindow + w.distanceWindow + w.lipschitzSlack + w.distanceBudget + w.slack

theorem boundedLipschitzDistance_budget_le_certificate
    (w : BoundedLipschitzDistanceWindow) :
    w.distanceBudget ≤ w.certificate := by
  unfold BoundedLipschitzDistanceWindow.certificate
  omega

def sampleBoundedLipschitzDistanceWindow :
    BoundedLipschitzDistanceWindow :=
  { testWindow := 6, distanceWindow := 8, lipschitzSlack := 2,
    distanceBudget := 15, slack := 1 }

example : boundedLipschitzDistanceWindowReady
    sampleBoundedLipschitzDistanceWindow := by
  norm_num [boundedLipschitzDistanceWindowReady,
    BoundedLipschitzDistanceWindow.distanceControlled,
    sampleBoundedLipschitzDistanceWindow]


structure BoundedLipschitzDistanceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundedLipschitzDistanceSchemasBudgetCertificate.controlled
    (c : BoundedLipschitzDistanceSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoundedLipschitzDistanceSchemasBudgetCertificate.budgetControlled
    (c : BoundedLipschitzDistanceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundedLipschitzDistanceSchemasBudgetCertificate.Ready
    (c : BoundedLipschitzDistanceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundedLipschitzDistanceSchemasBudgetCertificate.size
    (c : BoundedLipschitzDistanceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundedLipschitzDistanceSchemas_budgetCertificate_le_size
    (c : BoundedLipschitzDistanceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundedLipschitzDistanceSchemasBudgetCertificate :
    BoundedLipschitzDistanceSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoundedLipschitzDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]

example : sampleBoundedLipschitzDistanceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]

example :
    sampleBoundedLipschitzDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate.size := by
  apply boundedLipschitzDistanceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.controlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]
  · norm_num [BoundedLipschitzDistanceSchemasBudgetCertificate.budgetControlled,
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleBoundedLipschitzDistanceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundedLipschitzDistanceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List BoundedLipschitzDistanceSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundedLipschitzDistanceSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBoundedLipschitzDistanceSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.BoundedLipschitzDistanceSchemas
