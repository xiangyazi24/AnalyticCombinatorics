import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite cycle pointing models.

This module records finite bookkeeping for cycle pointing operations.
-/

namespace AnalyticCombinatorics.AppA.FiniteCyclePointingModels

structure CyclePointingData where
  cycleCount : ℕ
  pointPositions : ℕ
  pointingSlack : ℕ
deriving DecidableEq, Repr

def hasCycleCount (d : CyclePointingData) : Prop :=
  0 < d.cycleCount

def pointPositionsControlled (d : CyclePointingData) : Prop :=
  d.pointPositions ≤ d.cycleCount + d.pointingSlack

def cyclePointingReady (d : CyclePointingData) : Prop :=
  hasCycleCount d ∧ pointPositionsControlled d

def cyclePointingBudget (d : CyclePointingData) : ℕ :=
  d.cycleCount + d.pointPositions + d.pointingSlack

theorem cyclePointingReady.hasCycleCount {d : CyclePointingData}
    (h : cyclePointingReady d) :
    hasCycleCount d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointPositions_le_budget (d : CyclePointingData) :
    d.pointPositions ≤ cyclePointingBudget d := by
  unfold cyclePointingBudget
  omega

def sampleCyclePointingData : CyclePointingData :=
  { cycleCount := 5, pointPositions := 7, pointingSlack := 3 }

example : cyclePointingReady sampleCyclePointingData := by
  norm_num [cyclePointingReady, hasCycleCount]
  norm_num [pointPositionsControlled, sampleCyclePointingData]

example : cyclePointingBudget sampleCyclePointingData = 15 := by
  native_decide

structure CyclePointingWindow where
  cycleCount : ℕ
  pointPositions : ℕ
  pointingSlack : ℕ
  pointedCycleBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CyclePointingWindow.positionsControlled (w : CyclePointingWindow) : Prop :=
  w.pointPositions ≤ w.cycleCount + w.pointingSlack + w.slack

def CyclePointingWindow.pointedCycleControlled (w : CyclePointingWindow) : Prop :=
  w.pointedCycleBudget ≤ w.cycleCount + w.pointPositions + w.pointingSlack + w.slack

def cyclePointingWindowReady (w : CyclePointingWindow) : Prop :=
  0 < w.cycleCount ∧
    w.positionsControlled ∧
    w.pointedCycleControlled

def CyclePointingWindow.certificate (w : CyclePointingWindow) : ℕ :=
  w.cycleCount + w.pointPositions + w.pointingSlack + w.slack

theorem cyclePointing_pointedCycleBudget_le_certificate {w : CyclePointingWindow}
    (h : cyclePointingWindowReady w) :
    w.pointedCycleBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hpointed⟩
  exact hpointed

def sampleCyclePointingWindow : CyclePointingWindow :=
  { cycleCount := 5, pointPositions := 7, pointingSlack := 3, pointedCycleBudget := 14,
    slack := 0 }

example : cyclePointingWindowReady sampleCyclePointingWindow := by
  norm_num [cyclePointingWindowReady, CyclePointingWindow.positionsControlled,
    CyclePointingWindow.pointedCycleControlled, sampleCyclePointingWindow]

example : sampleCyclePointingWindow.certificate = 15 := by
  native_decide


structure FiniteCyclePointingModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCyclePointingModelsBudgetCertificate.controlled
    (c : FiniteCyclePointingModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCyclePointingModelsBudgetCertificate.budgetControlled
    (c : FiniteCyclePointingModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCyclePointingModelsBudgetCertificate.Ready
    (c : FiniteCyclePointingModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCyclePointingModelsBudgetCertificate.size
    (c : FiniteCyclePointingModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCyclePointingModels_budgetCertificate_le_size
    (c : FiniteCyclePointingModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCyclePointingModelsBudgetCertificate :
    FiniteCyclePointingModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteCyclePointingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.controlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCyclePointingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCyclePointingModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteCyclePointingModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.controlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]

example :
    sampleFiniteCyclePointingModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCyclePointingModelsBudgetCertificate.size := by
  apply finiteCyclePointingModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.controlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]
  · norm_num [FiniteCyclePointingModelsBudgetCertificate.budgetControlled,
      sampleFiniteCyclePointingModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteCyclePointingModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCyclePointingModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteCyclePointingModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteCyclePointingModels
