import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite pointed set models.

This module records finite bookkeeping for pointed set constructions.
-/

namespace AnalyticCombinatorics.AppA.FinitePointedSetModels

structure PointedSetData where
  setSize : ℕ
  pointWindow : ℕ
  pointingSlack : ℕ
deriving DecidableEq, Repr

def hasSetSize (d : PointedSetData) : Prop :=
  0 < d.setSize

def pointWindowControlled (d : PointedSetData) : Prop :=
  d.pointWindow ≤ d.setSize + d.pointingSlack

def pointedSetReady (d : PointedSetData) : Prop :=
  hasSetSize d ∧ pointWindowControlled d

def pointedSetBudget (d : PointedSetData) : ℕ :=
  d.setSize + d.pointWindow + d.pointingSlack

theorem pointedSetReady.hasSetSize {d : PointedSetData}
    (h : pointedSetReady d) :
    hasSetSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointWindow_le_budget (d : PointedSetData) :
    d.pointWindow ≤ pointedSetBudget d := by
  unfold pointedSetBudget
  omega

def samplePointedSetData : PointedSetData :=
  { setSize := 6, pointWindow := 8, pointingSlack := 3 }

example : pointedSetReady samplePointedSetData := by
  norm_num [pointedSetReady, hasSetSize]
  norm_num [pointWindowControlled, samplePointedSetData]

example : pointedSetBudget samplePointedSetData = 17 := by
  native_decide

structure PointedSetWindow where
  setSize : ℕ
  pointWindow : ℕ
  pointingSlack : ℕ
  transportBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointedSetWindow.pointWindowControlled (w : PointedSetWindow) : Prop :=
  w.pointWindow ≤ w.setSize + w.pointingSlack + w.slack

def PointedSetWindow.transportControlled (w : PointedSetWindow) : Prop :=
  w.transportBudget ≤ w.setSize + w.pointWindow + w.pointingSlack + w.slack

def pointedSetWindowReady (w : PointedSetWindow) : Prop :=
  0 < w.setSize ∧
    w.pointWindowControlled ∧
    w.transportControlled

def PointedSetWindow.certificate (w : PointedSetWindow) : ℕ :=
  w.setSize + w.pointWindow + w.pointingSlack + w.slack

theorem pointedSet_transportBudget_le_certificate {w : PointedSetWindow}
    (h : pointedSetWindowReady w) :
    w.transportBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htransport⟩
  exact htransport

def samplePointedSetWindow : PointedSetWindow :=
  { setSize := 6, pointWindow := 8, pointingSlack := 3, transportBudget := 16, slack := 0 }

example : pointedSetWindowReady samplePointedSetWindow := by
  norm_num [pointedSetWindowReady, PointedSetWindow.pointWindowControlled,
    PointedSetWindow.transportControlled, samplePointedSetWindow]

example : samplePointedSetWindow.certificate = 17 := by
  native_decide


structure FinitePointedSetModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePointedSetModelsBudgetCertificate.controlled
    (c : FinitePointedSetModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePointedSetModelsBudgetCertificate.budgetControlled
    (c : FinitePointedSetModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePointedSetModelsBudgetCertificate.Ready
    (c : FinitePointedSetModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePointedSetModelsBudgetCertificate.size
    (c : FinitePointedSetModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePointedSetModels_budgetCertificate_le_size
    (c : FinitePointedSetModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePointedSetModelsBudgetCertificate :
    FinitePointedSetModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePointedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedSetModelsBudgetCertificate.controlled,
      sampleFinitePointedSetModelsBudgetCertificate]
  · norm_num [FinitePointedSetModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSetModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePointedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedSetModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePointedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedSetModelsBudgetCertificate.controlled,
      sampleFinitePointedSetModelsBudgetCertificate]
  · norm_num [FinitePointedSetModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSetModelsBudgetCertificate]

example :
    sampleFinitePointedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedSetModelsBudgetCertificate.size := by
  apply finitePointedSetModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePointedSetModelsBudgetCertificate.controlled,
      sampleFinitePointedSetModelsBudgetCertificate]
  · norm_num [FinitePointedSetModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedSetModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FinitePointedSetModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePointedSetModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePointedSetModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePointedSetModels
