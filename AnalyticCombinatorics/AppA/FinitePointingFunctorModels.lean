import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite pointing functor models.

The finite schema stores base objects, pointing choices, and functorial
slack.
-/

namespace AnalyticCombinatorics.AppA.FinitePointingFunctorModels

structure PointingFunctorData where
  baseObjects : ℕ
  pointingChoices : ℕ
  functorSlack : ℕ
deriving DecidableEq, Repr

def baseObjectsNonempty (d : PointingFunctorData) : Prop :=
  0 < d.baseObjects

def pointingChoicesControlled (d : PointingFunctorData) : Prop :=
  d.pointingChoices ≤ d.baseObjects + d.functorSlack

def pointingFunctorReady (d : PointingFunctorData) : Prop :=
  baseObjectsNonempty d ∧ pointingChoicesControlled d

def pointingFunctorBudget (d : PointingFunctorData) : ℕ :=
  d.baseObjects + d.pointingChoices + d.functorSlack

theorem pointingFunctorReady.base {d : PointingFunctorData}
    (h : pointingFunctorReady d) :
    baseObjectsNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointingChoices_le_functorBudget (d : PointingFunctorData) :
    d.pointingChoices ≤ pointingFunctorBudget d := by
  unfold pointingFunctorBudget
  omega

def samplePointingFunctorData : PointingFunctorData :=
  { baseObjects := 6, pointingChoices := 8, functorSlack := 3 }

example : pointingFunctorReady samplePointingFunctorData := by
  norm_num [pointingFunctorReady, baseObjectsNonempty]
  norm_num [pointingChoicesControlled, samplePointingFunctorData]

example : pointingFunctorBudget samplePointingFunctorData = 17 := by
  native_decide

structure PointingFunctorWindow where
  baseObjects : ℕ
  pointingChoices : ℕ
  functorSlack : ℕ
  functorialityBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PointingFunctorWindow.choicesControlled (w : PointingFunctorWindow) : Prop :=
  w.pointingChoices ≤ w.baseObjects + w.functorSlack + w.slack

def PointingFunctorWindow.functorialityControlled (w : PointingFunctorWindow) : Prop :=
  w.functorialityBudget ≤ w.baseObjects + w.pointingChoices + w.functorSlack + w.slack

def pointingFunctorWindowReady (w : PointingFunctorWindow) : Prop :=
  0 < w.baseObjects ∧
    w.choicesControlled ∧
    w.functorialityControlled

def PointingFunctorWindow.certificate (w : PointingFunctorWindow) : ℕ :=
  w.baseObjects + w.pointingChoices + w.functorSlack + w.slack

theorem pointingFunctor_functorialityBudget_le_certificate {w : PointingFunctorWindow}
    (h : pointingFunctorWindowReady w) :
    w.functorialityBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hfunctoriality⟩
  exact hfunctoriality

def samplePointingFunctorWindow : PointingFunctorWindow :=
  { baseObjects := 6, pointingChoices := 8, functorSlack := 3, functorialityBudget := 16,
    slack := 0 }

example : pointingFunctorWindowReady samplePointingFunctorWindow := by
  norm_num [pointingFunctorWindowReady, PointingFunctorWindow.choicesControlled,
    PointingFunctorWindow.functorialityControlled, samplePointingFunctorWindow]

example : samplePointingFunctorWindow.certificate = 17 := by
  native_decide


structure FinitePointingFunctorModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePointingFunctorModelsBudgetCertificate.controlled
    (c : FinitePointingFunctorModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePointingFunctorModelsBudgetCertificate.budgetControlled
    (c : FinitePointingFunctorModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePointingFunctorModelsBudgetCertificate.Ready
    (c : FinitePointingFunctorModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePointingFunctorModelsBudgetCertificate.size
    (c : FinitePointingFunctorModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePointingFunctorModels_budgetCertificate_le_size
    (c : FinitePointingFunctorModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePointingFunctorModelsBudgetCertificate :
    FinitePointingFunctorModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePointingFunctorModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.controlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.budgetControlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePointingFunctorModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointingFunctorModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePointingFunctorModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.controlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.budgetControlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]

example :
    sampleFinitePointingFunctorModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointingFunctorModelsBudgetCertificate.size := by
  apply finitePointingFunctorModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.controlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]
  · norm_num [FinitePointingFunctorModelsBudgetCertificate.budgetControlled,
      sampleFinitePointingFunctorModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FinitePointingFunctorModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePointingFunctorModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePointingFunctorModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePointingFunctorModels
