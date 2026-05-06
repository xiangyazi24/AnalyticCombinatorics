import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rooted set models.

This module records finite bookkeeping for rooted set constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteRootedSetModels

structure RootedSetData where
  rootChoices : ℕ
  setWindow : ℕ
  rootSlack : ℕ
deriving DecidableEq, Repr

def hasRootChoices (d : RootedSetData) : Prop :=
  0 < d.rootChoices

def setWindowControlled (d : RootedSetData) : Prop :=
  d.setWindow ≤ d.rootChoices + d.rootSlack

def rootedSetReady (d : RootedSetData) : Prop :=
  hasRootChoices d ∧ setWindowControlled d

def rootedSetBudget (d : RootedSetData) : ℕ :=
  d.rootChoices + d.setWindow + d.rootSlack

theorem rootedSetReady.hasRootChoices {d : RootedSetData}
    (h : rootedSetReady d) :
    hasRootChoices d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem setWindow_le_budget (d : RootedSetData) :
    d.setWindow ≤ rootedSetBudget d := by
  unfold rootedSetBudget
  omega

def sampleRootedSetData : RootedSetData :=
  { rootChoices := 6, setWindow := 8, rootSlack := 3 }

example : rootedSetReady sampleRootedSetData := by
  norm_num [rootedSetReady, hasRootChoices]
  norm_num [setWindowControlled, sampleRootedSetData]

example : rootedSetBudget sampleRootedSetData = 17 := by
  native_decide

structure RootedSetWindow where
  rootChoices : ℕ
  setWindow : ℕ
  rootSlack : ℕ
  rootedSetBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedSetWindow.setWindowControlled (w : RootedSetWindow) : Prop :=
  w.setWindow ≤ w.rootChoices + w.rootSlack + w.slack

def RootedSetWindow.rootedControlled (w : RootedSetWindow) : Prop :=
  w.rootedSetBudget ≤ w.rootChoices + w.setWindow + w.rootSlack + w.slack

def rootedSetWindowReady (w : RootedSetWindow) : Prop :=
  0 < w.rootChoices ∧
    w.setWindowControlled ∧
    w.rootedControlled

def RootedSetWindow.certificate (w : RootedSetWindow) : ℕ :=
  w.rootChoices + w.setWindow + w.rootSlack + w.slack

theorem rootedSet_budget_le_certificate {w : RootedSetWindow}
    (h : rootedSetWindowReady w) :
    w.rootedSetBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrooted⟩
  exact hrooted

def sampleRootedSetWindow : RootedSetWindow :=
  { rootChoices := 6, setWindow := 8, rootSlack := 3, rootedSetBudget := 16, slack := 0 }

example : rootedSetWindowReady sampleRootedSetWindow := by
  norm_num [rootedSetWindowReady, RootedSetWindow.setWindowControlled,
    RootedSetWindow.rootedControlled, sampleRootedSetWindow]

example : sampleRootedSetWindow.certificate = 17 := by
  native_decide


structure FiniteRootedSetModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRootedSetModelsBudgetCertificate.controlled
    (c : FiniteRootedSetModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRootedSetModelsBudgetCertificate.budgetControlled
    (c : FiniteRootedSetModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRootedSetModelsBudgetCertificate.Ready
    (c : FiniteRootedSetModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRootedSetModelsBudgetCertificate.size
    (c : FiniteRootedSetModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRootedSetModels_budgetCertificate_le_size
    (c : FiniteRootedSetModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRootedSetModelsBudgetCertificate :
    FiniteRootedSetModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRootedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedSetModelsBudgetCertificate.controlled,
      sampleFiniteRootedSetModelsBudgetCertificate]
  · norm_num [FiniteRootedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSetModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRootedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedSetModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRootedSetModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedSetModelsBudgetCertificate.controlled,
      sampleFiniteRootedSetModelsBudgetCertificate]
  · norm_num [FiniteRootedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSetModelsBudgetCertificate]

example :
    sampleFiniteRootedSetModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedSetModelsBudgetCertificate.size := by
  apply finiteRootedSetModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRootedSetModelsBudgetCertificate.controlled,
      sampleFiniteRootedSetModelsBudgetCertificate]
  · norm_num [FiniteRootedSetModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedSetModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRootedSetModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRootedSetModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRootedSetModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRootedSetModels
