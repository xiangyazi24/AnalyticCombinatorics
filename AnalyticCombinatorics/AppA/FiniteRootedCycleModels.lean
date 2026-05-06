import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rooted cycle models.

This module records finite bookkeeping for rooted cycle constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteRootedCycleModels

structure RootedCycleData where
  cycleRoots : ℕ
  rotationWindow : ℕ
  cycleSlack : ℕ
deriving DecidableEq, Repr

def hasCycleRoots (d : RootedCycleData) : Prop :=
  0 < d.cycleRoots

def rotationWindowControlled (d : RootedCycleData) : Prop :=
  d.rotationWindow ≤ d.cycleRoots + d.cycleSlack

def rootedCycleReady (d : RootedCycleData) : Prop :=
  hasCycleRoots d ∧ rotationWindowControlled d

def rootedCycleBudget (d : RootedCycleData) : ℕ :=
  d.cycleRoots + d.rotationWindow + d.cycleSlack

theorem rootedCycleReady.hasCycleRoots {d : RootedCycleData}
    (h : rootedCycleReady d) :
    hasCycleRoots d ∧ rotationWindowControlled d ∧ d.rotationWindow ≤ rootedCycleBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold rootedCycleBudget
  omega

theorem rotationWindow_le_budget (d : RootedCycleData) :
    d.rotationWindow ≤ rootedCycleBudget d := by
  unfold rootedCycleBudget
  omega

def sampleRootedCycleData : RootedCycleData :=
  { cycleRoots := 7, rotationWindow := 9, cycleSlack := 3 }

example : rootedCycleReady sampleRootedCycleData := by
  norm_num [rootedCycleReady, hasCycleRoots]
  norm_num [rotationWindowControlled, sampleRootedCycleData]

example : rootedCycleBudget sampleRootedCycleData = 19 := by
  native_decide

structure RootedCycleWindow where
  cycleRoots : ℕ
  rotationWindow : ℕ
  cycleSlack : ℕ
  rootedOrbitBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedCycleWindow.rotationControlled (w : RootedCycleWindow) : Prop :=
  w.rotationWindow ≤ w.cycleRoots + w.cycleSlack + w.slack

def RootedCycleWindow.orbitControlled (w : RootedCycleWindow) : Prop :=
  w.rootedOrbitBudget ≤ w.cycleRoots + w.rotationWindow + w.cycleSlack + w.slack

def rootedCycleWindowReady (w : RootedCycleWindow) : Prop :=
  0 < w.cycleRoots ∧
    w.rotationControlled ∧
    w.orbitControlled

def RootedCycleWindow.certificate (w : RootedCycleWindow) : ℕ :=
  w.cycleRoots + w.rotationWindow + w.cycleSlack + w.slack

theorem rootedCycle_orbitBudget_le_certificate {w : RootedCycleWindow}
    (h : rootedCycleWindowReady w) :
    w.rootedOrbitBudget ≤ w.certificate := by
  rcases h with ⟨_, _, horbit⟩
  exact horbit

def sampleRootedCycleWindow : RootedCycleWindow :=
  { cycleRoots := 7, rotationWindow := 9, cycleSlack := 3, rootedOrbitBudget := 18, slack := 0 }

example : rootedCycleWindowReady sampleRootedCycleWindow := by
  norm_num [rootedCycleWindowReady, RootedCycleWindow.rotationControlled,
    RootedCycleWindow.orbitControlled, sampleRootedCycleWindow]

example : sampleRootedCycleWindow.certificate = 19 := by
  native_decide


structure FiniteRootedCycleModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRootedCycleModelsBudgetCertificate.controlled
    (c : FiniteRootedCycleModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRootedCycleModelsBudgetCertificate.budgetControlled
    (c : FiniteRootedCycleModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRootedCycleModelsBudgetCertificate.Ready
    (c : FiniteRootedCycleModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRootedCycleModelsBudgetCertificate.size
    (c : FiniteRootedCycleModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRootedCycleModels_budgetCertificate_le_size
    (c : FiniteRootedCycleModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRootedCycleModelsBudgetCertificate :
    FiniteRootedCycleModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRootedCycleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.controlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRootedCycleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedCycleModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRootedCycleModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.controlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]

example :
    sampleFiniteRootedCycleModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedCycleModelsBudgetCertificate.size := by
  apply finiteRootedCycleModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.controlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]
  · norm_num [FiniteRootedCycleModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedCycleModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRootedCycleModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRootedCycleModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRootedCycleModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRootedCycleModels
