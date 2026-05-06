import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rooted tree window models.

This module records finite bookkeeping for rooted tree windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteRootedTreeWindowModels

structure RootedTreeWindowData where
  treeRoots : ℕ
  branchWindow : ℕ
  treeSlack : ℕ
deriving DecidableEq, Repr

def hasTreeRoots (d : RootedTreeWindowData) : Prop :=
  0 < d.treeRoots

def branchWindowControlled (d : RootedTreeWindowData) : Prop :=
  d.branchWindow ≤ d.treeRoots + d.treeSlack

def rootedTreeReady (d : RootedTreeWindowData) : Prop :=
  hasTreeRoots d ∧ branchWindowControlled d

def rootedTreeBudget (d : RootedTreeWindowData) : ℕ :=
  d.treeRoots + d.branchWindow + d.treeSlack

theorem rootedTreeReady.hasTreeRoots {d : RootedTreeWindowData}
    (h : rootedTreeReady d) :
    hasTreeRoots d ∧ branchWindowControlled d ∧ d.branchWindow ≤ rootedTreeBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold rootedTreeBudget
  omega

theorem branchWindow_le_budget (d : RootedTreeWindowData) :
    d.branchWindow ≤ rootedTreeBudget d := by
  unfold rootedTreeBudget
  omega

def sampleRootedTreeWindowData : RootedTreeWindowData :=
  { treeRoots := 7, branchWindow := 9, treeSlack := 3 }

example : rootedTreeReady sampleRootedTreeWindowData := by
  norm_num [rootedTreeReady, hasTreeRoots]
  norm_num [branchWindowControlled, sampleRootedTreeWindowData]

example : rootedTreeBudget sampleRootedTreeWindowData = 19 := by
  native_decide

structure RootedTreeCertificateWindow where
  treeRoots : ℕ
  branchWindow : ℕ
  treeSlack : ℕ
  fringeBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedTreeCertificateWindow.branchControlled (w : RootedTreeCertificateWindow) : Prop :=
  w.branchWindow ≤ w.treeRoots + w.treeSlack + w.slack

def RootedTreeCertificateWindow.fringeControlled (w : RootedTreeCertificateWindow) : Prop :=
  w.fringeBudget ≤ w.treeRoots + w.branchWindow + w.treeSlack + w.slack

def rootedTreeWindowReady (w : RootedTreeCertificateWindow) : Prop :=
  0 < w.treeRoots ∧
    w.branchControlled ∧
    w.fringeControlled

def RootedTreeCertificateWindow.certificate (w : RootedTreeCertificateWindow) : ℕ :=
  w.treeRoots + w.branchWindow + w.treeSlack + w.slack

theorem rootedTree_fringeBudget_le_certificate {w : RootedTreeCertificateWindow}
    (h : rootedTreeWindowReady w) :
    w.fringeBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hfringe⟩
  exact hfringe

def sampleRootedTreeCertificateWindow : RootedTreeCertificateWindow :=
  { treeRoots := 7, branchWindow := 9, treeSlack := 3, fringeBudget := 18, slack := 0 }

example : rootedTreeWindowReady sampleRootedTreeCertificateWindow := by
  norm_num [rootedTreeWindowReady, RootedTreeCertificateWindow.branchControlled,
    RootedTreeCertificateWindow.fringeControlled, sampleRootedTreeCertificateWindow]

example : sampleRootedTreeCertificateWindow.certificate = 19 := by
  native_decide


structure FiniteRootedTreeWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRootedTreeWindowModelsBudgetCertificate.controlled
    (c : FiniteRootedTreeWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRootedTreeWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteRootedTreeWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRootedTreeWindowModelsBudgetCertificate.Ready
    (c : FiniteRootedTreeWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRootedTreeWindowModelsBudgetCertificate.size
    (c : FiniteRootedTreeWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRootedTreeWindowModels_budgetCertificate_le_size
    (c : FiniteRootedTreeWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRootedTreeWindowModelsBudgetCertificate :
    FiniteRootedTreeWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRootedTreeWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.controlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRootedTreeWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedTreeWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRootedTreeWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.controlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]

example :
    sampleFiniteRootedTreeWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedTreeWindowModelsBudgetCertificate.size := by
  apply finiteRootedTreeWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.controlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]
  · norm_num [FiniteRootedTreeWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedTreeWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRootedTreeWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRootedTreeWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRootedTreeWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRootedTreeWindowModels
