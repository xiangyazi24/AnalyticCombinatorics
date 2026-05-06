import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Rooted set construction schemas.

This module records finite bookkeeping for rooted set symbolic constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.RootedSetConstructionSchemas

structure RootedSetConstructionData where
  constructionRoots : ℕ
  setComponents : ℕ
  constructionSlack : ℕ
deriving DecidableEq, Repr

def hasConstructionRoots (d : RootedSetConstructionData) : Prop :=
  0 < d.constructionRoots

def setComponentsControlled (d : RootedSetConstructionData) : Prop :=
  d.setComponents ≤ d.constructionRoots + d.constructionSlack

def rootedSetConstructionReady (d : RootedSetConstructionData) : Prop :=
  hasConstructionRoots d ∧ setComponentsControlled d

def rootedSetConstructionBudget (d : RootedSetConstructionData) : ℕ :=
  d.constructionRoots + d.setComponents + d.constructionSlack

theorem rootedSetConstructionReady.hasConstructionRoots
    {d : RootedSetConstructionData}
    (h : rootedSetConstructionReady d) :
    hasConstructionRoots d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem setComponents_le_budget (d : RootedSetConstructionData) :
    d.setComponents ≤ rootedSetConstructionBudget d := by
  unfold rootedSetConstructionBudget
  omega

def sampleRootedSetConstructionData : RootedSetConstructionData :=
  { constructionRoots := 6, setComponents := 8, constructionSlack := 3 }

example : rootedSetConstructionReady sampleRootedSetConstructionData := by
  norm_num [rootedSetConstructionReady, hasConstructionRoots]
  norm_num [setComponentsControlled, sampleRootedSetConstructionData]

example : rootedSetConstructionBudget sampleRootedSetConstructionData = 17 := by
  native_decide

structure RootedSetConstructionBudgetCertificate where
  rootWindow : ℕ
  componentWindow : ℕ
  constructionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedSetConstructionBudgetCertificate.controlled
    (c : RootedSetConstructionBudgetCertificate) : Prop :=
  0 < c.rootWindow ∧
    c.componentWindow ≤ c.rootWindow + c.constructionSlackWindow + c.slack

def RootedSetConstructionBudgetCertificate.budgetControlled
    (c : RootedSetConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rootWindow + c.componentWindow + c.constructionSlackWindow + c.slack

def RootedSetConstructionBudgetCertificate.Ready
    (c : RootedSetConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RootedSetConstructionBudgetCertificate.size
    (c : RootedSetConstructionBudgetCertificate) : ℕ :=
  c.rootWindow + c.componentWindow + c.constructionSlackWindow + c.slack

theorem rootedSetConstruction_budgetCertificate_le_size
    (c : RootedSetConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRootedSetConstructionBudgetCertificate :
    RootedSetConstructionBudgetCertificate :=
  { rootWindow := 6
    componentWindow := 8
    constructionSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRootedSetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedSetConstructionBudgetCertificate.controlled,
      sampleRootedSetConstructionBudgetCertificate]
  · norm_num [RootedSetConstructionBudgetCertificate.budgetControlled,
      sampleRootedSetConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRootedSetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedSetConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRootedSetConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedSetConstructionBudgetCertificate.controlled,
      sampleRootedSetConstructionBudgetCertificate]
  · norm_num [RootedSetConstructionBudgetCertificate.budgetControlled,
      sampleRootedSetConstructionBudgetCertificate]

example :
    sampleRootedSetConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedSetConstructionBudgetCertificate.size := by
  apply rootedSetConstruction_budgetCertificate_le_size
  constructor
  · norm_num [RootedSetConstructionBudgetCertificate.controlled,
      sampleRootedSetConstructionBudgetCertificate]
  · norm_num [RootedSetConstructionBudgetCertificate.budgetControlled,
      sampleRootedSetConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RootedSetConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRootedSetConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRootedSetConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.RootedSetConstructionSchemas
