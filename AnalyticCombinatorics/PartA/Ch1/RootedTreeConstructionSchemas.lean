import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Rooted tree construction schemas.

The finite schema records root choices, child slots, and recursion slack.
-/

namespace AnalyticCombinatorics.PartA.Ch1.RootedTreeConstructionSchemas

structure RootedTreeConstructionData where
  rootChoices : ℕ
  childSlots : ℕ
  recursionSlack : ℕ
deriving DecidableEq, Repr

def rootChoicesPositive (d : RootedTreeConstructionData) : Prop :=
  0 < d.rootChoices

def childSlotsControlled (d : RootedTreeConstructionData) : Prop :=
  d.childSlots ≤ d.rootChoices + d.recursionSlack

def rootedTreeConstructionReady
    (d : RootedTreeConstructionData) : Prop :=
  rootChoicesPositive d ∧ childSlotsControlled d

def rootedTreeConstructionBudget
    (d : RootedTreeConstructionData) : ℕ :=
  d.rootChoices + d.childSlots + d.recursionSlack

theorem rootedTreeConstructionReady.root
    {d : RootedTreeConstructionData}
    (h : rootedTreeConstructionReady d) :
    rootChoicesPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem childSlots_le_rootedTreeBudget
    (d : RootedTreeConstructionData) :
    d.childSlots ≤ rootedTreeConstructionBudget d := by
  unfold rootedTreeConstructionBudget
  omega

def sampleRootedTreeConstructionData : RootedTreeConstructionData :=
  { rootChoices := 5, childSlots := 7, recursionSlack := 3 }

example : rootedTreeConstructionReady sampleRootedTreeConstructionData := by
  norm_num [rootedTreeConstructionReady, rootChoicesPositive]
  norm_num [childSlotsControlled, sampleRootedTreeConstructionData]

example : rootedTreeConstructionBudget sampleRootedTreeConstructionData = 15 := by
  native_decide

structure RootedTreeConstructionBudgetCertificate where
  rootChoicesWindow : ℕ
  childSlotsWindow : ℕ
  recursionSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedTreeConstructionBudgetCertificate.controlled
    (c : RootedTreeConstructionBudgetCertificate) : Prop :=
  0 < c.rootChoicesWindow ∧
    c.childSlotsWindow ≤ c.rootChoicesWindow + c.recursionSlackWindow + c.slack

def RootedTreeConstructionBudgetCertificate.budgetControlled
    (c : RootedTreeConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rootChoicesWindow + c.childSlotsWindow + c.recursionSlackWindow + c.slack

def RootedTreeConstructionBudgetCertificate.Ready
    (c : RootedTreeConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RootedTreeConstructionBudgetCertificate.size
    (c : RootedTreeConstructionBudgetCertificate) : ℕ :=
  c.rootChoicesWindow + c.childSlotsWindow + c.recursionSlackWindow + c.slack

theorem rootedTreeConstruction_budgetCertificate_le_size
    (c : RootedTreeConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRootedTreeConstructionBudgetCertificate :
    RootedTreeConstructionBudgetCertificate :=
  { rootChoicesWindow := 5
    childSlotsWindow := 7
    recursionSlackWindow := 3
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRootedTreeConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedTreeConstructionBudgetCertificate.controlled,
      sampleRootedTreeConstructionBudgetCertificate]
  · norm_num [RootedTreeConstructionBudgetCertificate.budgetControlled,
      sampleRootedTreeConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRootedTreeConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedTreeConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRootedTreeConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [RootedTreeConstructionBudgetCertificate.controlled,
      sampleRootedTreeConstructionBudgetCertificate]
  · norm_num [RootedTreeConstructionBudgetCertificate.budgetControlled,
      sampleRootedTreeConstructionBudgetCertificate]

example :
    sampleRootedTreeConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleRootedTreeConstructionBudgetCertificate.size := by
  apply rootedTreeConstruction_budgetCertificate_le_size
  constructor
  · norm_num [RootedTreeConstructionBudgetCertificate.controlled,
      sampleRootedTreeConstructionBudgetCertificate]
  · norm_num [RootedTreeConstructionBudgetCertificate.budgetControlled,
      sampleRootedTreeConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RootedTreeConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRootedTreeConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRootedTreeConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.RootedTreeConstructionSchemas
