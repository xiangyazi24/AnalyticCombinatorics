import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Recursive tree schemas.

The finite schema records node budget, recursive calls, and guard slack.
-/

namespace AnalyticCombinatorics.PartA.Ch1.RecursiveTreeSchemas

structure RecursiveTreeData where
  nodeBudget : ℕ
  recursiveCalls : ℕ
  guardSlack : ℕ
deriving DecidableEq, Repr

def nodeBudgetPositive (d : RecursiveTreeData) : Prop :=
  0 < d.nodeBudget

def recursiveCallsControlled (d : RecursiveTreeData) : Prop :=
  d.recursiveCalls ≤ d.nodeBudget + d.guardSlack

def recursiveTreeReady (d : RecursiveTreeData) : Prop :=
  nodeBudgetPositive d ∧ recursiveCallsControlled d

def recursiveTreeBudget (d : RecursiveTreeData) : ℕ :=
  d.nodeBudget + d.recursiveCalls + d.guardSlack

theorem recursiveTreeReady.nodes {d : RecursiveTreeData}
    (h : recursiveTreeReady d) :
    nodeBudgetPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem recursiveCalls_le_recursiveTreeBudget (d : RecursiveTreeData) :
    d.recursiveCalls ≤ recursiveTreeBudget d := by
  unfold recursiveTreeBudget
  omega

def sampleRecursiveTreeData : RecursiveTreeData :=
  { nodeBudget := 7, recursiveCalls := 9, guardSlack := 3 }

example : recursiveTreeReady sampleRecursiveTreeData := by
  norm_num [recursiveTreeReady, nodeBudgetPositive]
  norm_num [recursiveCallsControlled, sampleRecursiveTreeData]

example : recursiveTreeBudget sampleRecursiveTreeData = 19 := by
  native_decide

structure RecursiveTreeWindow where
  nodeBudget : ℕ
  recursiveCalls : ℕ
  guardSlack : ℕ
  leafBudget : ℕ
deriving DecidableEq, Repr

def RecursiveTreeWindow.nodesReady (w : RecursiveTreeWindow) : Prop :=
  0 < w.nodeBudget

def RecursiveTreeWindow.callsControlled (w : RecursiveTreeWindow) : Prop :=
  w.recursiveCalls ≤ w.nodeBudget + w.guardSlack

def RecursiveTreeWindow.leavesControlled (w : RecursiveTreeWindow) : Prop :=
  w.leafBudget ≤ w.nodeBudget + w.guardSlack

def RecursiveTreeWindow.ready (w : RecursiveTreeWindow) : Prop :=
  w.nodesReady ∧ w.callsControlled ∧ w.leavesControlled

def RecursiveTreeWindow.certificate (w : RecursiveTreeWindow) : ℕ :=
  w.nodeBudget + w.recursiveCalls + w.guardSlack + w.leafBudget

theorem leafBudget_le_certificate (w : RecursiveTreeWindow) :
    w.leafBudget ≤ w.certificate := by
  unfold RecursiveTreeWindow.certificate
  omega

def sampleRecursiveTreeWindow : RecursiveTreeWindow :=
  { nodeBudget := 7, recursiveCalls := 9, guardSlack := 3, leafBudget := 4 }

example : sampleRecursiveTreeWindow.ready := by
  norm_num [sampleRecursiveTreeWindow, RecursiveTreeWindow.ready,
    RecursiveTreeWindow.nodesReady, RecursiveTreeWindow.callsControlled,
    RecursiveTreeWindow.leavesControlled]


structure RecursiveTreeSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecursiveTreeSchemasBudgetCertificate.controlled
    (c : RecursiveTreeSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecursiveTreeSchemasBudgetCertificate.budgetControlled
    (c : RecursiveTreeSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecursiveTreeSchemasBudgetCertificate.Ready
    (c : RecursiveTreeSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecursiveTreeSchemasBudgetCertificate.size
    (c : RecursiveTreeSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recursiveTreeSchemas_budgetCertificate_le_size
    (c : RecursiveTreeSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecursiveTreeSchemasBudgetCertificate :
    RecursiveTreeSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRecursiveTreeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveTreeSchemasBudgetCertificate.controlled,
      sampleRecursiveTreeSchemasBudgetCertificate]
  · norm_num [RecursiveTreeSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveTreeSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecursiveTreeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveTreeSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRecursiveTreeSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RecursiveTreeSchemasBudgetCertificate.controlled,
      sampleRecursiveTreeSchemasBudgetCertificate]
  · norm_num [RecursiveTreeSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveTreeSchemasBudgetCertificate]

example :
    sampleRecursiveTreeSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRecursiveTreeSchemasBudgetCertificate.size := by
  apply recursiveTreeSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RecursiveTreeSchemasBudgetCertificate.controlled,
      sampleRecursiveTreeSchemasBudgetCertificate]
  · norm_num [RecursiveTreeSchemasBudgetCertificate.budgetControlled,
      sampleRecursiveTreeSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RecursiveTreeSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecursiveTreeSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRecursiveTreeSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.RecursiveTreeSchemas
