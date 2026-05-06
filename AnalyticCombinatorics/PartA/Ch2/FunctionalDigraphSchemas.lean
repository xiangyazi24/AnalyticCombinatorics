import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Functional digraph schemas.

The finite record stores node count, cycle budget, and tree slack.
-/

namespace AnalyticCombinatorics.PartA.Ch2.FunctionalDigraphSchemas

structure FunctionalDigraphData where
  nodeCount : ℕ
  cycleBudget : ℕ
  treeSlack : ℕ
deriving DecidableEq, Repr

def nodeCountPositive (d : FunctionalDigraphData) : Prop :=
  0 < d.nodeCount

def cycleBudgetControlled (d : FunctionalDigraphData) : Prop :=
  d.cycleBudget ≤ d.nodeCount + d.treeSlack

def functionalDigraphReady (d : FunctionalDigraphData) : Prop :=
  nodeCountPositive d ∧ cycleBudgetControlled d

def functionalDigraphBudget (d : FunctionalDigraphData) : ℕ :=
  d.nodeCount + d.cycleBudget + d.treeSlack

theorem functionalDigraphReady.nodes {d : FunctionalDigraphData}
    (h : functionalDigraphReady d) :
    nodeCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem cycleBudget_le_functionalDigraphBudget
    (d : FunctionalDigraphData) :
    d.cycleBudget ≤ functionalDigraphBudget d := by
  unfold functionalDigraphBudget
  omega

def sampleFunctionalDigraphData : FunctionalDigraphData :=
  { nodeCount := 7, cycleBudget := 9, treeSlack := 3 }

example : functionalDigraphReady sampleFunctionalDigraphData := by
  norm_num [functionalDigraphReady, nodeCountPositive]
  norm_num [cycleBudgetControlled, sampleFunctionalDigraphData]

example : functionalDigraphBudget sampleFunctionalDigraphData = 19 := by
  native_decide

structure FunctionalDigraphWindow where
  nodeCount : ℕ
  cycleBudget : ℕ
  treeSlack : ℕ
  forestBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionalDigraphWindow.cycleControlled (w : FunctionalDigraphWindow) : Prop :=
  w.cycleBudget ≤ w.nodeCount + w.treeSlack + w.slack

def FunctionalDigraphWindow.forestControlled (w : FunctionalDigraphWindow) : Prop :=
  w.forestBudget ≤ w.nodeCount + w.cycleBudget + w.treeSlack + w.slack

def functionalDigraphWindowReady (w : FunctionalDigraphWindow) : Prop :=
  0 < w.nodeCount ∧
    w.cycleControlled ∧
    w.forestControlled

def FunctionalDigraphWindow.certificate (w : FunctionalDigraphWindow) : ℕ :=
  w.nodeCount + w.cycleBudget + w.treeSlack + w.slack

theorem functionalDigraph_forestBudget_le_certificate {w : FunctionalDigraphWindow}
    (h : functionalDigraphWindowReady w) :
    w.forestBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hforest⟩
  exact hforest

def sampleFunctionalDigraphWindow : FunctionalDigraphWindow :=
  { nodeCount := 7, cycleBudget := 9, treeSlack := 3, forestBudget := 18, slack := 0 }

example : functionalDigraphWindowReady sampleFunctionalDigraphWindow := by
  norm_num [functionalDigraphWindowReady, FunctionalDigraphWindow.cycleControlled,
    FunctionalDigraphWindow.forestControlled, sampleFunctionalDigraphWindow]

example : sampleFunctionalDigraphWindow.certificate = 19 := by
  native_decide


structure FunctionalDigraphSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FunctionalDigraphSchemasBudgetCertificate.controlled
    (c : FunctionalDigraphSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FunctionalDigraphSchemasBudgetCertificate.budgetControlled
    (c : FunctionalDigraphSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FunctionalDigraphSchemasBudgetCertificate.Ready
    (c : FunctionalDigraphSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FunctionalDigraphSchemasBudgetCertificate.size
    (c : FunctionalDigraphSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem functionalDigraphSchemas_budgetCertificate_le_size
    (c : FunctionalDigraphSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFunctionalDigraphSchemasBudgetCertificate :
    FunctionalDigraphSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFunctionalDigraphSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.controlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.budgetControlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFunctionalDigraphSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionalDigraphSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFunctionalDigraphSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.controlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.budgetControlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]

example :
    sampleFunctionalDigraphSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleFunctionalDigraphSchemasBudgetCertificate.size := by
  apply functionalDigraphSchemas_budgetCertificate_le_size
  constructor
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.controlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]
  · norm_num [FunctionalDigraphSchemasBudgetCertificate.budgetControlled,
      sampleFunctionalDigraphSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FunctionalDigraphSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFunctionalDigraphSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFunctionalDigraphSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.FunctionalDigraphSchemas
