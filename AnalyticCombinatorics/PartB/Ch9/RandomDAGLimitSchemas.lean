import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random DAG limit schema bookkeeping.

The finite record stores vertex count, edge budget, and acyclicity witness
budget for random DAG asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomDAGLimitSchemas

structure RandomDAGData where
  vertexCount : ℕ
  edgeBudget : ℕ
  acyclicityBudget : ℕ
deriving DecidableEq, Repr

def nonemptyDAG (d : RandomDAGData) : Prop :=
  0 < d.vertexCount

def edgeBudgetControlled (d : RandomDAGData) : Prop :=
  d.edgeBudget ≤ d.vertexCount * d.vertexCount

def randomDAGReady (d : RandomDAGData) : Prop :=
  nonemptyDAG d ∧ edgeBudgetControlled d

def dagBudget (d : RandomDAGData) : ℕ :=
  d.vertexCount + d.edgeBudget + d.acyclicityBudget

theorem randomDAGReady.nonempty {d : RandomDAGData}
    (h : randomDAGReady d) :
    nonemptyDAG d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem vertexCount_le_dagBudget (d : RandomDAGData) :
    d.vertexCount ≤ dagBudget d := by
  unfold dagBudget
  omega

def sampleDAG : RandomDAGData :=
  { vertexCount := 5, edgeBudget := 12, acyclicityBudget := 4 }

example : randomDAGReady sampleDAG := by
  norm_num [randomDAGReady, nonemptyDAG, edgeBudgetControlled, sampleDAG]

example : dagBudget sampleDAG = 21 := by
  native_decide

/-- Finite executable readiness audit for random DAG limit data. -/
def randomDAGDataListReady (data : List RandomDAGData) : Bool :=
  data.all fun d =>
    0 < d.vertexCount && d.edgeBudget ≤ d.vertexCount * d.vertexCount

theorem randomDAGDataList_readyWindow :
    randomDAGDataListReady
      [{ vertexCount := 3, edgeBudget := 6, acyclicityBudget := 2 },
       { vertexCount := 5, edgeBudget := 12, acyclicityBudget := 4 }] = true := by
  unfold randomDAGDataListReady
  native_decide

structure RandomDAGWindow where
  vertexCount : ℕ
  edgeBudget : ℕ
  acyclicityBudget : ℕ
  topologicalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomDAGWindow.edgeControlled (w : RandomDAGWindow) : Prop :=
  w.edgeBudget ≤ w.vertexCount * w.vertexCount

def RandomDAGWindow.topologicalControlled (w : RandomDAGWindow) : Prop :=
  w.topologicalBudget ≤ w.edgeBudget + w.acyclicityBudget + w.slack

def randomDAGWindowReady (w : RandomDAGWindow) : Prop :=
  0 < w.vertexCount ∧
    w.edgeControlled ∧
    w.topologicalControlled

def RandomDAGWindow.certificate (w : RandomDAGWindow) : ℕ :=
  w.edgeBudget + w.acyclicityBudget + w.slack

theorem randomDAG_topologicalBudget_le_certificate {w : RandomDAGWindow}
    (h : randomDAGWindowReady w) :
    w.topologicalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htop⟩
  exact htop

def sampleRandomDAGWindow : RandomDAGWindow :=
  { vertexCount := 5, edgeBudget := 12, acyclicityBudget := 4, topologicalBudget := 15,
    slack := 0 }

example : randomDAGWindowReady sampleRandomDAGWindow := by
  norm_num [randomDAGWindowReady, RandomDAGWindow.edgeControlled,
    RandomDAGWindow.topologicalControlled, sampleRandomDAGWindow]

example : sampleRandomDAGWindow.certificate = 16 := by
  native_decide


structure RandomDAGLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomDAGLimitSchemasBudgetCertificate.controlled
    (c : RandomDAGLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomDAGLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomDAGLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomDAGLimitSchemasBudgetCertificate.Ready
    (c : RandomDAGLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomDAGLimitSchemasBudgetCertificate.size
    (c : RandomDAGLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomDAGLimitSchemas_budgetCertificate_le_size
    (c : RandomDAGLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomDAGLimitSchemasBudgetCertificate :
    RandomDAGLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomDAGLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.controlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]

example :
    sampleRandomDAGLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomDAGLimitSchemasBudgetCertificate.size := by
  apply randomDAGLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.controlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomDAGLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.controlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]
  · norm_num [RandomDAGLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomDAGLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomDAGLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomDAGLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomDAGLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomDAGLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomDAGLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomDAGLimitSchemas
