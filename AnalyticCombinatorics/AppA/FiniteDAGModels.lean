import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite DAG models.

The finite schema tracks vertices, directed edges, and a rank budget for
acyclic dependency graphs.
-/

namespace AnalyticCombinatorics.AppA.FiniteDAGModels

structure DAGData where
  vertices : ℕ
  directedEdges : ℕ
  rankBudget : ℕ
deriving DecidableEq, Repr

def dagVerticesNonempty (d : DAGData) : Prop :=
  0 < d.vertices

def directedEdgesControlled (d : DAGData) : Prop :=
  d.directedEdges ≤ d.vertices + d.rankBudget

def dagReady (d : DAGData) : Prop :=
  dagVerticesNonempty d ∧ directedEdgesControlled d

def dagBudget (d : DAGData) : ℕ :=
  d.vertices + d.directedEdges + d.rankBudget

theorem dagReady.vertices {d : DAGData} (h : dagReady d) :
    dagVerticesNonempty d ∧ directedEdgesControlled d ∧ d.directedEdges ≤ dagBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold dagBudget
  omega

theorem directedEdges_le_dagBudget (d : DAGData) :
    d.directedEdges ≤ dagBudget d := by
  unfold dagBudget
  omega

def sampleDAGData : DAGData :=
  { vertices := 8, directedEdges := 10, rankBudget := 3 }

example : dagReady sampleDAGData := by
  norm_num [dagReady, dagVerticesNonempty]
  norm_num [directedEdgesControlled, sampleDAGData]

example : dagBudget sampleDAGData = 21 := by
  native_decide

structure DAGWindow where
  vertices : ℕ
  directedEdges : ℕ
  rankBudget : ℕ
  topologicalBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DAGWindow.edgesControlled (w : DAGWindow) : Prop :=
  w.directedEdges ≤ w.vertices + w.rankBudget + w.slack

def DAGWindow.topologicalControlled (w : DAGWindow) : Prop :=
  w.topologicalBudget ≤ w.vertices + w.directedEdges + w.rankBudget + w.slack

def dagWindowReady (w : DAGWindow) : Prop :=
  0 < w.vertices ∧
    w.edgesControlled ∧
    w.topologicalControlled

def DAGWindow.certificate (w : DAGWindow) : ℕ :=
  w.vertices + w.directedEdges + w.rankBudget + w.slack

theorem dag_topologicalBudget_le_certificate {w : DAGWindow}
    (h : dagWindowReady w) :
    w.topologicalBudget ≤ w.certificate := by
  rcases h with ⟨_, _, htop⟩
  exact htop

def sampleDAGWindow : DAGWindow :=
  { vertices := 8, directedEdges := 10, rankBudget := 3, topologicalBudget := 19, slack := 0 }

example : dagWindowReady sampleDAGWindow := by
  norm_num [dagWindowReady, DAGWindow.edgesControlled, DAGWindow.topologicalControlled,
    sampleDAGWindow]

example : sampleDAGWindow.certificate = 21 := by
  native_decide


structure FiniteDAGModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteDAGModelsBudgetCertificate.controlled
    (c : FiniteDAGModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteDAGModelsBudgetCertificate.budgetControlled
    (c : FiniteDAGModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteDAGModelsBudgetCertificate.Ready
    (c : FiniteDAGModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteDAGModelsBudgetCertificate.size
    (c : FiniteDAGModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteDAGModels_budgetCertificate_le_size
    (c : FiniteDAGModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteDAGModelsBudgetCertificate :
    FiniteDAGModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteDAGModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDAGModelsBudgetCertificate.controlled,
      sampleFiniteDAGModelsBudgetCertificate]
  · norm_num [FiniteDAGModelsBudgetCertificate.budgetControlled,
      sampleFiniteDAGModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteDAGModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDAGModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteDAGModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteDAGModelsBudgetCertificate.controlled,
      sampleFiniteDAGModelsBudgetCertificate]
  · norm_num [FiniteDAGModelsBudgetCertificate.budgetControlled,
      sampleFiniteDAGModelsBudgetCertificate]

example :
    sampleFiniteDAGModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteDAGModelsBudgetCertificate.size := by
  apply finiteDAGModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteDAGModelsBudgetCertificate.controlled,
      sampleFiniteDAGModelsBudgetCertificate]
  · norm_num [FiniteDAGModelsBudgetCertificate.budgetControlled,
      sampleFiniteDAGModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteDAGModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteDAGModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteDAGModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteDAGModels
