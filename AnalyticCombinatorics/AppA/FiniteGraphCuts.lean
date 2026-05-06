import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite graph-cut bookkeeping.

Edges are represented as pairs of natural labels.  The definitions here are
small executable helpers for cut-size and boundary-count examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteGraphCuts

def crossesCut (left : List ℕ) (edge : ℕ × ℕ) : Bool :=
  (left.any (fun x => x == edge.1)) != (left.any (fun x => x == edge.2))

def cutSize (left : List ℕ) (edges : List (ℕ × ℕ)) : ℕ :=
  edges.filter (crossesCut left) |>.length

def internalEdgeCount (left : List ℕ) (edges : List (ℕ × ℕ)) : ℕ :=
  edges.filter (fun e => left.any (fun x => x == e.1) && left.any (fun x => x == e.2)) |>.length

theorem cutSize_nil (left : List ℕ) :
    cutSize left [] = 0 := by
  rfl

theorem internalEdgeCount_nil (left : List ℕ) :
    internalEdgeCount left [] = 0 := by
  rfl

def sampleEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (0, 2)]

example : crossesCut [0, 1] (1, 2) = true := by
  native_decide

example : cutSize [0, 1] sampleEdges = 2 := by
  native_decide

example : internalEdgeCount [0, 1, 2] sampleEdges = 3 := by
  native_decide

structure GraphCutWindow where
  vertices : ℕ
  leftSize : ℕ
  rightSize : ℕ
  crossingEdges : ℕ
  edgeSlack : ℕ
deriving DecidableEq, Repr

def GraphCutWindow.partitionReady (w : GraphCutWindow) : Prop :=
  w.leftSize + w.rightSize = w.vertices

def GraphCutWindow.crossingControlled (w : GraphCutWindow) : Prop :=
  w.crossingEdges ≤ w.leftSize * w.rightSize + w.edgeSlack

def GraphCutWindow.ready (w : GraphCutWindow) : Prop :=
  w.partitionReady ∧ w.crossingControlled

def GraphCutWindow.certificate (w : GraphCutWindow) : ℕ :=
  w.vertices + w.leftSize + w.rightSize + w.crossingEdges + w.edgeSlack

theorem crossingEdges_le_certificate (w : GraphCutWindow) :
    w.crossingEdges ≤ w.certificate := by
  unfold GraphCutWindow.certificate
  omega

def sampleGraphCutWindow : GraphCutWindow :=
  { vertices := 5, leftSize := 2, rightSize := 3, crossingEdges := 4, edgeSlack := 0 }

example : sampleGraphCutWindow.ready := by
  norm_num [sampleGraphCutWindow, GraphCutWindow.ready, GraphCutWindow.partitionReady,
    GraphCutWindow.crossingControlled]


structure FiniteGraphCutsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteGraphCutsBudgetCertificate.controlled
    (c : FiniteGraphCutsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteGraphCutsBudgetCertificate.budgetControlled
    (c : FiniteGraphCutsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteGraphCutsBudgetCertificate.Ready
    (c : FiniteGraphCutsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteGraphCutsBudgetCertificate.size
    (c : FiniteGraphCutsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteGraphCuts_budgetCertificate_le_size
    (c : FiniteGraphCutsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteGraphCutsBudgetCertificate :
    FiniteGraphCutsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteGraphCutsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGraphCutsBudgetCertificate.controlled,
      sampleFiniteGraphCutsBudgetCertificate]
  · norm_num [FiniteGraphCutsBudgetCertificate.budgetControlled,
      sampleFiniteGraphCutsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteGraphCutsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGraphCutsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteGraphCutsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteGraphCutsBudgetCertificate.controlled,
      sampleFiniteGraphCutsBudgetCertificate]
  · norm_num [FiniteGraphCutsBudgetCertificate.budgetControlled,
      sampleFiniteGraphCutsBudgetCertificate]

example :
    sampleFiniteGraphCutsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteGraphCutsBudgetCertificate.size := by
  apply finiteGraphCuts_budgetCertificate_le_size
  constructor
  · norm_num [FiniteGraphCutsBudgetCertificate.controlled,
      sampleFiniteGraphCutsBudgetCertificate]
  · norm_num [FiniteGraphCutsBudgetCertificate.budgetControlled,
      sampleFiniteGraphCutsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteGraphCutsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteGraphCutsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteGraphCutsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteGraphCuts
