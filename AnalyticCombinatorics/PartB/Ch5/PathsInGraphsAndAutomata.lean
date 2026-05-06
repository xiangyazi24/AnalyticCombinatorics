import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Paths in graphs and automata.

Finite state-window bookkeeping for path enumeration by adjacency data.
-/

namespace AnalyticCombinatorics.PartB.Ch5.PathsInGraphsAndAutomata

/-- Edge predicate for the two-state automaton avoiding consecutive ones. -/
def noConsecutiveOnesEdge (src dst : Fin 2) : Bool :=
  !(src.val = 1 && dst.val = 1)

/-- Count one-step paths from a state in a two-state automaton. -/
def oneStepPathCount2 (edge : Fin 2 → Fin 2 → Bool) (src : Fin 2) : ℕ :=
  (List.finRange 2).foldl
    (fun total dst => if edge src dst then total + 1 else total) 0

/-- Finite path-degree audit for a two-state automaton. -/
def pathDegreeBoundCheck (edge : Fin 2 → Fin 2 → Bool) (bound : ℕ) : Bool :=
  (List.finRange 2).all fun src => oneStepPathCount2 edge src ≤ bound

theorem noConsecutiveOnes_pathDegreeBound :
    pathDegreeBoundCheck noConsecutiveOnesEdge 2 = true := by
  unfold pathDegreeBoundCheck oneStepPathCount2 noConsecutiveOnesEdge
  native_decide

/-- Total one-step path count in the two-state automaton. -/
def totalOneStepPathCount2 (edge : Fin 2 → Fin 2 → Bool) : ℕ :=
  (List.finRange 2).foldl (fun total src => total + oneStepPathCount2 edge src) 0

theorem noConsecutiveOnes_totalOneStepPaths :
    totalOneStepPathCount2 noConsecutiveOnesEdge = 3 := by
  unfold totalOneStepPathCount2 oneStepPathCount2 noConsecutiveOnesEdge
  native_decide

structure GraphAutomataPathWindow where
  vertexCount : ℕ
  edgeCount : ℕ
  pathLengthDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def graphAutomataPathReady (w : GraphAutomataPathWindow) : Prop :=
  0 < w.vertexCount ∧
    w.pathLengthDepth ≤ w.vertexCount + w.edgeCount + w.slack

def graphAutomataPathBudget (w : GraphAutomataPathWindow) : ℕ :=
  w.vertexCount + w.edgeCount + w.pathLengthDepth + w.slack

theorem pathLengthDepth_le_graphAutomataPathBudget
    (w : GraphAutomataPathWindow) :
    w.pathLengthDepth ≤ graphAutomataPathBudget w := by
  unfold graphAutomataPathBudget
  omega

def sampleGraphAutomataPathWindow : GraphAutomataPathWindow :=
  { vertexCount := 5, edgeCount := 8, pathLengthDepth := 10, slack := 1 }

example : graphAutomataPathReady sampleGraphAutomataPathWindow := by
  norm_num [graphAutomataPathReady, sampleGraphAutomataPathWindow]

structure PathsInGraphsAndAutomataBudgetCertificate where
  vertexWindow : ℕ
  edgeWindow : ℕ
  pathWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PathsInGraphsAndAutomataBudgetCertificate.controlled
    (c : PathsInGraphsAndAutomataBudgetCertificate) : Prop :=
  0 < c.vertexWindow ∧ c.pathWindow ≤ c.vertexWindow + c.edgeWindow + c.slack

def PathsInGraphsAndAutomataBudgetCertificate.budgetControlled
    (c : PathsInGraphsAndAutomataBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.vertexWindow + c.edgeWindow + c.pathWindow + c.slack

def PathsInGraphsAndAutomataBudgetCertificate.Ready
    (c : PathsInGraphsAndAutomataBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PathsInGraphsAndAutomataBudgetCertificate.size
    (c : PathsInGraphsAndAutomataBudgetCertificate) : ℕ :=
  c.vertexWindow + c.edgeWindow + c.pathWindow + c.slack

theorem pathsInGraphsAndAutomata_budgetCertificate_le_size
    (c : PathsInGraphsAndAutomataBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePathsInGraphsAndAutomataBudgetCertificate :
    PathsInGraphsAndAutomataBudgetCertificate :=
  { vertexWindow := 5
    edgeWindow := 8
    pathWindow := 10
    certificateBudgetWindow := 24
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePathsInGraphsAndAutomataBudgetCertificate.Ready := by
  constructor
  · norm_num [PathsInGraphsAndAutomataBudgetCertificate.controlled,
      samplePathsInGraphsAndAutomataBudgetCertificate]
  · norm_num [PathsInGraphsAndAutomataBudgetCertificate.budgetControlled,
      samplePathsInGraphsAndAutomataBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePathsInGraphsAndAutomataBudgetCertificate.certificateBudgetWindow ≤
      samplePathsInGraphsAndAutomataBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePathsInGraphsAndAutomataBudgetCertificate.Ready := by
  constructor
  · norm_num [PathsInGraphsAndAutomataBudgetCertificate.controlled,
      samplePathsInGraphsAndAutomataBudgetCertificate]
  · norm_num [PathsInGraphsAndAutomataBudgetCertificate.budgetControlled,
      samplePathsInGraphsAndAutomataBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List PathsInGraphsAndAutomataBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [samplePathsInGraphsAndAutomataBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePathsInGraphsAndAutomataBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.PathsInGraphsAndAutomata
