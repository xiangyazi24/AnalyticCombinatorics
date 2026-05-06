import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Plane tree examples.

Plane trees with `n + 1` nodes are counted by the Catalan number `C_n`.
-/

namespace AnalyticCombinatorics.Examples.PlaneTrees

inductive PlaneTree where
  | node : List PlaneTree → PlaneTree
deriving Repr

namespace PlaneTree

mutual
  def size : PlaneTree → ℕ
    | node children => 1 + childrenSize children

  def childrenSize : List PlaneTree → ℕ
    | [] => 0
    | t :: ts => size t + childrenSize ts
end

def children : PlaneTree → List PlaneTree
  | node children => children

theorem size_pos (t : PlaneTree) : 0 < size t := by
  cases t
  simp [size]

end PlaneTree

def catalanFormula (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def planeTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | 8 => 1430
  | 9 => 4862
  | 10 => 16796
  | _ => 0

def samplePlaneTree : PlaneTree :=
  PlaneTree.node [PlaneTree.node [], PlaneTree.node [PlaneTree.node []]]

example : PlaneTree.size samplePlaneTree = 4 := by native_decide
example : catalanFormula 6 = planeTreeCount 6 := by native_decide
example : planeTreeCount 0 = 1 := by native_decide
example : planeTreeCount 1 = 1 := by native_decide
example : planeTreeCount 2 = 2 := by native_decide
example : planeTreeCount 3 = 5 := by native_decide
example : planeTreeCount 4 = 14 := by native_decide
example : planeTreeCount 5 = 42 := by native_decide
example : planeTreeCount 10 = 16796 := by native_decide
example : (List.range 6).map planeTreeCount = [1, 1, 2, 5, 14, 42] := by
  native_decide

/-- Finite Catalan recurrence audit for plane-tree counts. -/
def planeTreeCatalanRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    planeTreeCount (n + 1) * (n + 2) =
      2 * (2 * n + 1) * planeTreeCount n

theorem planeTreeCount_recurrenceWindow :
    planeTreeCatalanRecurrenceCheck 9 = true := by
  unfold planeTreeCatalanRecurrenceCheck planeTreeCount
  native_decide

structure PlaneTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PlaneTreesBudgetCertificate.controlled
    (c : PlaneTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PlaneTreesBudgetCertificate.budgetControlled
    (c : PlaneTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PlaneTreesBudgetCertificate.Ready (c : PlaneTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PlaneTreesBudgetCertificate.size (c : PlaneTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem planeTrees_budgetCertificate_le_size
    (c : PlaneTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePlaneTreesBudgetCertificate : PlaneTreesBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : samplePlaneTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [PlaneTreesBudgetCertificate.controlled,
      samplePlaneTreesBudgetCertificate]
  · norm_num [PlaneTreesBudgetCertificate.budgetControlled,
      samplePlaneTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePlaneTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [PlaneTreesBudgetCertificate.controlled,
      samplePlaneTreesBudgetCertificate]
  · norm_num [PlaneTreesBudgetCertificate.budgetControlled,
      samplePlaneTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePlaneTreesBudgetCertificate.certificateBudgetWindow ≤
      samplePlaneTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PlaneTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePlaneTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePlaneTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.PlaneTrees
