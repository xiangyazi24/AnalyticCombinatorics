import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Plane tree count table.

A plane tree is a rooted tree whose children are ordered.  This self-contained
model keeps the size and child-list bookkeeping used by the symbolic equation
`T = Z * SEQ(T)`.
-/

namespace AnalyticCombinatorics.PartA.Ch1.PlaneTrees

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

theorem childrenSize_append (left right : List PlaneTree) :
    childrenSize (left ++ right) = childrenSize left + childrenSize right := by
  induction left with
  | nil =>
      simp [childrenSize]
  | cons t ts ih =>
      simp [childrenSize, ih, Nat.add_assoc]

theorem child_size_le_childrenSize {children : List PlaneTree} {t : PlaneTree}
    (h : t ∈ children) :
    size t ≤ childrenSize children := by
  induction children with
  | nil =>
      simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      rcases h with hhead | htail
      · subst head
        simp only [childrenSize]
        omega
      · have hle := ih htail
        simp only [childrenSize]
        omega

end PlaneTree

structure PlaneTreeWindow where
  nodeCount : ℕ
  orderedChildSlots : ℕ
  planeSlack : ℕ
deriving DecidableEq, Repr

def nonemptyPlaneTreeWindow (w : PlaneTreeWindow) : Prop :=
  0 < w.nodeCount

def orderedChildSlotsControlled (w : PlaneTreeWindow) : Prop :=
  w.orderedChildSlots ≤ w.nodeCount + w.planeSlack

def planeTreeWindowReady (w : PlaneTreeWindow) : Prop :=
  nonemptyPlaneTreeWindow w ∧ orderedChildSlotsControlled w

def planeTreeWindowBudget (w : PlaneTreeWindow) : ℕ :=
  w.nodeCount + w.orderedChildSlots + w.planeSlack

theorem planeTreeWindowReady.certificate {w : PlaneTreeWindow}
    (h : planeTreeWindowReady w) :
    nonemptyPlaneTreeWindow w ∧ orderedChildSlotsControlled w ∧
      w.orderedChildSlots ≤ planeTreeWindowBudget w := by
  rcases h with ⟨hnodes, hcontrolled⟩
  refine ⟨hnodes, hcontrolled, ?_⟩
  unfold planeTreeWindowBudget
  omega

theorem nodeCount_le_budget (w : PlaneTreeWindow) :
    w.nodeCount ≤ planeTreeWindowBudget w := by
  unfold planeTreeWindowBudget
  omega

def samplePlaneTree : PlaneTree :=
  PlaneTree.node [PlaneTree.node [], PlaneTree.node [PlaneTree.node []]]

def planeTreeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | _ => 0

def samplePlaneTreeWindow : PlaneTreeWindow :=
  { nodeCount := 6, orderedChildSlots := 8, planeSlack := 2 }

example : planeTreeWindowReady samplePlaneTreeWindow := by
  norm_num [planeTreeWindowReady, nonemptyPlaneTreeWindow]
  norm_num [orderedChildSlotsControlled, samplePlaneTreeWindow]

example : planeTreeCount 6 = 132 := by native_decide
example : planeTreeWindowBudget samplePlaneTreeWindow = 16 := by native_decide
example : PlaneTree.size samplePlaneTree = 4 := by native_decide
example : PlaneTree.childrenSize (PlaneTree.children samplePlaneTree) = 3 := by native_decide
example : planeTreeCount 5 = 42 := by native_decide


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

def PlaneTreesBudgetCertificate.Ready
    (c : PlaneTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PlaneTreesBudgetCertificate.size
    (c : PlaneTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem planeTrees_budgetCertificate_le_size
    (c : PlaneTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePlaneTreesBudgetCertificate :
    PlaneTreesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePlaneTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [PlaneTreesBudgetCertificate.controlled,
      samplePlaneTreesBudgetCertificate]
  · norm_num [PlaneTreesBudgetCertificate.budgetControlled,
      samplePlaneTreesBudgetCertificate]

example :
    samplePlaneTreesBudgetCertificate.certificateBudgetWindow ≤
      samplePlaneTreesBudgetCertificate.size := by
  apply planeTrees_budgetCertificate_le_size
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

end AnalyticCombinatorics.PartA.Ch1.PlaneTrees
