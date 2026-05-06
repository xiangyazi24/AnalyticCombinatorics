import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite relations used in combinatorial specifications.

The file provides small relation predicates and closure checks without
depending on graph-theoretic project modules.
-/

namespace AnalyticCombinatorics.AppA.FiniteRelations

def relates (edges : List (ℕ × ℕ)) (a b : ℕ) : Bool :=
  edges.any (fun e => e.1 == a && e.2 == b)

def loopCount (edges : List (ℕ × ℕ)) : ℕ :=
  edges.filter (fun e => e.1 == e.2) |>.length

def symmetricOn (edges : List (ℕ × ℕ)) (vertices : List ℕ) : Prop :=
  ∀ a ∈ vertices, ∀ b ∈ vertices, relates edges a b = true → relates edges b a = true

theorem symmetricOn_nil (edges : List (ℕ × ℕ)) :
    symmetricOn edges [] := by
  intro a ha
  simp at ha

theorem loopCount_nil :
    loopCount [] = 0 := by
  rfl

def sampleEdges : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (2, 2)]

example : relates sampleEdges 0 1 = true := by
  native_decide

example : relates sampleEdges 1 2 = false := by
  native_decide

example : loopCount sampleEdges = 2 := by
  native_decide

structure RelationWindow where
  vertices : ℕ
  edges : ℕ
  loops : ℕ
  symmetricPairs : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RelationWindow.loopControlled (w : RelationWindow) : Prop :=
  w.loops ≤ w.vertices

def RelationWindow.edgeControlled (w : RelationWindow) : Prop :=
  w.edges ≤ w.vertices * w.vertices + w.slack

def RelationWindow.symmetricControlled (w : RelationWindow) : Prop :=
  2 * w.symmetricPairs ≤ w.edges + w.slack

def RelationWindow.ready (w : RelationWindow) : Prop :=
  w.loopControlled ∧ w.edgeControlled ∧ w.symmetricControlled

def RelationWindow.certificate (w : RelationWindow) : ℕ :=
  w.vertices + w.edges + w.loops + w.symmetricPairs + w.slack

theorem edges_le_certificate (w : RelationWindow) :
    w.edges ≤ w.certificate := by
  unfold RelationWindow.certificate
  omega

def sampleRelationWindow : RelationWindow :=
  { vertices := 3, edges := 4, loops := 2, symmetricPairs := 1, slack := 0 }

example : sampleRelationWindow.ready := by
  norm_num [sampleRelationWindow, RelationWindow.ready, RelationWindow.loopControlled,
    RelationWindow.edgeControlled, RelationWindow.symmetricControlled]


structure FiniteRelationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRelationsBudgetCertificate.controlled
    (c : FiniteRelationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRelationsBudgetCertificate.budgetControlled
    (c : FiniteRelationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRelationsBudgetCertificate.Ready
    (c : FiniteRelationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRelationsBudgetCertificate.size
    (c : FiniteRelationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRelations_budgetCertificate_le_size
    (c : FiniteRelationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRelationsBudgetCertificate :
    FiniteRelationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRelationsBudgetCertificate.controlled,
      sampleFiniteRelationsBudgetCertificate]
  · norm_num [FiniteRelationsBudgetCertificate.budgetControlled,
      sampleFiniteRelationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRelationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRelationsBudgetCertificate.controlled,
      sampleFiniteRelationsBudgetCertificate]
  · norm_num [FiniteRelationsBudgetCertificate.budgetControlled,
      sampleFiniteRelationsBudgetCertificate]

example :
    sampleFiniteRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRelationsBudgetCertificate.size := by
  apply finiteRelations_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRelationsBudgetCertificate.controlled,
      sampleFiniteRelationsBudgetCertificate]
  · norm_num [FiniteRelationsBudgetCertificate.budgetControlled,
      sampleFiniteRelationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRelationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRelationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRelationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRelations
