import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite equivalence-relation bookkeeping via blocks.

Blocks are represented by lists of natural labels; this is enough for small
coefficient partitions and quotient-class examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteEquivalenceRelations

def blockContains (x : ℕ) (block : List ℕ) : Bool :=
  block.any (fun y => y == x)

def classCount (blocks : List (List ℕ)) : ℕ :=
  blocks.length

def totalBlockMass (blocks : List (List ℕ)) : ℕ :=
  blocks.map List.length |>.sum

def singletonBlocks (xs : List ℕ) : List (List ℕ) :=
  xs.map (fun x => [x])

theorem classCount_singletonBlocks (xs : List ℕ) :
    classCount (singletonBlocks xs) = xs.length := by
  simp [classCount, singletonBlocks]

theorem totalBlockMass_nil :
    totalBlockMass [] = 0 := by
  rfl

theorem classCount_cons (b : List ℕ) (blocks : List (List ℕ)) :
    classCount (b :: blocks) = classCount blocks + 1 := by
  simp [classCount]

def sampleBlocks : List (List ℕ) :=
  [[0, 2], [1], [3, 4, 5]]

example : blockContains 2 [0, 2] = true := by
  native_decide

example : classCount sampleBlocks = 3 := by
  native_decide

example : totalBlockMass sampleBlocks = 6 := by
  native_decide

structure EquivalenceWindow where
  elements : ℕ
  classes : ℕ
  totalMass : ℕ
  singletonClasses : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EquivalenceWindow.massReady (w : EquivalenceWindow) : Prop :=
  w.totalMass ≤ w.elements + w.slack

def EquivalenceWindow.classControlled (w : EquivalenceWindow) : Prop :=
  w.classes ≤ w.elements + w.slack ∧ w.singletonClasses ≤ w.classes

def EquivalenceWindow.ready (w : EquivalenceWindow) : Prop :=
  w.massReady ∧ w.classControlled

def EquivalenceWindow.certificate (w : EquivalenceWindow) : ℕ :=
  w.elements + w.classes + w.totalMass + w.singletonClasses + w.slack

theorem classes_le_certificate (w : EquivalenceWindow) :
    w.classes ≤ w.certificate := by
  unfold EquivalenceWindow.certificate
  omega

def sampleEquivalenceWindow : EquivalenceWindow :=
  { elements := 6, classes := 3, totalMass := 6, singletonClasses := 1, slack := 0 }

example : sampleEquivalenceWindow.ready := by
  norm_num [sampleEquivalenceWindow, EquivalenceWindow.ready,
    EquivalenceWindow.massReady, EquivalenceWindow.classControlled]


structure FiniteEquivalenceRelationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteEquivalenceRelationsBudgetCertificate.controlled
    (c : FiniteEquivalenceRelationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteEquivalenceRelationsBudgetCertificate.budgetControlled
    (c : FiniteEquivalenceRelationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteEquivalenceRelationsBudgetCertificate.Ready
    (c : FiniteEquivalenceRelationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteEquivalenceRelationsBudgetCertificate.size
    (c : FiniteEquivalenceRelationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteEquivalenceRelations_budgetCertificate_le_size
    (c : FiniteEquivalenceRelationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteEquivalenceRelationsBudgetCertificate :
    FiniteEquivalenceRelationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteEquivalenceRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.controlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.budgetControlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]

example :
    sampleFiniteEquivalenceRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteEquivalenceRelationsBudgetCertificate.size := by
  apply finiteEquivalenceRelations_budgetCertificate_le_size
  constructor
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.controlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.budgetControlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteEquivalenceRelationsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.controlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]
  · norm_num [FiniteEquivalenceRelationsBudgetCertificate.budgetControlled,
      sampleFiniteEquivalenceRelationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteEquivalenceRelationsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteEquivalenceRelationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteEquivalenceRelationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteEquivalenceRelationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteEquivalenceRelationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteEquivalenceRelations
