import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Tree structures.
-/

namespace AnalyticCombinatorics.PartA.Ch1.TreeStructures

/-- Catalan-count model for plane binary tree shapes. -/
def catalanTreeCount (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- Finite envelope check for tree families. -/
def treeEnvelopeCheck (a envelope : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => a n ≤ envelope n

/-- Finite nondecreasing check for sampled tree-count envelopes. -/
def nondecreasingUpTo (a : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range N).all fun n => a n ≤ a (n + 1)

/-- Finite statement form for a tree family with a growth envelope. -/
def TreeFamilyWindow (a envelope : ℕ → ℕ) (N : ℕ) : Prop :=
  treeEnvelopeCheck a envelope N = true ∧
    nondecreasingUpTo envelope N = true

theorem catalanTreeCount_samples :
    catalanTreeCount 0 = 1 ∧
    catalanTreeCount 1 = 1 ∧
    catalanTreeCount 2 = 2 ∧
    catalanTreeCount 3 = 5 ∧
    catalanTreeCount 4 = 14 := by
  unfold catalanTreeCount
  native_decide

theorem catalanTreeCount_exponentialWindow :
    TreeFamilyWindow catalanTreeCount (fun n => 4 ^ n) 16 := by
  unfold TreeFamilyWindow treeEnvelopeCheck nondecreasingUpTo catalanTreeCount
  native_decide

/-- Finite Catalan recurrence audit for plane binary tree shapes. -/
def catalanTreeRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    catalanTreeCount (n + 1) * (n + 2) =
      2 * (2 * n + 1) * catalanTreeCount n

theorem catalanTreeCount_recurrenceWindow :
    catalanTreeRecurrenceCheck 12 = true := by
  unfold catalanTreeRecurrenceCheck catalanTreeCount
  native_decide

example : catalanTreeCount 5 = 42 := by
  unfold catalanTreeCount
  native_decide

example : treeEnvelopeCheck catalanTreeCount (fun n => 4 ^ n) 8 = true := by
  unfold treeEnvelopeCheck catalanTreeCount
  native_decide

structure TreeStructuresBudgetCertificate where
  nodeWindow : ℕ
  branchingWindow : ℕ
  treeWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeStructuresBudgetCertificate.controlled
    (c : TreeStructuresBudgetCertificate) : Prop :=
  0 < c.nodeWindow ∧ c.treeWindow ≤ c.nodeWindow + c.branchingWindow + c.slack

def TreeStructuresBudgetCertificate.budgetControlled
    (c : TreeStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.nodeWindow + c.branchingWindow + c.treeWindow + c.slack

def TreeStructuresBudgetCertificate.Ready
    (c : TreeStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TreeStructuresBudgetCertificate.size
    (c : TreeStructuresBudgetCertificate) : ℕ :=
  c.nodeWindow + c.branchingWindow + c.treeWindow + c.slack

theorem treeStructures_budgetCertificate_le_size
    (c : TreeStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleTreeStructuresBudgetCertificate : TreeStructuresBudgetCertificate :=
  { nodeWindow := 5
    branchingWindow := 6
    treeWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleTreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeStructuresBudgetCertificate.controlled,
      sampleTreeStructuresBudgetCertificate]
  · norm_num [TreeStructuresBudgetCertificate.budgetControlled,
      sampleTreeStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTreeStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleTreeStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleTreeStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [TreeStructuresBudgetCertificate.controlled,
      sampleTreeStructuresBudgetCertificate]
  · norm_num [TreeStructuresBudgetCertificate.budgetControlled,
      sampleTreeStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List TreeStructuresBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleTreeStructuresBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleTreeStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.TreeStructures
