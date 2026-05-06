import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Alignments, permutations, and related structures.

Finite tables for rencontres, excedance, record, and arrangement windows
used with labelled permutation classes.
-/

namespace AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsRelatedStructures

/-- Falling factorial `n^{underline k}`, counting injective alignments. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _n, 0 => 1
  | 0, _k + 1 => 0
  | n + 1, k + 1 => (n + 1) * fallingFactorial n k

theorem fallingFactorial_row5 :
    (List.range 7).map (fallingFactorial 5) =
      [1, 5, 20, 60, 120, 120, 0] := by
  native_decide

/-- Derangement numbers, used for rencontres tables. -/
def derangement : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangement (n + 1) + derangement n)

/-- Rencontres number: permutations of `n` labels with exactly `k` fixed points. -/
def rencontres (n k : ℕ) : ℕ :=
  n.choose k * derangement (n - k)

theorem rencontres_row5 :
    (List.range 6).map (rencontres 5) = [44, 45, 20, 10, 0, 1] := by
  native_decide

theorem rencontres_row5_sum :
    (List.range 6).foldl (fun s k => s + rencontres 5 k) 0 =
      Nat.factorial 5 := by
  native_decide

/-- Eulerian numbers by the standard recurrence. -/
def eulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _k + 1 => 0
  | _n + 1, 0 => 1
  | n + 1, k + 1 =>
      (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k

theorem eulerian_row5 :
    (List.range 5).map (eulerian 5) = [1, 26, 66, 26, 1] := by
  native_decide

theorem eulerian_row5_sum :
    (List.range 5).foldl (fun s k => s + eulerian 5 k) 0 =
      Nat.factorial 5 := by
  native_decide

/-- Unsigned Stirling numbers of the first kind, counting permutations by records/cycles. -/
def stirlingOne : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _k + 1 => 0
  | _n + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingOne n (k + 1) + stirlingOne n k

theorem stirlingOne_row5 :
    (List.range 6).map (stirlingOne 5) = [0, 24, 50, 35, 10, 1] := by
  native_decide

theorem stirlingOne_row5_sum :
    (List.range 6).foldl (fun s k => s + stirlingOne 5 k) 0 =
      Nat.factorial 5 := by
  native_decide

structure AlignmentPermutationRelatedWindow where
  labels : ℕ
  fixedPointWindow : ℕ
  excedanceWindow : ℕ
  recordWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlignmentPermutationRelatedWindow.ready
    (w : AlignmentPermutationRelatedWindow) : Prop :=
  0 < w.labels ∧
    w.fixedPointWindow ≤ w.labels + w.slack ∧
      w.excedanceWindow ≤ w.labels + w.slack ∧
        w.recordWindow ≤ w.labels + w.slack

def sampleAlignmentPermutationRelatedWindow :
    AlignmentPermutationRelatedWindow :=
  { labels := 5
    fixedPointWindow := 5
    excedanceWindow := 4
    recordWindow := 5
    slack := 0 }

example : sampleAlignmentPermutationRelatedWindow.ready := by
  norm_num [AlignmentPermutationRelatedWindow.ready,
    sampleAlignmentPermutationRelatedWindow]

structure AlignmentsPermutationsRelatedStructuresBudgetCertificate where
  alignmentWindow : ℕ
  permutationWindow : ℕ
  relatedStructureWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlignmentsPermutationsRelatedStructuresBudgetCertificate.controlled
    (c : AlignmentsPermutationsRelatedStructuresBudgetCertificate) : Prop :=
  0 < c.alignmentWindow ∧
    c.relatedStructureWindow ≤ c.alignmentWindow + c.permutationWindow + c.slack

def AlignmentsPermutationsRelatedStructuresBudgetCertificate.budgetControlled
    (c : AlignmentsPermutationsRelatedStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.alignmentWindow + c.permutationWindow + c.relatedStructureWindow + c.slack

def AlignmentsPermutationsRelatedStructuresBudgetCertificate.Ready
    (c : AlignmentsPermutationsRelatedStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlignmentsPermutationsRelatedStructuresBudgetCertificate.size
    (c : AlignmentsPermutationsRelatedStructuresBudgetCertificate) : ℕ :=
  c.alignmentWindow + c.permutationWindow + c.relatedStructureWindow + c.slack

theorem alignmentsPermutationsRelatedStructures_budgetCertificate_le_size
    (c : AlignmentsPermutationsRelatedStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate :
    AlignmentsPermutationsRelatedStructuresBudgetCertificate :=
  { alignmentWindow := 5
    permutationWindow := 6
    relatedStructureWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [AlignmentsPermutationsRelatedStructuresBudgetCertificate.controlled,
      sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate]
  · norm_num [AlignmentsPermutationsRelatedStructuresBudgetCertificate.budgetControlled,
      sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [AlignmentsPermutationsRelatedStructuresBudgetCertificate.controlled,
      sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate]
  · norm_num [AlignmentsPermutationsRelatedStructuresBudgetCertificate.budgetControlled,
      sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AlignmentsPermutationsRelatedStructuresBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleAlignmentsPermutationsRelatedStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AlignmentsPermutationsRelatedStructures
