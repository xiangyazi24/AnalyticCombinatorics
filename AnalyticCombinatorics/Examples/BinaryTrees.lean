import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Binary tree examples.

This module records Catalan counts for binary trees as executable checks.
-/

namespace AnalyticCombinatorics.Examples.BinaryTrees

/-- Catalan number table for `0 <= n <= 20`, with `0` outside the table. -/
def catalanCount : ℕ → ℕ
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
  | 11 => 58786
  | 12 => 208012
  | 13 => 742900
  | 14 => 2674440
  | 15 => 9694845
  | 16 => 35357670
  | 17 => 129644790
  | 18 => 477638700
  | 19 => 1767263190
  | 20 => 6564120420
  | _ => 0

/-- Binary trees with `n` internal nodes are counted by `C_n`. -/
def binaryTreeCount (n : ℕ) : ℕ := catalanCount n

example : binaryTreeCount 0 = 1 := by native_decide
example : binaryTreeCount 1 = 1 := by native_decide
example : binaryTreeCount 2 = 2 := by native_decide
example : binaryTreeCount 3 = 5 := by native_decide
example : binaryTreeCount 4 = 14 := by native_decide
example : binaryTreeCount 5 = 42 := by native_decide
example : binaryTreeCount 10 = 16796 := by native_decide
example : binaryTreeCount 20 = 6564120420 := by native_decide

theorem binaryTreeCount_values_0_to_10 :
    (List.range 11).map binaryTreeCount =
      [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796] := by
  native_decide

/-- Finite Catalan recurrence audit for the binary-tree table. -/
def binaryTreeCatalanRecurrenceCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    binaryTreeCount (n + 1) * (n + 2) =
      2 * (2 * n + 1) * binaryTreeCount n

theorem binaryTreeCount_recurrenceWindow :
    binaryTreeCatalanRecurrenceCheck 10 = true := by
  unfold binaryTreeCatalanRecurrenceCheck binaryTreeCount catalanCount
  native_decide

structure BinaryTreesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinaryTreesBudgetCertificate.controlled
    (c : BinaryTreesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BinaryTreesBudgetCertificate.budgetControlled
    (c : BinaryTreesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BinaryTreesBudgetCertificate.Ready
    (c : BinaryTreesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BinaryTreesBudgetCertificate.size (c : BinaryTreesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem binaryTrees_budgetCertificate_le_size
    (c : BinaryTreesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBinaryTreesBudgetCertificate : BinaryTreesBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleBinaryTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [BinaryTreesBudgetCertificate.controlled,
      sampleBinaryTreesBudgetCertificate]
  · norm_num [BinaryTreesBudgetCertificate.budgetControlled,
      sampleBinaryTreesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBinaryTreesBudgetCertificate.Ready := by
  constructor
  · norm_num [BinaryTreesBudgetCertificate.controlled,
      sampleBinaryTreesBudgetCertificate]
  · norm_num [BinaryTreesBudgetCertificate.budgetControlled,
      sampleBinaryTreesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBinaryTreesBudgetCertificate.certificateBudgetWindow ≤
      sampleBinaryTreesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BinaryTreesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBinaryTreesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBinaryTreesBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.BinaryTrees
