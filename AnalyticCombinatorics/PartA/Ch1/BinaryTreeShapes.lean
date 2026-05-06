import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.BinaryTreeShapes


/-!
  Chapter I finite checks for binary tree shapes and related structures.

  The file records the initial Catalan, Motzkin, and Schroeder tables used in
  elementary symbolic-method examples.  The assertions are deliberately finite
  computational checks.
-/

/-! ## Catalan numbers and full binary tree shapes -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- First Catalan numbers: `1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862`. -/
def catalanTable : Fin 10 → ℕ := ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- Full binary tree shapes with `2n+1` nodes are counted by `C_n`. -/
def fullBinaryTreeShapeCount (n : ℕ) : ℕ :=
  catalanNumber n

/-- Number of nodes in a full binary tree with `n` internal nodes. -/
def fullBinaryTreeNodeCount (n : ℕ) : ℕ :=
  2 * n + 1

/-- Number of leaves in a full binary tree with `n` internal nodes. -/
def fullBinaryTreeLeafCount (n : ℕ) : ℕ :=
  n + 1

/-- Ballot sequences of length `2n`, equivalently semilength `n`, are counted by `C_n`. -/
def ballotSequenceCount (n : ℕ) : ℕ :=
  catalanNumber n

theorem catalan_table_checked :
    (fun n : Fin 10 => catalanNumber n.val) = catalanTable := by
  native_decide

theorem catalan_initial_values :
    catalanNumber 0 = 1 ∧ catalanNumber 1 = 1 ∧ catalanNumber 2 = 2 ∧
      catalanNumber 3 = 5 ∧ catalanNumber 4 = 14 ∧ catalanNumber 5 = 42 ∧
      catalanNumber 6 = 132 ∧ catalanNumber 7 = 429 ∧
      catalanNumber 8 = 1430 ∧ catalanNumber 9 = 4862 := by
  native_decide

theorem full_binary_tree_shapes_counted_by_catalan :
    ∀ n : Fin 10, fullBinaryTreeShapeCount n.val = catalanNumber n.val := by
  native_decide

theorem full_binary_tree_shape_table :
    (fun n : Fin 10 => fullBinaryTreeShapeCount n.val) = catalanTable := by
  native_decide

theorem full_binary_tree_nodes_are_odd :
    (fun n : Fin 10 => fullBinaryTreeNodeCount n.val) =
      ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19] := by
  native_decide

theorem full_binary_tree_leaves_from_internal_nodes :
    ∀ n : Fin 10, fullBinaryTreeLeafCount n.val = n.val + 1 := by
  native_decide

theorem full_binary_tree_nodes_from_internal_and_leaves :
    ∀ n : Fin 10,
      fullBinaryTreeNodeCount n.val = n.val + fullBinaryTreeLeafCount n.val := by
  native_decide

theorem ballot_sequences_counted_by_catalan :
    ∀ n : Fin 10, ballotSequenceCount n.val = catalanNumber n.val := by
  native_decide

theorem ballot_sequence_table :
    (fun n : Fin 10 => ballotSequenceCount n.val) = catalanTable := by
  native_decide

/-! ## Motzkin numbers -/

/-- Motzkin numbers, with `0` outside the displayed finite table. -/
def motzkinNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 9
  | 5 => 21
  | 6 => 51
  | 7 => 127
  | 8 => 323
  | 9 => 835
  | _ => 0

/-- First Motzkin numbers: `1, 1, 2, 4, 9, 21, 51, 127, 323, 835`. -/
def motzkinTable : Fin 10 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

theorem motzkin_table_checked :
    (fun n : Fin 10 => motzkinNumber n.val) = motzkinTable := by
  native_decide

theorem motzkin_initial_values :
    motzkinNumber 0 = 1 ∧ motzkinNumber 1 = 1 ∧ motzkinNumber 2 = 2 ∧
      motzkinNumber 3 = 4 ∧ motzkinNumber 4 = 9 ∧ motzkinNumber 5 = 21 ∧
      motzkinNumber 6 = 51 ∧ motzkinNumber 7 = 127 ∧
      motzkinNumber 8 = 323 ∧ motzkinNumber 9 = 835 := by
  native_decide

/-- The standard Motzkin recurrence in addition form,
    `(n+2) M_n = (2n+1) M_{n-1} + 3(n-1) M_{n-2}`,
    checked for `n = 2..8`. -/
theorem motzkin_recurrence_checked_two_through_eight :
    ∀ k : Fin 7,
      let n := k.val + 2
      (n + 2) * motzkinNumber n =
        (2 * n + 1) * motzkinNumber (n - 1) +
          3 * (n - 1) * motzkinNumber (n - 2) := by
  native_decide

theorem motzkin_recurrence_addition_form_checked :
    (4 * motzkinNumber 2 = 5 * motzkinNumber 1 + 3 * 1 * motzkinNumber 0) ∧
      (5 * motzkinNumber 3 = 7 * motzkinNumber 2 + 3 * 2 * motzkinNumber 1) ∧
      (6 * motzkinNumber 4 = 9 * motzkinNumber 3 + 3 * 3 * motzkinNumber 2) ∧
      (7 * motzkinNumber 5 = 11 * motzkinNumber 4 + 3 * 4 * motzkinNumber 3) ∧
      (8 * motzkinNumber 6 = 13 * motzkinNumber 5 + 3 * 5 * motzkinNumber 4) ∧
      (9 * motzkinNumber 7 = 15 * motzkinNumber 6 + 3 * 6 * motzkinNumber 5) ∧
      (10 * motzkinNumber 8 = 17 * motzkinNumber 7 + 3 * 7 * motzkinNumber 6) := by
  native_decide

/-! ## Schroeder numbers -/

/-- Large Schroeder numbers, with `0` outside the displayed finite table. -/
def largeSchroderNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | 6 => 1806
  | 7 => 8558
  | _ => 0

/-- Small Schroeder, or super-Catalan, numbers. -/
def smallSchroderNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 11
  | 4 => 45
  | 5 => 197
  | 6 => 903
  | 7 => 4279
  | _ => 0

/-- Large Schroeder numbers: `1, 2, 6, 22, 90, 394, 1806, 8558`. -/
def largeSchroderTable : Fin 8 → ℕ := ![1, 2, 6, 22, 90, 394, 1806, 8558]

/-- Small Schroeder numbers: `1, 1, 3, 11, 45, 197, 903, 4279`. -/
def smallSchroderTable : Fin 8 → ℕ := ![1, 1, 3, 11, 45, 197, 903, 4279]

theorem large_schroder_table_checked :
    (fun n : Fin 8 => largeSchroderNumber n.val) = largeSchroderTable := by
  native_decide

theorem small_schroder_table_checked :
    (fun n : Fin 8 => smallSchroderNumber n.val) = smallSchroderTable := by
  native_decide

theorem large_schroder_initial_values :
    largeSchroderNumber 0 = 1 ∧ largeSchroderNumber 1 = 2 ∧
      largeSchroderNumber 2 = 6 ∧ largeSchroderNumber 3 = 22 ∧
      largeSchroderNumber 4 = 90 ∧ largeSchroderNumber 5 = 394 ∧
      largeSchroderNumber 6 = 1806 ∧ largeSchroderNumber 7 = 8558 := by
  native_decide

theorem small_schroder_initial_values :
    smallSchroderNumber 0 = 1 ∧ smallSchroderNumber 1 = 1 ∧
      smallSchroderNumber 2 = 3 ∧ smallSchroderNumber 3 = 11 ∧
      smallSchroderNumber 4 = 45 ∧ smallSchroderNumber 5 = 197 ∧
      smallSchroderNumber 6 = 903 ∧ smallSchroderNumber 7 = 4279 := by
  native_decide

/-- Large Schroeder numbers are twice the small Schroeder numbers after index `0`. -/
theorem large_schroder_twice_small_one_through_seven :
    ∀ k : Fin 7,
      let n := k.val + 1
      largeSchroderNumber n = 2 * smallSchroderNumber n := by
  native_decide

theorem large_schroder_not_twice_small_at_zero :
    largeSchroderNumber 0 ≠ 2 * smallSchroderNumber 0 := by
  native_decide



structure BinaryTreeShapesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BinaryTreeShapesBudgetCertificate.controlled
    (c : BinaryTreeShapesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BinaryTreeShapesBudgetCertificate.budgetControlled
    (c : BinaryTreeShapesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BinaryTreeShapesBudgetCertificate.Ready
    (c : BinaryTreeShapesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BinaryTreeShapesBudgetCertificate.size
    (c : BinaryTreeShapesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem binaryTreeShapes_budgetCertificate_le_size
    (c : BinaryTreeShapesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBinaryTreeShapesBudgetCertificate :
    BinaryTreeShapesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBinaryTreeShapesBudgetCertificate.Ready := by
  constructor
  · norm_num [BinaryTreeShapesBudgetCertificate.controlled,
      sampleBinaryTreeShapesBudgetCertificate]
  · norm_num [BinaryTreeShapesBudgetCertificate.budgetControlled,
      sampleBinaryTreeShapesBudgetCertificate]

example :
    sampleBinaryTreeShapesBudgetCertificate.certificateBudgetWindow ≤
      sampleBinaryTreeShapesBudgetCertificate.size := by
  apply binaryTreeShapes_budgetCertificate_le_size
  constructor
  · norm_num [BinaryTreeShapesBudgetCertificate.controlled,
      sampleBinaryTreeShapesBudgetCertificate]
  · norm_num [BinaryTreeShapesBudgetCertificate.budgetControlled,
      sampleBinaryTreeShapesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBinaryTreeShapesBudgetCertificate.Ready := by
  constructor
  · norm_num [BinaryTreeShapesBudgetCertificate.controlled,
      sampleBinaryTreeShapesBudgetCertificate]
  · norm_num [BinaryTreeShapesBudgetCertificate.budgetControlled,
      sampleBinaryTreeShapesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBinaryTreeShapesBudgetCertificate.certificateBudgetWindow ≤
      sampleBinaryTreeShapesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BinaryTreeShapesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBinaryTreeShapesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBinaryTreeShapesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.BinaryTreeShapes
