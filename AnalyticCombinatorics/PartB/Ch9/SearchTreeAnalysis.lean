import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.SearchTreeAnalysis


/-!
# Search Tree Analysis and Digital Structures

Small finite tables for the search-tree and digital-structure side of
Chapter IX of Flajolet and Sedgewick.  The tables deliberately stay bounded:
BST and Quicksort averages are represented by their values multiplied by `n!`,
and all indexed data use `Fin n` with `n ≤ 12`.
-/

/-! ## Harmonic sums scaled by factorials -/

/-- `n! * H_n`, computed as an integer sum for small `n`. -/
def scaledHarmonic (n : ℕ) : ℕ :=
  (Finset.range n).sum (fun i => Nat.factorial n / (i + 1))

/-- Values of `n! * H_n` for `0 ≤ n ≤ 10`. -/
def scaledHarmonicTable : Fin 11 → ℕ :=
  ![0, 1, 3, 11, 50, 274, 1764, 13068, 109584, 1026576, 10628640]

theorem scaledHarmonic_values :
    List.map scaledHarmonic [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
      [0, 1, 3, 11, 50, 274, 1764, 13068, 109584, 1026576, 10628640] := by
  native_decide

theorem scaledHarmonicTable_values :
    List.ofFn scaledHarmonicTable =
      [0, 1, 3, 11, 50, 274, 1764, 13068, 109584, 1026576, 10628640] := by
  native_decide

/-! ## Random BST internal path length -/

/-- Expected internal path length of a random BST, multiplied by `n!`. -/
def bstExpectedPathLengthScaled (n : ℕ) : ℕ :=
  2 * (n + 1) * scaledHarmonic n - 4 * n * Nat.factorial n

/-- Scaled expected internal path lengths for random BSTs, `0 ≤ n ≤ 10`. -/
def bstExpectedPathLengthTable : Fin 11 → ℕ :=
  ![0, 0, 2, 16, 116, 888, 7416, 67968, 682272, 7467840, 88678080]

theorem bstExpectedPathLength_values :
    List.map bstExpectedPathLengthScaled [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
      [0, 0, 2, 16, 116, 888, 7416, 67968, 682272, 7467840, 88678080] := by
  native_decide

theorem bstExpectedPathLengthTable_values :
    List.ofFn bstExpectedPathLengthTable =
      [0, 0, 2, 16, 116, 888, 7416, 67968, 682272, 7467840, 88678080] := by
  native_decide

/-- Expected external path length of a random BST, multiplied by `n!`. -/
def randomBSTExternalPathLengthScaled (n : ℕ) : ℕ :=
  bstExpectedPathLengthScaled n + 2 * n * Nat.factorial n

/-- Scaled expected external path lengths for random BSTs, `0 ≤ n ≤ 10`. -/
def randomBSTExternalPathLengthTable : Fin 11 → ℕ :=
  ![0, 2, 10, 52, 308, 2088, 16056, 138528, 1327392, 13999680, 161254080]

theorem randomBSTExternalPathLength_values :
    List.map randomBSTExternalPathLengthScaled [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
      [0, 2, 10, 52, 308, 2088, 16056, 138528, 1327392, 13999680, 161254080] := by
  native_decide

/-! ## Quicksort comparisons -/

/-- Expected Quicksort comparisons, multiplied by `n!`, for the same recurrence as
    BST path length. -/
def quicksortComparisonsScaled (n : ℕ) : ℕ :=
  bstExpectedPathLengthScaled n

/-- Scaled expected Quicksort comparisons for `0 ≤ n ≤ 10`. -/
def quicksortComparisonsTable : Fin 11 → ℕ :=
  ![0, 0, 2, 16, 116, 888, 7416, 67968, 682272, 7467840, 88678080]

theorem quicksortComparisons_values :
    List.map quicksortComparisonsScaled [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
      [0, 0, 2, 16, 116, 888, 7416, 67968, 682272, 7467840, 88678080] := by
  native_decide

theorem quicksort_matches_bst_table :
    List.ofFn quicksortComparisonsTable = List.ofFn bstExpectedPathLengthTable := by
  native_decide

/-! ## AVL height bounds -/

/-- Minimum number of nodes in an AVL tree of exact height `h`, for small `h`. -/
def avlMinNodes : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | h + 2 => avlMinNodes (h + 1) + avlMinNodes h + 1

/-- AVL minimum node counts by height, for `0 ≤ h ≤ 10`. -/
def avlMinNodesTable : Fin 11 → ℕ :=
  ![1, 2, 4, 7, 12, 20, 33, 54, 88, 143, 232]

theorem avlMinNodes_values :
    List.map avlMinNodes [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
      [1, 2, 4, 7, 12, 20, 33, 54, 88, 143, 232] := by
  native_decide

theorem avlMinNodesTable_values :
    List.ofFn avlMinNodesTable = [1, 2, 4, 7, 12, 20, 33, 54, 88, 143, 232] := by
  native_decide

/-! ## 2-3 tree node-count bounds -/

/-- Minimum total nodes in a complete 2-3 tree of height `h`. -/
def twoThreeMinNodes (h : ℕ) : ℕ :=
  2 ^ (h + 1) - 1

/-- Maximum total nodes in a complete 2-3 tree of height `h`. -/
def twoThreeMaxNodes (h : ℕ) : ℕ :=
  (3 ^ (h + 1) - 1) / 2

/-- Minimum total node counts for 2-3 trees, `0 ≤ h ≤ 9`. -/
def twoThreeMinNodesTable : Fin 10 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023]

/-- Maximum total node counts for 2-3 trees, `0 ≤ h ≤ 9`. -/
def twoThreeMaxNodesTable : Fin 10 → ℕ :=
  ![1, 4, 13, 40, 121, 364, 1093, 3280, 9841, 29524]

theorem twoThreeMinNodes_values :
    List.map twoThreeMinNodes [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] =
      [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023] := by
  native_decide

theorem twoThreeMaxNodes_values :
    List.map twoThreeMaxNodes [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] =
      [1, 4, 13, 40, 121, 364, 1093, 3280, 9841, 29524] := by
  native_decide

/-! ## Binary tries -/

/-- Number of binary strings at exact depth `d`. -/
def binaryTrieLevelSize (d : ℕ) : ℕ :=
  2 ^ d

/-- Number of binary prefixes of length at most `d`. -/
def binaryTriePrefixCapacity (d : ℕ) : ℕ :=
  2 ^ (d + 1) - 1

/-- Level sizes in the full binary trie for `0 ≤ d ≤ 11`. -/
def binaryTrieLevelSizeTable : Fin 12 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- Prefix capacities in the full binary trie for `0 ≤ d ≤ 11`. -/
def binaryTriePrefixCapacityTable : Fin 12 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095]

theorem binaryTrieLevelSize_values :
    List.map binaryTrieLevelSize [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  native_decide

theorem binaryTriePrefixCapacity_values :
    List.map binaryTriePrefixCapacity [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] =
      [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095] := by
  native_decide

theorem binaryTrieCapacity_is_full_tree :
    List.ofFn binaryTriePrefixCapacityTable = List.map twoThreeMinNodes
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
  native_decide



structure SearchTreeAnalysisBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SearchTreeAnalysisBudgetCertificate.controlled
    (c : SearchTreeAnalysisBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SearchTreeAnalysisBudgetCertificate.budgetControlled
    (c : SearchTreeAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SearchTreeAnalysisBudgetCertificate.Ready
    (c : SearchTreeAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SearchTreeAnalysisBudgetCertificate.size
    (c : SearchTreeAnalysisBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem searchTreeAnalysis_budgetCertificate_le_size
    (c : SearchTreeAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSearchTreeAnalysisBudgetCertificate :
    SearchTreeAnalysisBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSearchTreeAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [SearchTreeAnalysisBudgetCertificate.controlled,
      sampleSearchTreeAnalysisBudgetCertificate]
  · norm_num [SearchTreeAnalysisBudgetCertificate.budgetControlled,
      sampleSearchTreeAnalysisBudgetCertificate]

example :
    sampleSearchTreeAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleSearchTreeAnalysisBudgetCertificate.size := by
  apply searchTreeAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [SearchTreeAnalysisBudgetCertificate.controlled,
      sampleSearchTreeAnalysisBudgetCertificate]
  · norm_num [SearchTreeAnalysisBudgetCertificate.budgetControlled,
      sampleSearchTreeAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSearchTreeAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [SearchTreeAnalysisBudgetCertificate.controlled,
      sampleSearchTreeAnalysisBudgetCertificate]
  · norm_num [SearchTreeAnalysisBudgetCertificate.budgetControlled,
      sampleSearchTreeAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSearchTreeAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleSearchTreeAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SearchTreeAnalysisBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSearchTreeAnalysisBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSearchTreeAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.SearchTreeAnalysis
