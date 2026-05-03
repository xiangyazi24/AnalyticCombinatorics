import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ConnectedStructures

/-!
# Connected structures and logarithmic constructions

Small bounded tables for Chapter II connected constructions.  The labelled
tables use sizes `1, ..., 7`, except for indecomposable permutations where the
bounded recurrence is checked through size `10`.
-/

/-! ## Connected labelled graphs -/

/-- Connected labelled simple graph counts for `n = 1, ..., 7`. -/
def connectedGraphTable : Fin 7 → ℕ :=
  ![1, 1, 4, 38, 728, 26704, 1866256]

/-- Total labelled simple graph counts `2^binom(n,2)` for `n = 1, ..., 7`. -/
def totalGraphTable : Fin 7 → ℕ :=
  ![1, 2, 8, 64, 1024, 32768, 2097152]

/-- Connected labelled simple graph count, with `0` outside the table. -/
def connectedGraphCount : ℕ → ℕ
  | 1 => connectedGraphTable 0
  | 2 => connectedGraphTable 1
  | 3 => connectedGraphTable 2
  | 4 => connectedGraphTable 3
  | 5 => connectedGraphTable 4
  | 6 => connectedGraphTable 5
  | 7 => connectedGraphTable 6
  | _ => 0

/-- Total labelled simple graph count, with the empty graph included. -/
def totalGraphCount : ℕ → ℕ
  | 0 => 1
  | 1 => totalGraphTable 0
  | 2 => totalGraphTable 1
  | 3 => totalGraphTable 2
  | 4 => totalGraphTable 3
  | 5 => totalGraphTable 4
  | 6 => totalGraphTable 5
  | 7 => totalGraphTable 6
  | _ => 0

def graphComponentExpansion (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n,
    Nat.choose (n - 1) (k - 1) * connectedGraphCount k * totalGraphCount (n - k)

theorem totalGraph_formula_table :
    ∀ i : Fin 7, totalGraphTable i = 2 ^ Nat.choose (i.val + 1) 2 := by
  native_decide

theorem connectedGraph_le_totalGraph_table :
    ∀ i : Fin 7, connectedGraphTable i ≤ totalGraphTable i := by
  native_decide

theorem graph_exponential_formula_checked :
    ∀ i : Fin 7, totalGraphCount (i.val + 1) = graphComponentExpansion (i.val + 1) := by
  native_decide

/-! ## Connected permutations: indecomposable permutations -/

/-- Indecomposable permutation counts for `n = 1, ..., 10`. -/
def connectedPermutationTable : Fin 10 → ℕ :=
  ![1, 1, 3, 13, 71, 461, 3447, 29093, 273343, 2829325]

/-- Indecomposable permutation count, with `0` outside the table. -/
def connectedPermutationCount : ℕ → ℕ
  | 1 => connectedPermutationTable 0
  | 2 => connectedPermutationTable 1
  | 3 => connectedPermutationTable 2
  | 4 => connectedPermutationTable 3
  | 5 => connectedPermutationTable 4
  | 6 => connectedPermutationTable 5
  | 7 => connectedPermutationTable 6
  | 8 => connectedPermutationTable 7
  | 9 => connectedPermutationTable 8
  | 10 => connectedPermutationTable 9
  | _ => 0

def permutationPrefixExpansion (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n,
    connectedPermutationCount k * Nat.factorial (n - k)

theorem connectedPermutation_prefix_decomposition_checked :
    ∀ i : Fin 10, Nat.factorial (i.val + 1) = permutationPrefixExpansion (i.val + 1) := by
  native_decide

theorem connectedPermutation_growth_checked :
    ∀ i : Fin 9, connectedPermutationTable i.castSucc ≤ connectedPermutationTable i.succ := by
  native_decide

/-! ## Connected chord diagrams -/

/-- Total chord diagrams with `n = 1, ..., 7` chords. -/
def totalChordDiagramTable : Fin 7 → ℕ :=
  ![1, 3, 15, 105, 945, 10395, 135135]

/-- Chord diagrams whose crossing graph is connected, for `n = 1, ..., 7` chords. -/
def connectedChordDiagramTable : Fin 7 → ℕ :=
  ![1, 1, 4, 27, 248, 2830, 38232]

theorem connectedChordDiagram_le_total_table :
    ∀ i : Fin 7, connectedChordDiagramTable i ≤ totalChordDiagramTable i := by
  native_decide

theorem totalChordDiagram_odd_double_factorial_table :
    totalChordDiagramTable 0 = 1 ∧
    totalChordDiagramTable 1 = 1 * 3 ∧
    totalChordDiagramTable 2 = 1 * 3 * 5 ∧
    totalChordDiagramTable 3 = 1 * 3 * 5 * 7 ∧
    totalChordDiagramTable 4 = 1 * 3 * 5 * 7 * 9 ∧
    totalChordDiagramTable 5 = 1 * 3 * 5 * 7 * 9 * 11 ∧
    totalChordDiagramTable 6 = 1 * 3 * 5 * 7 * 9 * 11 * 13 := by
  native_decide

/-! ## Connected posets under labelled disjoint union -/

/-- Total labelled poset counts for `n = 1, ..., 7`. -/
def totalPosetTable : Fin 7 → ℕ :=
  ![1, 3, 19, 219, 4231, 130023, 6129859]

/-- Connected labelled poset counts for `n = 1, ..., 7`. -/
def connectedPosetTable : Fin 7 → ℕ :=
  ![1, 2, 12, 146, 3060, 101642, 5106612]

def connectedPosetCount : ℕ → ℕ
  | 1 => connectedPosetTable 0
  | 2 => connectedPosetTable 1
  | 3 => connectedPosetTable 2
  | 4 => connectedPosetTable 3
  | 5 => connectedPosetTable 4
  | 6 => connectedPosetTable 5
  | 7 => connectedPosetTable 6
  | _ => 0

def totalPosetCount : ℕ → ℕ
  | 0 => 1
  | 1 => totalPosetTable 0
  | 2 => totalPosetTable 1
  | 3 => totalPosetTable 2
  | 4 => totalPosetTable 3
  | 5 => totalPosetTable 4
  | 6 => totalPosetTable 5
  | 7 => totalPosetTable 6
  | _ => 0

def posetComponentExpansion (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n,
    Nat.choose (n - 1) (k - 1) * connectedPosetCount k * totalPosetCount (n - k)

theorem connectedPoset_le_total_table :
    ∀ i : Fin 7, connectedPosetTable i ≤ totalPosetTable i := by
  native_decide

theorem poset_exponential_formula_checked :
    ∀ i : Fin 7, totalPosetCount (i.val + 1) = posetComponentExpansion (i.val + 1) := by
  native_decide

/-! ## Weakly connected labelled digraphs -/

/-- Total loopless labelled digraph counts `2^(n*(n-1))` for `n = 1, ..., 7`. -/
def totalDigraphTable : Fin 7 → ℕ :=
  ![1, 4, 64, 4096, 1048576, 1073741824, 4398046511104]

/-- Weakly connected loopless labelled digraph counts for `n = 1, ..., 7`. -/
def connectedDigraphTable : Fin 7 → ℕ :=
  ![1, 3, 54, 3834, 1027080, 1067308488, 4390480193904]

def connectedDigraphCount : ℕ → ℕ
  | 1 => connectedDigraphTable 0
  | 2 => connectedDigraphTable 1
  | 3 => connectedDigraphTable 2
  | 4 => connectedDigraphTable 3
  | 5 => connectedDigraphTable 4
  | 6 => connectedDigraphTable 5
  | 7 => connectedDigraphTable 6
  | _ => 0

def totalDigraphCount : ℕ → ℕ
  | 0 => 1
  | 1 => totalDigraphTable 0
  | 2 => totalDigraphTable 1
  | 3 => totalDigraphTable 2
  | 4 => totalDigraphTable 3
  | 5 => totalDigraphTable 4
  | 6 => totalDigraphTable 5
  | 7 => totalDigraphTable 6
  | _ => 0

def digraphComponentExpansion (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n,
    Nat.choose (n - 1) (k - 1) * connectedDigraphCount k * totalDigraphCount (n - k)

theorem totalDigraph_formula_table :
    ∀ i : Fin 7, totalDigraphTable i = 2 ^ ((i.val + 1) * i.val) := by
  native_decide

theorem connectedDigraph_le_total_table :
    ∀ i : Fin 7, connectedDigraphTable i ≤ totalDigraphTable i := by
  native_decide

theorem digraph_exponential_formula_checked :
    ∀ i : Fin 7, totalDigraphCount (i.val + 1) = digraphComponentExpansion (i.val + 1) := by
  native_decide

/-! ## Logarithmic extraction instances -/

def egfLogCoeffOne (a₁ : ℤ) : ℤ :=
  a₁

def egfLogCoeffTwo (a₁ a₂ : ℤ) : ℤ :=
  a₂ - a₁ ^ 2

def egfLogCoeffThree (a₁ a₂ a₃ : ℤ) : ℤ :=
  a₃ - 3 * a₁ * a₂ + 2 * a₁ ^ 3

def egfLogCoeffFour (a₁ a₂ a₃ a₄ : ℤ) : ℤ :=
  a₄ - 4 * a₁ * a₃ - 3 * a₂ ^ 2 + 12 * a₁ ^ 2 * a₂ - 6 * a₁ ^ 4

theorem graph_log_extraction_up_to_four :
    egfLogCoeffOne (totalGraphCount 1 : ℤ) = (connectedGraphCount 1 : ℤ) ∧
    egfLogCoeffTwo (totalGraphCount 1 : ℤ) (totalGraphCount 2 : ℤ) =
      (connectedGraphCount 2 : ℤ) ∧
    egfLogCoeffThree (totalGraphCount 1 : ℤ) (totalGraphCount 2 : ℤ)
      (totalGraphCount 3 : ℤ) = (connectedGraphCount 3 : ℤ) ∧
    egfLogCoeffFour (totalGraphCount 1 : ℤ) (totalGraphCount 2 : ℤ)
      (totalGraphCount 3 : ℤ) (totalGraphCount 4 : ℤ) = (connectedGraphCount 4 : ℤ) := by
  native_decide

theorem poset_log_extraction_up_to_four :
    egfLogCoeffOne (totalPosetCount 1 : ℤ) = (connectedPosetCount 1 : ℤ) ∧
    egfLogCoeffTwo (totalPosetCount 1 : ℤ) (totalPosetCount 2 : ℤ) =
      (connectedPosetCount 2 : ℤ) ∧
    egfLogCoeffThree (totalPosetCount 1 : ℤ) (totalPosetCount 2 : ℤ)
      (totalPosetCount 3 : ℤ) = (connectedPosetCount 3 : ℤ) ∧
    egfLogCoeffFour (totalPosetCount 1 : ℤ) (totalPosetCount 2 : ℤ)
      (totalPosetCount 3 : ℤ) (totalPosetCount 4 : ℤ) = (connectedPosetCount 4 : ℤ) := by
  native_decide

theorem digraph_log_extraction_up_to_four :
    egfLogCoeffOne (totalDigraphCount 1 : ℤ) = (connectedDigraphCount 1 : ℤ) ∧
    egfLogCoeffTwo (totalDigraphCount 1 : ℤ) (totalDigraphCount 2 : ℤ) =
      (connectedDigraphCount 2 : ℤ) ∧
    egfLogCoeffThree (totalDigraphCount 1 : ℤ) (totalDigraphCount 2 : ℤ)
      (totalDigraphCount 3 : ℤ) = (connectedDigraphCount 3 : ℤ) ∧
    egfLogCoeffFour (totalDigraphCount 1 : ℤ) (totalDigraphCount 2 : ℤ)
      (totalDigraphCount 3 : ℤ) (totalDigraphCount 4 : ℤ) = (connectedDigraphCount 4 : ℤ) := by
  native_decide

end ConnectedStructures
