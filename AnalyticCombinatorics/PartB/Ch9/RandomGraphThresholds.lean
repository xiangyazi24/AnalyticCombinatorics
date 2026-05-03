import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace RandomGraphThresholds

/-!
# Random graph thresholds

Bounded numerical checks for Erdos-Renyi threshold data from the random graph
discussion in Chapter IX of Flajolet and Sedgewick.
-/

/-- Number of possible edges in a labelled graph on `n` vertices. -/
def possibleEdges (n : Nat) : Nat :=
  Nat.choose n 2

/-- Table of `choose n 2` for `0 <= n < 12`. -/
def possibleEdgesTable : Fin 12 -> Nat :=
  ![0, 0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55]

/-- At the sparse scale `p = c/n`, twice the expected edge count is `c*(n-1)`. -/
def sparseThresholdTwiceExpectedEdges (n c : Nat) : Nat :=
  c * (n - 1)

/-- The `c = 1` table for twice the expected number of edges at `p = 1/n`. -/
def criticalWindowTwiceEdgesTable : Fin 12 -> Nat :=
  ![0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- Connected labelled graph counts for `0 <= n < 9`. -/
def connectedGraphCounts : Fin 9 -> Nat :=
  ![1, 1, 1, 4, 38, 728, 26704, 1866256, 251548592]

/-- Total labelled graph counts `2^(choose n 2)` for `0 <= n < 9`. -/
def totalGraphCounts : Fin 9 -> Nat :=
  ![1, 1, 2, 8, 64, 1024, 32768, 2097152, 268435456]

/-- Connectivity probability, scaled by `10^6` and rounded down. -/
def connectivityPerMillion (n : Fin 9) : Nat :=
  (1000000 * connectedGraphCounts n) / totalGraphCounts n

/-- Table for the scaled connectivity probabilities above. -/
def connectivityPerMillionTable : Fin 9 -> Nat :=
  ![1000000, 1000000, 500000, 500000, 593750, 710937, 814941, 889900, 937091]

/-- Component counts of the empty graph: every vertex is isolated. -/
def emptyGraphComponentCounts : Fin 12 -> Nat :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Component counts of the complete graph: one component when `n > 0`. -/
def completeGraphComponentCounts : Fin 12 -> Nat :=
  ![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Numerators for expected isolated vertices in `G(n,1/2)`: `n / 2^(n-1)`. -/
def isolatedHalfNumerators : Fin 12 -> Nat :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Denominators for expected isolated vertices in `G(n,1/2)`: `n / 2^(n-1)`. -/
def isolatedHalfDenominators : Fin 12 -> Nat :=
  ![1, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

/-- Threshold code for the emergence of a giant component at mean degree `c = 1`. -/
def giantComponentSignal : Fin 8 -> Nat :=
  ![0, 0, 1, 1, 1, 1, 1, 1]

/-- Greedy chromatic upper bounds from sample maximum degrees `0 <= d < 10`. -/
def chromaticGreedyBounds : Fin 10 -> Nat :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem possible_edges_table_correct :
    (forall n : Fin 12, possibleEdges n = possibleEdgesTable n) := by
  native_decide

theorem critical_window_table_correct :
    (forall n : Fin 12,
      sparseThresholdTwiceExpectedEdges n 1 = criticalWindowTwiceEdgesTable n) := by
  native_decide

theorem total_graph_counts_correct :
    (forall n : Fin 9, totalGraphCounts n = 2 ^ possibleEdges n) := by
  native_decide

theorem connected_counts_bounded_by_total :
    (forall n : Fin 9, connectedGraphCounts n <= totalGraphCounts n) := by
  native_decide

theorem connectivity_probability_table_correct :
    (forall n : Fin 9, connectivityPerMillion n = connectivityPerMillionTable n) := by
  native_decide

theorem empty_and_complete_component_tables :
    (forall n : Fin 12,
      emptyGraphComponentCounts n = n
        ∧ completeGraphComponentCounts n = if (n : Nat) = 0 then 0 else 1) := by
  native_decide

theorem isolated_half_denominator_table_correct :
    (forall n : Fin 12,
      isolatedHalfNumerators n = n
        ∧ isolatedHalfDenominators n = if (n : Nat) = 0 then 1 else 2 ^ ((n : Nat) - 1)) := by
  native_decide

theorem isolated_vertices_drop_after_four :
    isolatedHalfNumerators 4 * isolatedHalfDenominators 8
        ≥ isolatedHalfNumerators 8 * isolatedHalfDenominators 4
      ∧ isolatedHalfNumerators 5 * isolatedHalfDenominators 10
        ≥ isolatedHalfNumerators 10 * isolatedHalfDenominators 5
      ∧ isolatedHalfNumerators 6 * isolatedHalfDenominators 11
        ≥ isolatedHalfNumerators 11 * isolatedHalfDenominators 6 := by
  native_decide

theorem giant_component_signal_threshold :
    (forall c : Fin 8, giantComponentSignal c = if (c : Nat) <= 1 then 0 else 1) := by
  native_decide

theorem chromatic_greedy_bounds_correct :
    (forall d : Fin 10, chromaticGreedyBounds d = (d : Nat) + 1) := by
  native_decide

end RandomGraphThresholds
