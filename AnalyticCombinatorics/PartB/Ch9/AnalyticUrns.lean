import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticUrns

/-!
# Analytic urn models and Pólya-type processes

Finite, decidable checks for urn processes and occupancy formulas from
Flajolet--Sedgewick, Chapter IX.
-/

section PolyaUrn

/--
Expected number of black balls after `n` draws in a two-colour Polya urn that
starts with `a` black and `b` white balls and adds `c` balls of the drawn colour.
-/
def polyaExpectedBlackBalls (a b c n : ℕ) : ℚ :=
  (a : ℚ) + (c * n : ℚ) * (a : ℚ) / (a + b : ℚ)

/--
Expected black proportion after `n` draws in the same Pólya urn. The expectation
is invariant: it equals the initial black proportion `a/(a+b)`.
-/
def polyaExpectedBlackProportion (a b c n : ℕ) : ℚ :=
  polyaExpectedBlackBalls a b c n / (a + b + c * n : ℚ)

/-- Simple Pólya urn: one black, one white, and one extra ball of the drawn colour. -/
def simplePolyaExpectedBlackBalls (n : ℕ) : ℚ :=
  (n + 2 : ℚ) / 2

def simplePolyaExpectedBlackTable : Fin 4 → ℚ := ![1, 3 / 2, 2, 5 / 2]

theorem polya_expected_proportion_checks :
    polyaExpectedBlackProportion 2 3 1 0 = 2 / 5 ∧
    polyaExpectedBlackProportion 2 3 4 7 = 2 / 5 ∧
    polyaExpectedBlackBalls 2 3 4 7 = 66 / 5 := by native_decide

theorem simple_polya_expected_formula_checks :
    simplePolyaExpectedBlackBalls 0 = (0 + 2 : ℚ) / 2 ∧
    simplePolyaExpectedBlackBalls 1 = (1 + 2 : ℚ) / 2 ∧
    simplePolyaExpectedBlackBalls 2 = (2 + 2 : ℚ) / 2 ∧
    simplePolyaExpectedBlackBalls 3 = (3 + 2 : ℚ) / 2 := by native_decide

theorem simple_polya_expected_values :
    simplePolyaExpectedBlackBalls 0 = 1 ∧
    simplePolyaExpectedBlackBalls 1 = 3 / 2 ∧
    simplePolyaExpectedBlackBalls 2 = 2 ∧
    simplePolyaExpectedBlackBalls 3 = 5 / 2 := by native_decide

theorem simple_polya_expected_table_checks :
    simplePolyaExpectedBlackTable 0 = simplePolyaExpectedBlackBalls 0 ∧
    simplePolyaExpectedBlackTable 1 = simplePolyaExpectedBlackBalls 1 ∧
    simplePolyaExpectedBlackTable 2 = simplePolyaExpectedBlackBalls 2 ∧
    simplePolyaExpectedBlackTable 3 = simplePolyaExpectedBlackBalls 3 := by native_decide

end PolyaUrn

section EhrenfestUrn

/--
Ehrenfest transition probability from `i` balls in the first urn to `j` balls
in the first urn, with `n` total balls.
-/
def ehrenfestTransition (n i j : ℕ) : ℚ :=
  if j + 1 = i then
    (i : ℚ) / (n : ℚ)
  else if j = i + 1 then
    (n - i : ℚ) / (n : ℚ)
  else
    0

/-- Binomial stationary mass for the Ehrenfest chain. -/
def ehrenfestStationaryMass (n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) / (2 : ℚ) ^ n

/-- One stationarity equation for state `j`, summed over states `0..n`. -/
def ehrenfestStationaryRhs (n j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    ehrenfestStationaryMass n i * ehrenfestTransition n i j

def ehrenfestStationaryTable4 : Fin 5 → ℚ := ![1 / 16, 1 / 4, 3 / 8, 1 / 4, 1 / 16]

theorem ehrenfest_transition_probability_checks :
    ehrenfestTransition 4 0 1 = 1 ∧
    ehrenfestTransition 4 1 0 = 1 / 4 ∧
    ehrenfestTransition 4 1 2 = 3 / 4 ∧
    ehrenfestTransition 4 2 1 = 1 / 2 ∧
    ehrenfestTransition 4 2 3 = 1 / 2 ∧
    ehrenfestTransition 4 4 3 = 1 ∧
    ehrenfestTransition 4 2 2 = 0 := by native_decide

theorem ehrenfest_stationary_distribution_n4_table :
    ehrenfestStationaryTable4 0 = ehrenfestStationaryMass 4 0 ∧
    ehrenfestStationaryTable4 1 = ehrenfestStationaryMass 4 1 ∧
    ehrenfestStationaryTable4 2 = ehrenfestStationaryMass 4 2 ∧
    ehrenfestStationaryTable4 3 = ehrenfestStationaryMass 4 3 ∧
    ehrenfestStationaryTable4 4 = ehrenfestStationaryMass 4 4 := by native_decide

theorem ehrenfest_stationary_distribution_n4 :
    ehrenfestStationaryMass 4 0 = 1 / 16 ∧
    ehrenfestStationaryMass 4 1 = 4 / 16 ∧
    ehrenfestStationaryMass 4 2 = 6 / 16 ∧
    ehrenfestStationaryMass 4 3 = 4 / 16 ∧
    ehrenfestStationaryMass 4 4 = 1 / 16 := by native_decide

theorem ehrenfest_stationarity_n4 :
    ehrenfestStationaryRhs 4 0 = ehrenfestStationaryMass 4 0 ∧
    ehrenfestStationaryRhs 4 1 = ehrenfestStationaryMass 4 1 ∧
    ehrenfestStationaryRhs 4 2 = ehrenfestStationaryMass 4 2 ∧
    ehrenfestStationaryRhs 4 3 = ehrenfestStationaryMass 4 3 ∧
    ehrenfestStationaryRhs 4 4 = ehrenfestStationaryMass 4 4 := by native_decide

end EhrenfestUrn

section Occupancy

/-- Probability that a fixed bin is empty when `n` balls are allocated to `m` bins. -/
def occupancyBinEmptyProb (m n : ℕ) : ℚ :=
  ((m - 1 : ℕ) : ℚ) ^ n / (m : ℚ) ^ n

/-- Expected number of occupied bins. -/
def expectedOccupiedBins (m n : ℕ) : ℚ :=
  (m : ℚ) * (1 - occupancyBinEmptyProb m n)

def expectedOccupiedBinsM10Table : Fin 10 → ℚ :=
  ![1, 19 / 10, 271 / 100, 3439 / 1000, 40951 / 10000,
    468559 / 100000, 5217031 / 1000000, 56953279 / 10000000,
    612579511 / 100000000, 6513215599 / 1000000000]

theorem occupancy_empty_probability_checks :
    occupancyBinEmptyProb 10 0 = 1 ∧
    occupancyBinEmptyProb 10 1 = 9 / 10 ∧
    occupancyBinEmptyProb 10 2 = 81 / 100 ∧
    occupancyBinEmptyProb 10 3 = 729 / 1000 := by native_decide

theorem expected_occupied_bins_m10_values :
    expectedOccupiedBins 10 1 = 1 ∧
    expectedOccupiedBins 10 2 = 19 / 10 ∧
    expectedOccupiedBins 10 3 = 271 / 100 ∧
    expectedOccupiedBins 10 4 = 3439 / 1000 ∧
    expectedOccupiedBins 10 5 = 40951 / 10000 ∧
    expectedOccupiedBins 10 6 = 468559 / 100000 ∧
    expectedOccupiedBins 10 7 = 5217031 / 1000000 ∧
    expectedOccupiedBins 10 8 = 56953279 / 10000000 ∧
    expectedOccupiedBins 10 9 = 612579511 / 100000000 ∧
    expectedOccupiedBins 10 10 = 6513215599 / 1000000000 := by native_decide

theorem expected_occupied_bins_m10_table_checks :
    expectedOccupiedBinsM10Table 0 = expectedOccupiedBins 10 1 ∧
    expectedOccupiedBinsM10Table 1 = expectedOccupiedBins 10 2 ∧
    expectedOccupiedBinsM10Table 2 = expectedOccupiedBins 10 3 ∧
    expectedOccupiedBinsM10Table 3 = expectedOccupiedBins 10 4 ∧
    expectedOccupiedBinsM10Table 4 = expectedOccupiedBins 10 5 ∧
    expectedOccupiedBinsM10Table 5 = expectedOccupiedBins 10 6 ∧
    expectedOccupiedBinsM10Table 6 = expectedOccupiedBins 10 7 ∧
    expectedOccupiedBinsM10Table 7 = expectedOccupiedBins 10 8 ∧
    expectedOccupiedBinsM10Table 8 = expectedOccupiedBins 10 9 ∧
    expectedOccupiedBinsM10Table 9 = expectedOccupiedBins 10 10 := by native_decide

end Occupancy

section MaximumLoad

/--
Integer proxy for the balanced maximum load scale
`log n / log (log n)`, using base-2 natural-number logarithms.
-/
def maximumLoadLogLogScale (n : ℕ) : ℕ :=
  Nat.log 2 n / Nat.log 2 (Nat.log 2 n)

theorem maximum_load_loglog_scale_checks :
    Nat.log 2 65536 = 16 ∧
    Nat.log 2 (Nat.log 2 65536) = 4 ∧
    maximumLoadLogLogScale 65536 = 4 ∧
    maximumLoadLogLogScale 1048576 = 5 := by native_decide

end MaximumLoad

section MultinomialCoefficients

/-- Product of factorials of the parts. -/
def factorialProduct : List ℕ → ℕ
  | [] => 1
  | k :: ks => Nat.factorial k * factorialProduct ks

/-- Multinomial coefficient `n!/(k_1! k_2! ... k_m!)`. -/
def multinomialCoefficient (n : ℕ) (parts : List ℕ) : ℕ :=
  Nat.factorial n / factorialProduct parts

def multinomialPartitionTable : Fin 4 → ℕ := ![90, 60, 1, 720]

theorem multinomial_specific_partition_values :
    multinomialCoefficient 6 [2, 2, 2] = 90 ∧
    multinomialCoefficient 6 [3, 2, 1] = 60 ∧
    multinomialCoefficient 6 [6] = 1 ∧
    multinomialCoefficient 6 [1, 1, 1, 1, 1, 1] = 720 := by native_decide

theorem multinomial_factorial_formula_checks :
    Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 ∧
    Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 60 ∧
    Nat.factorial 6 / Nat.factorial 6 = 1 ∧
    Nat.factorial 6 /
        (Nat.factorial 1 * Nat.factorial 1 * Nat.factorial 1 *
          Nat.factorial 1 * Nat.factorial 1 * Nat.factorial 1) = 720 := by native_decide

theorem multinomial_partition_table_checks :
    multinomialPartitionTable 0 = multinomialCoefficient 6 [2, 2, 2] ∧
    multinomialPartitionTable 1 = multinomialCoefficient 6 [3, 2, 1] ∧
    multinomialPartitionTable 2 = multinomialCoefficient 6 [6] ∧
    multinomialPartitionTable 3 = multinomialCoefficient 6 [1, 1, 1, 1, 1, 1] := by native_decide

end MultinomialCoefficients

end AnalyticUrns
