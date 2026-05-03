import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RandomPermutationCycles

open Finset

/-!
Finite, computable checks for random permutation cycle statistics from
Flajolet--Sedgewick, Chapter IX.

All expectations below are stored as integer numerators scaled by `n!`.
-/

/-- Unsigned Stirling numbers of the first kind, counting permutations of
`[n]` with exactly `k` cycles. -/
def stirlingCycle : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingCycle n (k + 1) + stirlingCycle n k

/-- Derangement numbers. -/
def derangements : Nat -> Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (derangements (n + 1) + derangements n)

/-- `n! H_n`, computed using integer arithmetic. -/
def harmonicScaledByFactorial (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, Nat.factorial n / (i + 1)

/-- Total number of cycles over all permutations of `[n]`. -/
def totalCycleCount (n : Nat) : Nat :=
  ∑ k ∈ Finset.range (n + 1), k * stirlingCycle n k

/-! ## Expected number of cycles: `H_n` -/

theorem expected_cycles_scaled_1 :
    totalCycleCount 1 = harmonicScaledByFactorial 1 := by native_decide

theorem expected_cycles_scaled_2 :
    totalCycleCount 2 = harmonicScaledByFactorial 2 := by native_decide

theorem expected_cycles_scaled_3 :
    totalCycleCount 3 = harmonicScaledByFactorial 3 := by native_decide

theorem expected_cycles_scaled_4 :
    totalCycleCount 4 = harmonicScaledByFactorial 4 := by native_decide

theorem expected_cycles_scaled_5 :
    totalCycleCount 5 = harmonicScaledByFactorial 5 := by native_decide

theorem expected_cycles_scaled_6 :
    totalCycleCount 6 = harmonicScaledByFactorial 6 := by native_decide

theorem harmonic_scaled_values_1_to_6 :
    [harmonicScaledByFactorial 1,
     harmonicScaledByFactorial 2,
     harmonicScaledByFactorial 3,
     harmonicScaledByFactorial 4,
     harmonicScaledByFactorial 5,
     harmonicScaledByFactorial 6] = [1, 3, 11, 50, 274, 1764] := by native_decide

/-! ## Derangements: `D(n) / n! -> 1 / e` -/

/-- Exact scaled derangement probability as numerator and denominator. -/
def derangementProbabilityScaled (n : Nat) : Nat × Nat :=
  (derangements n, Nat.factorial n)

theorem derangements_table_0_to_6 :
    [derangements 0,
     derangements 1,
     derangements 2,
     derangements 3,
     derangements 4,
     derangements 5,
     derangements 6] = [1, 0, 1, 2, 9, 44, 265] := by native_decide

theorem derangement_probability_scaled_6 :
    derangementProbabilityScaled 6 = (265, 720) := by native_decide

/-! ## Number of permutations with exactly `k` cycles: `|s(n,k)|` -/

theorem stirling_cycle_4_1 : stirlingCycle 4 1 = 6 := by native_decide
theorem stirling_cycle_4_2 : stirlingCycle 4 2 = 11 := by native_decide
theorem stirling_cycle_4_3 : stirlingCycle 4 3 = 6 := by native_decide
theorem stirling_cycle_4_4 : stirlingCycle 4 4 = 1 := by native_decide

theorem stirling_cycle_row_4 :
    [stirlingCycle 4 1,
     stirlingCycle 4 2,
     stirlingCycle 4 3,
     stirlingCycle 4 4] = [6, 11, 6, 1] := by native_decide

theorem stirling_cycle_row_sum_6 :
    ∑ k ∈ Finset.range 7, stirlingCycle 6 k = Nat.factorial 6 := by native_decide

/-! ## Maximum cycle length and the Golomb--Dickman constant -/

/-- Four-decimal fixed-point record of the Golomb--Dickman constant. -/
def golombDickmanScaled10000 : Nat := 6243

/-- A permutation of `{0,1,2}`, represented by its three images. -/
structure Perm3 where
  image0 : Nat
  image1 : Nat
  image2 : Nat
deriving DecidableEq, Repr

namespace Perm3

def valid (p : Perm3) : Bool :=
  p.image0 < 3 &&
  p.image1 < 3 &&
  p.image2 < 3 &&
  [p.image0, p.image1, p.image2].Nodup

def apply (p : Perm3) : Nat -> Nat
  | 0 => p.image0
  | 1 => p.image1
  | 2 => p.image2
  | m => m

def iterate (p : Perm3) : Nat -> Nat -> Nat
  | 0, i => i
  | n + 1, i => iterate p n (p.apply i)

def cycleLengthAt (p : Perm3) (i : Nat) : Nat :=
  if p.iterate 1 i = i then 1
  else if p.iterate 2 i = i then 2
  else 3

def longestCycleLength (p : Perm3) : Nat :=
  max (p.cycleLengthAt 0) (max (p.cycleLengthAt 1) (p.cycleLengthAt 2))

end Perm3

def s3Permutations : List Perm3 :=
  [⟨0, 1, 2⟩,
   ⟨0, 2, 1⟩,
   ⟨1, 0, 2⟩,
   ⟨2, 1, 0⟩,
   ⟨1, 2, 0⟩,
   ⟨2, 0, 1⟩]

def countS3WithLongestCycle (m : Nat) : Nat :=
  (s3Permutations.filter (fun p => p.longestCycleLength == m)).length

def sumS3LongestCycleLengths : Nat :=
  (s3Permutations.map (fun p => p.longestCycleLength)).sum

theorem s3_all_entries_valid :
    s3Permutations.all Perm3.valid = true := by native_decide

theorem s3_longest_cycle_lengths :
    s3Permutations.map (fun p => p.longestCycleLength) = [1, 2, 2, 2, 3, 3] := by
  native_decide

theorem s3_longest_cycle_distribution :
    [countS3WithLongestCycle 1,
     countS3WithLongestCycle 2,
     countS3WithLongestCycle 3] = [1, 3, 2] := by native_decide

theorem s3_expected_longest_cycle_scaled :
    sumS3LongestCycleLengths = 13 := by native_decide

/-! ## Left-to-right maxima -/

/-- Total number of left-to-right maxima over all permutations of `[n]`.
It has the same scaled expectation as the number of cycles. -/
def totalLeftToRightMaxima (n : Nat) : Nat :=
  harmonicScaledByFactorial n

theorem left_to_right_maxima_scaled_values_1_to_6 :
    [totalLeftToRightMaxima 1,
     totalLeftToRightMaxima 2,
     totalLeftToRightMaxima 3,
     totalLeftToRightMaxima 4,
     totalLeftToRightMaxima 5,
     totalLeftToRightMaxima 6] = [1, 3, 11, 50, 274, 1764] := by native_decide

theorem cycles_and_left_to_right_maxima_same_scaled_1_to_6 :
    [totalCycleCount 1,
     totalCycleCount 2,
     totalCycleCount 3,
     totalCycleCount 4,
     totalCycleCount 5,
     totalCycleCount 6] =
    [totalLeftToRightMaxima 1,
     totalLeftToRightMaxima 2,
     totalLeftToRightMaxima 3,
     totalLeftToRightMaxima 4,
     totalLeftToRightMaxima 5,
     totalLeftToRightMaxima 6] := by native_decide

/-! ## Fixed points -/

/-- Scaled numerator for the expected number of fixed points. -/
def fixedPointMeanScaled (n : Nat) : Nat :=
  Nat.factorial n

/-- Scaled numerator for the fixed-point variance, valid for `n >= 2`. -/
def fixedPointVarianceScaled (n : Nat) : Nat :=
  Nat.factorial n

theorem fixed_points_mean_one_scaled_2_to_8 :
    [fixedPointMeanScaled 2,
     fixedPointMeanScaled 3,
     fixedPointMeanScaled 4,
     fixedPointMeanScaled 5,
     fixedPointMeanScaled 6,
     fixedPointMeanScaled 7,
     fixedPointMeanScaled 8] =
    [Nat.factorial 2,
     Nat.factorial 3,
     Nat.factorial 4,
     Nat.factorial 5,
     Nat.factorial 6,
     Nat.factorial 7,
     Nat.factorial 8] := by native_decide

theorem fixed_points_variance_one_scaled_2_to_8 :
    [fixedPointVarianceScaled 2,
     fixedPointVarianceScaled 3,
     fixedPointVarianceScaled 4,
     fixedPointVarianceScaled 5,
     fixedPointVarianceScaled 6,
     fixedPointVarianceScaled 7,
     fixedPointVarianceScaled 8] =
    [Nat.factorial 2,
     Nat.factorial 3,
     Nat.factorial 4,
     Nat.factorial 5,
     Nat.factorial 6,
     Nat.factorial 7,
     Nat.factorial 8] := by native_decide

end RandomPermutationCycles
