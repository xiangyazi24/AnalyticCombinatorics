import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.SeriesAcceleration


open Finset

/-!
# Series acceleration and transformation methods

Finite, decidable certificates for several transformations from Chapter V of
Flajolet and Sedgewick.  The statements below are numerical identities over
`Nat`, `Int`, and `Rat`; they deliberately avoid analytic limits.
-/

-- ============================================================
-- Section 1: Euler transform for alternating series
-- ============================================================

def alternatingPartial (a : Nat -> Rat) (N : Nat) : Rat :=
  ∑ n ∈ range N, (-1 : Rat) ^ n * a n

def forwardDifference : Nat -> (Nat -> Rat) -> Nat -> Rat
  | 0, a, n => a n
  | m + 1, a, n => forwardDifference m a n - forwardDifference m a (n + 1)

def eulerTerm (a : Nat -> Rat) (m : Nat) : Rat :=
  forwardDifference m a 0 / (2 : Rat) ^ (m + 1)

def eulerAcceleratedPartial (a : Nat -> Rat) (N : Nat) : Rat :=
  ∑ m ∈ range N, eulerTerm a m

def constantOneRat (n : Nat) : Rat := (n : Rat) - (n : Rat) + 1

def geometricHalf (n : Nat) : Rat := (1 / 2 : Rat) ^ n

theorem euler_grandi_accelerates_to_half :
    eulerAcceleratedPartial constantOneRat 1 = 1 / 2
      ∧ eulerAcceleratedPartial constantOneRat 2 = 1 / 2
      ∧ eulerAcceleratedPartial constantOneRat 5 = 1 / 2 := by
  native_decide

theorem euler_geometric_half_differences :
    (∀ m : Fin 6, forwardDifference m.val geometricHalf 0 = (1 / 2 : Rat) ^ m.val) := by
  native_decide

theorem euler_geometric_half_prefix :
    eulerAcceleratedPartial geometricHalf 1 = 1 / 2
      ∧ eulerAcceleratedPartial geometricHalf 2 = 5 / 8
      ∧ eulerAcceleratedPartial geometricHalf 3 = 21 / 32
      ∧ eulerAcceleratedPartial geometricHalf 4 = 85 / 128
      ∧ eulerAcceleratedPartial geometricHalf 5 = 341 / 512 := by
  native_decide

theorem alternating_geometric_half_prefix :
    alternatingPartial geometricHalf 1 = 1
      ∧ alternatingPartial geometricHalf 2 = 1 / 2
      ∧ alternatingPartial geometricHalf 3 = 3 / 4
      ∧ alternatingPartial geometricHalf 4 = 5 / 8
      ∧ alternatingPartial geometricHalf 5 = 11 / 16 := by
  native_decide

theorem euler_geometric_half_brackets_limit :
    eulerAcceleratedPartial geometricHalf 3 < 2 / 3
      ∧ eulerAcceleratedPartial geometricHalf 5 < 2 / 3
      ∧ 2 / 3 - eulerAcceleratedPartial geometricHalf 6 < 1 / 1000
      ∧ eulerAcceleratedPartial geometricHalf 6 = 1365 / 2048 := by
  native_decide

-- ============================================================
-- Section 2: Richardson extrapolation
-- ============================================================

def richardson (p : Nat) (full half : Rat) : Rat :=
  ((2 : Rat) ^ p * half - full) / ((2 : Rat) ^ p - 1)

def linearModel (L c h : Rat) : Rat :=
  L + c * h

def quadraticErrorModel (L c h : Rat) : Rat :=
  L + c * h ^ 2

def evenQuarticModel (L c d h : Rat) : Rat :=
  L + c * h ^ 2 + d * h ^ 4

theorem richardson_cancels_linear_error :
    richardson 1 (linearModel 3 10 1) (linearModel 3 10 (1 / 2)) = 3
      ∧ richardson 1 (linearModel (-4) 7 1) (linearModel (-4) 7 (1 / 2)) = -4 := by
  native_decide

theorem richardson_cancels_quadratic_error :
    richardson 2 (quadraticErrorModel 5 12 1) (quadraticErrorModel 5 12 (1 / 2)) = 5
      ∧ richardson 2 (quadraticErrorModel (-2) 9 1) (quadraticErrorModel (-2) 9 (1 / 2)) = -2 := by
  native_decide

def rombergStep (coarse fine : Rat) : Rat :=
  richardson 4 coarse fine

theorem richardson_romberg_small_polynomial_identity :
    let A := evenQuarticModel 5 3 8
    let R0 := richardson 2 (A 1) (A (1 / 2))
    let R1 := richardson 2 (A (1 / 2)) (A (1 / 4))
    R0 = 3 ∧ R1 = 39 / 8 ∧ rombergStep R0 R1 = 5 := by
  native_decide

-- ============================================================
-- Section 3: Aitken delta-squared acceleration
-- ============================================================

def delta (s : Nat -> Rat) (n : Nat) : Rat :=
  s (n + 1) - s n

def delta2 (s : Nat -> Rat) (n : Nat) : Rat :=
  s (n + 2) - 2 * s (n + 1) + s n

def aitken (s : Nat -> Rat) (n : Nat) : Rat :=
  s n - delta s n ^ 2 / delta2 s n

def linearConvergentSequence (n : Nat) : Rat :=
  2 + (1 / 2 : Rat) ^ n

theorem aitken_geometric_sequence_values :
    linearConvergentSequence 0 = 3
      ∧ linearConvergentSequence 1 = 5 / 2
      ∧ linearConvergentSequence 2 = 9 / 4
      ∧ linearConvergentSequence 3 = 17 / 8 := by
  native_decide

theorem aitken_delta_data :
    delta linearConvergentSequence 0 = -1 / 2
      ∧ delta linearConvergentSequence 1 = -1 / 4
      ∧ delta2 linearConvergentSequence 0 = 1 / 4
      ∧ delta2 linearConvergentSequence 1 = 1 / 8 := by
  native_decide

theorem aitken_removes_single_geometric_error :
    ∀ n : Fin 6, aitken linearConvergentSequence n.val = 2 := by
  native_decide

-- ============================================================
-- Section 4: Shanks transformation, 2 by 2 determinant case
-- ============================================================

def det2 (a b c d : Rat) : Rat :=
  a * d - b * c

def shanksNumerator1 (s : Nat -> Rat) (n : Nat) : Rat :=
  det2 (s n) (s (n + 1)) (s (n + 1)) (s (n + 2))

def shanksDenominator1 (s : Nat -> Rat) (n : Nat) : Rat :=
  det2 1 1 (delta s n) (delta s (n + 1))

def shanks1 (s : Nat -> Rat) (n : Nat) : Rat :=
  shanksNumerator1 s n / shanksDenominator1 s n

theorem shanks_small_hankel_ratio_data :
    shanksNumerator1 linearConvergentSequence 0 = 1 / 2
      ∧ shanksDenominator1 linearConvergentSequence 0 = 1 / 4
      ∧ shanks1 linearConvergentSequence 0 = 2
      ∧ shanks1 linearConvergentSequence 1 = 2 := by
  native_decide

theorem shanks_matches_aitken_small_prefix :
    ∀ n : Fin 5,
      shanks1 linearConvergentSequence n.val = aitken linearConvergentSequence n.val := by
  native_decide

-- ============================================================
-- Section 5: Signed binomial transform and inverse pair
-- ============================================================

def signedBinomialTransform (b : Nat -> Int) (n : Nat) : Int :=
  ∑ k ∈ range (n + 1), (Nat.choose n k : Int) * (-1 : Int) ^ k * b k

def powersTwoInt (n : Nat) : Int := (2 : Int) ^ n

def alternatingSignsInt (n : Nat) : Int := (-1 : Int) ^ n

def finiteBinomialMatrix3 : Fin 4 -> Fin 4 -> Int :=
  ![![1, 0, 0, 0],
    ![1, -1, 0, 0],
    ![1, -2, 1, 0],
    ![1, -3, 3, -1]]

theorem signed_binomial_matrix_rows :
    (∀ n : Fin 4, ∀ k : Fin 4,
      finiteBinomialMatrix3 n k =
        if k.val <= n.val then (Nat.choose n.val k.val : Int) * (-1 : Int) ^ k.val else 0) := by
  native_decide

theorem signed_binomial_transform_power_pair_forward :
    ∀ n : Fin 8, signedBinomialTransform powersTwoInt n.val = alternatingSignsInt n.val := by
  native_decide

theorem signed_binomial_transform_power_pair_inverse :
    ∀ n : Fin 8, signedBinomialTransform alternatingSignsInt n.val = powersTwoInt n.val := by
  native_decide

theorem signed_binomial_transform_delta_pair :
    signedBinomialTransform (fun _n => (1 : Int)) 0 = 1
      ∧ signedBinomialTransform (fun _n => (1 : Int)) 1 = 0
      ∧ signedBinomialTransform (fun _n => (1 : Int)) 2 = 0
      ∧ signedBinomialTransform (fun _n => (1 : Int)) 3 = 0
      ∧ signedBinomialTransform (fun n => if n = 0 then (1 : Int) else 0) 3 = 1 := by
  native_decide

-- ============================================================
-- Section 6: Cesaro summation for an oscillating sequence
-- ============================================================

def oscillatingSignsRat (n : Nat) : Rat := (-1 : Rat) ^ n

def cesaroMean (s : Nat -> Rat) (n : Nat) : Rat :=
  (∑ k ∈ range (n + 1), s k) / ((n + 1 : Nat) : Rat)

theorem cesaro_oscillating_initial_values :
    cesaroMean oscillatingSignsRat 0 = 1
      ∧ cesaroMean oscillatingSignsRat 1 = 0
      ∧ cesaroMean oscillatingSignsRat 2 = 1 / 3
      ∧ cesaroMean oscillatingSignsRat 3 = 0
      ∧ cesaroMean oscillatingSignsRat 4 = 1 / 5
      ∧ cesaroMean oscillatingSignsRat 5 = 0 := by
  native_decide

theorem cesaro_oscillating_small_near_zero :
    (-1 / 10 : Rat) < cesaroMean oscillatingSignsRat 9
      ∧ cesaroMean oscillatingSignsRat 9 < 1 / 10
      ∧ (-1 / 10 : Rat) < cesaroMean oscillatingSignsRat 10
      ∧ cesaroMean oscillatingSignsRat 10 < 1 / 10
      ∧ (-1 / 50 : Rat) < cesaroMean oscillatingSignsRat 99
      ∧ cesaroMean oscillatingSignsRat 99 < 1 / 50
      ∧ (-1 / 50 : Rat) < cesaroMean oscillatingSignsRat 100
      ∧ cesaroMean oscillatingSignsRat 100 < 1 / 50 := by
  native_decide

theorem cesaro_oscillating_even_odd_prefix :
    (∀ m : Fin 8, cesaroMean oscillatingSignsRat (2 * m.val + 1) = 0)
      ∧ (∀ m : Fin 8,
        cesaroMean oscillatingSignsRat (2 * m.val) =
          1 / ((2 * m.val + 1 : Nat) : Rat)) := by
  native_decide



structure SeriesAccelerationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SeriesAccelerationBudgetCertificate.controlled
    (c : SeriesAccelerationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SeriesAccelerationBudgetCertificate.budgetControlled
    (c : SeriesAccelerationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SeriesAccelerationBudgetCertificate.Ready
    (c : SeriesAccelerationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SeriesAccelerationBudgetCertificate.size
    (c : SeriesAccelerationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem seriesAcceleration_budgetCertificate_le_size
    (c : SeriesAccelerationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSeriesAccelerationBudgetCertificate :
    SeriesAccelerationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSeriesAccelerationBudgetCertificate.Ready := by
  constructor
  · norm_num [SeriesAccelerationBudgetCertificate.controlled,
      sampleSeriesAccelerationBudgetCertificate]
  · norm_num [SeriesAccelerationBudgetCertificate.budgetControlled,
      sampleSeriesAccelerationBudgetCertificate]

example :
    sampleSeriesAccelerationBudgetCertificate.certificateBudgetWindow ≤
      sampleSeriesAccelerationBudgetCertificate.size := by
  apply seriesAcceleration_budgetCertificate_le_size
  constructor
  · norm_num [SeriesAccelerationBudgetCertificate.controlled,
      sampleSeriesAccelerationBudgetCertificate]
  · norm_num [SeriesAccelerationBudgetCertificate.budgetControlled,
      sampleSeriesAccelerationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSeriesAccelerationBudgetCertificate.Ready := by
  constructor
  · norm_num [SeriesAccelerationBudgetCertificate.controlled,
      sampleSeriesAccelerationBudgetCertificate]
  · norm_num [SeriesAccelerationBudgetCertificate.budgetControlled,
      sampleSeriesAccelerationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSeriesAccelerationBudgetCertificate.certificateBudgetWindow ≤
      sampleSeriesAccelerationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SeriesAccelerationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSeriesAccelerationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSeriesAccelerationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.SeriesAcceleration
