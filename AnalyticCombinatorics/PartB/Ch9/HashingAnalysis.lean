import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.HashingAnalysis


open Finset

/-!
# Hashing and Birthday-Type Identities

Finite, decidable numerical checks for hashing and occupancy formulae from
balls-into-bins analysis.
-/

/-! ## Birthday problem -/

/-- Falling factorial `m (m-1) ... (m-n+1)`, the no-collision count. -/
def fallingFactorial (m n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (m - i)

/-- Total assignments of `n` balls to `m` urns. -/
def assignments (m n : ℕ) : ℕ :=
  m ^ n

/-- Probability that `n` balls in `m` urns have no collision. -/
def noCollisionProbability (m n : ℕ) : ℚ :=
  (fallingFactorial m n : ℚ) / (assignments m n : ℚ)

/-- Probability that `n` balls in `m` urns have at least one collision. -/
def collisionProbability (m n : ℕ) : ℚ :=
  1 - noCollisionProbability m n

example : fallingFactorial 365 2 = 132860 := by native_decide
example : assignments 365 2 = 133225 := by native_decide
example : noCollisionProbability 365 2 = 364 / 365 := by native_decide
example : collisionProbability 365 2 = 1 / 365 := by native_decide

example : fallingFactorial 10 4 = 5040 := by native_decide
example : assignments 10 4 = 10000 := by native_decide
example : noCollisionProbability 10 4 = 63 / 125 := by native_decide
example : collisionProbability 10 4 = 62 / 125 := by native_decide

example : fallingFactorial 365 23 =
    42200819302092359872395663074908957253749760700776448000000 := by
  native_decide
example : assignments 365 23 =
    85651679353150321236814267844395152689354622364044189453125 := by
  native_decide
example : 2 * fallingFactorial 365 22 > assignments 365 22 := by native_decide
example : 2 * fallingFactorial 365 23 < assignments 365 23 := by native_decide

/-! ## Coupon collector -/

/-- Harmonic number `H_n = 1 + 1/2 + ... + 1/n`, in rational arithmetic. -/
def harmonic (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1)

/-- Expected time to collect all `m` coupons: `m * H_m`. -/
def couponCollectorExpected (m : ℕ) : ℚ :=
  (m : ℚ) * harmonic m

example : harmonic 1 = 1 := by native_decide
example : harmonic 2 = 3 / 2 := by native_decide
example : harmonic 3 = 11 / 6 := by native_decide
example : harmonic 4 = 25 / 12 := by native_decide
example : harmonic 5 = 137 / 60 := by native_decide
example : harmonic 10 = 7381 / 2520 := by native_decide

example : couponCollectorExpected 1 = 1 := by native_decide
example : couponCollectorExpected 2 = 3 := by native_decide
example : couponCollectorExpected 3 = 11 / 2 := by native_decide
example : couponCollectorExpected 4 = 25 / 3 := by native_decide
example : couponCollectorExpected 5 = 137 / 12 := by native_decide
example : couponCollectorExpected 10 = 7381 / 252 := by native_decide
example : couponCollectorExpected 100 > 500 := by native_decide

/-! ## Linear probing -/

/-- Classical successful-search probe estimate for linear probing. -/
def successfulProbeLength (alpha : ℚ) : ℚ :=
  (1 + 1 / (1 - alpha)) / 2

/-- Classical unsuccessful-search probe estimate for linear probing. -/
def unsuccessfulProbeLength (alpha : ℚ) : ℚ :=
  (1 + 1 / (1 - alpha) ^ 2) / 2

example : successfulProbeLength (1 / 2) = 3 / 2 := by native_decide
example : unsuccessfulProbeLength (1 / 2) = 5 / 2 := by native_decide
example : successfulProbeLength (3 / 4) = 5 / 2 := by native_decide
example : unsuccessfulProbeLength (3 / 4) = 17 / 2 := by native_decide
example : successfulProbeLength (9 / 10) = 11 / 2 := by native_decide
example : unsuccessfulProbeLength (9 / 10) = 101 / 2 := by native_decide
example : unsuccessfulProbeLength (99 / 100) = 10001 / 2 := by native_decide
example : unsuccessfulProbeLength (3 / 4) / unsuccessfulProbeLength (1 / 2) =
    17 / 5 := by
  native_decide

/-! ## Expected number of empty bins -/

/-- Numerator of `m * (1 - 1/m)^n`, written as `m * (m-1)^n / m^n`. -/
def expectedEmptyNumerator (m n : ℕ) : ℕ :=
  m * (m - 1) ^ n

/-- Denominator of `m * (1 - 1/m)^n`, written as `m * (m-1)^n / m^n`. -/
def expectedEmptyDenominator (m n : ℕ) : ℕ :=
  m ^ n

/-- Expected number of empty bins after throwing `n` balls into `m` bins. -/
def expectedEmptyBins (m n : ℕ) : ℚ :=
  (m : ℚ) * (1 - 1 / (m : ℚ)) ^ n

example : expectedEmptyBins 4 0 = 4 := by native_decide
example : expectedEmptyBins 4 1 = 3 := by native_decide
example : expectedEmptyBins 4 2 = 9 / 4 := by native_decide
example : expectedEmptyBins 4 3 = 27 / 16 := by native_decide
example : expectedEmptyBins 5 2 = 16 / 5 := by native_decide

example : expectedEmptyNumerator 10 5 = 590490 := by native_decide
example : expectedEmptyDenominator 10 5 = 100000 := by native_decide
example : expectedEmptyBins 10 5 = 59049 / 10000 := by native_decide

example : expectedEmptyBins 10 10 = 3486784401 / 1000000000 := by
  native_decide
example : 348 / 100 < expectedEmptyBins 10 10 := by native_decide
example : expectedEmptyBins 10 10 < 349 / 100 := by native_decide

/-! ## Maximum load numerical bounds -/

/--
Union-bound numerator for the event that some bin has load at least `k`:
`m * choose n k / m^k`.
-/
def maxLoadUnionNumerator (m n k : ℕ) : ℕ :=
  m * Nat.choose n k

/-- Union-bound denominator for the maximum-load estimate. -/
def maxLoadUnionDenominator (m k : ℕ) : ℕ :=
  m ^ k

/-- Ceiling division used for deterministic pigeonhole lower loads. -/
def ceilDiv (n m : ℕ) : ℕ :=
  (n + m - 1) / m

example : ceilDiv 100 10 = 10 := by native_decide
example : ceilDiv 101 10 = 11 := by native_decide
example : ceilDiv 1000 64 = 16 := by native_decide

example : maxLoadUnionNumerator 100 100 7 = 1600756080000 := by
  native_decide
example : maxLoadUnionDenominator 100 7 = 100000000000000 := by
  native_decide
example :
    (maxLoadUnionNumerator 100 100 7 : ℚ) /
        maxLoadUnionDenominator 100 7 < 1 / 50 := by
  native_decide

example : maxLoadUnionNumerator 64 64 8 = 283274583552 := by native_decide
example : maxLoadUnionDenominator 64 8 = 281474976710656 := by native_decide
example :
    (maxLoadUnionNumerator 64 64 8 : ℚ) /
        maxLoadUnionDenominator 64 8 < 1 / 900 := by
  native_decide

/-! ## Hash table occupancy fractions -/

/-- Occupancy fraction of a hash table with `used` occupied slots out of `slots`. -/
def occupancyFraction (used slots : ℕ) : ℚ :=
  (used : ℚ) / (slots : ℚ)

/-- Empty fraction of a hash table with `used` occupied slots out of `slots`. -/
def emptyFraction (used slots : ℕ) : ℚ :=
  1 - occupancyFraction used slots

/-- Expected occupied slots after hashing `n` keys into `m` slots. -/
def expectedOccupiedBins (m n : ℕ) : ℚ :=
  (m : ℚ) - expectedEmptyBins m n

/-- Expected occupancy fraction after hashing `n` keys into `m` slots. -/
def expectedOccupancyFraction (m n : ℕ) : ℚ :=
  1 - (1 - 1 / (m : ℚ)) ^ n

example : occupancyFraction 50 100 = 1 / 2 := by native_decide
example : emptyFraction 50 100 = 1 / 2 := by native_decide
example : occupancyFraction 75 100 = 3 / 4 := by native_decide
example : emptyFraction 75 100 = 1 / 4 := by native_decide
example : occupancyFraction 90 100 = 9 / 10 := by native_decide
example : successfulProbeLength (occupancyFraction 75 100) = 5 / 2 := by
  native_decide
example : unsuccessfulProbeLength (occupancyFraction 75 100) = 17 / 2 := by
  native_decide

example : expectedOccupiedBins 10 10 = 6513215599 / 1000000000 := by
  native_decide
example : expectedOccupancyFraction 10 10 = 6513215599 / 10000000000 := by
  native_decide
example : 65 / 100 < expectedOccupancyFraction 10 10 := by native_decide
example : expectedOccupancyFraction 10 10 < 66 / 100 := by native_decide

/-- Expected empty-bin sample for ten balls in ten bins. -/
theorem expectedEmptyBins_ten_ten :
    expectedEmptyBins 10 10 = 3486784401 / 1000000000 := by
  native_decide

/-- Expected occupancy fraction sample for ten balls in ten bins. -/
theorem expectedOccupancyFraction_ten_ten :
    expectedOccupancyFraction 10 10 = 6513215599 / 10000000000 := by
  native_decide



structure HashingAnalysisBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HashingAnalysisBudgetCertificate.controlled
    (c : HashingAnalysisBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HashingAnalysisBudgetCertificate.budgetControlled
    (c : HashingAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HashingAnalysisBudgetCertificate.Ready
    (c : HashingAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HashingAnalysisBudgetCertificate.size
    (c : HashingAnalysisBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hashingAnalysis_budgetCertificate_le_size
    (c : HashingAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHashingAnalysisBudgetCertificate :
    HashingAnalysisBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHashingAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [HashingAnalysisBudgetCertificate.controlled,
      sampleHashingAnalysisBudgetCertificate]
  · norm_num [HashingAnalysisBudgetCertificate.budgetControlled,
      sampleHashingAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHashingAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleHashingAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHashingAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [HashingAnalysisBudgetCertificate.controlled,
      sampleHashingAnalysisBudgetCertificate]
  · norm_num [HashingAnalysisBudgetCertificate.budgetControlled,
      sampleHashingAnalysisBudgetCertificate]

example :
    sampleHashingAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleHashingAnalysisBudgetCertificate.size := by
  apply hashingAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [HashingAnalysisBudgetCertificate.controlled,
      sampleHashingAnalysisBudgetCertificate]
  · norm_num [HashingAnalysisBudgetCertificate.budgetControlled,
      sampleHashingAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HashingAnalysisBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHashingAnalysisBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHashingAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.HashingAnalysis
