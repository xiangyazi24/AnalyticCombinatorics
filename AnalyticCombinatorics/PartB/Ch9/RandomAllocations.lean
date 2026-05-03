import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RandomAllocations

/-!
# Random allocations

Numerical, decidable checks for standard random-allocation identities from
Flajolet--Sedgewick, Chapter IX.  The asymptotic statements are represented by
their finite numerical shadows: exact formulas, integer logarithmic scales, and
rational approximation windows.
-/

/-! ## 1. Balls into bins -/

/-- Number of allocations of `n` labelled balls into `m` labelled bins. -/
def allocations (n m : ℕ) : ℕ := m ^ n

/-- Expected number of empty bins: `m * (1 - 1/m)^n`. -/
def expectedEmptyBins (n m : ℕ) : ℚ :=
  (m : ℚ) * (1 - 1 / (m : ℚ)) ^ n

/-- The same expectation written over the common denominator `m^n`. -/
def expectedEmptyBinsNumerator (n m : ℕ) : ℕ :=
  m * (m - 1) ^ n

theorem allocations_small_values :
    allocations 0 5 = 1 ∧
    allocations 3 2 = 8 ∧
    allocations 4 3 = 81 ∧
    allocations 5 4 = 1024 := by
  native_decide

theorem expected_empty_bins_small_values :
    expectedEmptyBins 0 5 = 5 ∧
    expectedEmptyBins 3 2 = 1 / 4 ∧
    expectedEmptyBins 2 3 = 4 / 3 ∧
    expectedEmptyBins 3 4 = 27 / 16 := by
  native_decide

theorem expected_empty_bins_scaled_checks :
    expectedEmptyBins 3 2 =
      (expectedEmptyBinsNumerator 3 2 : ℚ) / allocations 3 2 ∧
    expectedEmptyBins 2 3 =
      (expectedEmptyBinsNumerator 2 3 : ℚ) / allocations 2 3 ∧
    expectedEmptyBins 3 4 =
      (expectedEmptyBinsNumerator 3 4 : ℚ) / allocations 3 4 := by
  native_decide

/-! ## 2. Maximum occupancy for the balanced case `n = m` -/

/-- Integer shadow of the scale `log n / log log n`, using base-2 logs. -/
def logLogLoadScale (n : ℕ) : ℕ :=
  Nat.log 2 n / Nat.log 2 (Nat.log 2 n)

/-- The balanced-allocation max-load scale, for `n` balls and `m` bins with `n = m`. -/
def balancedMaxLoadScale (n m : ℕ) : ℕ :=
  if n = m then logLogLoadScale n else 0

theorem max_load_loglog_structure :
    Nat.log 2 65536 = 16 ∧
    Nat.log 2 (Nat.log 2 65536) = 4 ∧
    balancedMaxLoadScale 65536 65536 = 4 ∧
    3 ≤ balancedMaxLoadScale 65536 65536 ∧
    balancedMaxLoadScale 65536 65536 ≤ 5 ∧
    balancedMaxLoadScale 1048576 1048576 = 5 := by
  native_decide

theorem max_load_balanced_only :
    balancedMaxLoadScale 1024 1024 = 3 ∧
    balancedMaxLoadScale 1024 512 = 0 := by
  native_decide

/-! ## 3. Birthday-paradox threshold -/

/-- Falling factorial `m * (m - 1) * ... * (m - n + 1)`. -/
def fallingFactorial (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (m - n) * fallingFactorial m n

/-- Integer threshold using the classical `sqrt(pi*m/2)` scale and `pi ~= 355/113`. -/
def birthdayPiHalfThreshold (m : ℕ) : ℕ :=
  Nat.sqrt ((355 * m) / (2 * 113))

theorem birthday_threshold_values :
    birthdayPiHalfThreshold 365 = 23 ∧
    birthdayPiHalfThreshold 1000 = 39 ∧
    birthdayPiHalfThreshold 10000 = 125 := by
  native_decide

theorem birthday_365_half_probability_check :
    365 ^ 22 < 2 * fallingFactorial 365 22 ∧
    2 * fallingFactorial 365 23 < 365 ^ 23 := by
  native_decide

/-! ## 4. Poisson approximation for one bin -/

/-- Exact binomial probability that one fixed bin has load `k`. -/
def binOccupancyProb (n m k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) *
    (1 / (m : ℚ)) ^ k *
    (1 - 1 / (m : ℚ)) ^ (n - k)

/-- A rational approximation to `Poisson(1)` mass, using `e^(-1) ~= 367879/1000000`. -/
def poissonUnitMassApprox (k : ℕ) : ℚ :=
  ((367879 : ℚ) / 1000000) / (Nat.factorial k : ℚ)

theorem binomial_poisson_large_m_windows :
    36 / 100 ≤ binOccupancyProb 100 100 0 ∧
    binOccupancyProb 100 100 0 ≤ 37 / 100 ∧
    36 / 100 ≤ poissonUnitMassApprox 0 ∧
    poissonUnitMassApprox 0 ≤ 37 / 100 ∧
    36 / 100 ≤ binOccupancyProb 100 100 1 ∧
    binOccupancyProb 100 100 1 ≤ 37 / 100 ∧
    36 / 100 ≤ poissonUnitMassApprox 1 ∧
    poissonUnitMassApprox 1 ≤ 37 / 100 ∧
    18 / 100 ≤ binOccupancyProb 100 100 2 ∧
    binOccupancyProb 100 100 2 ≤ 19 / 100 ∧
    18 / 100 ≤ poissonUnitMassApprox 2 ∧
    poissonUnitMassApprox 2 ≤ 19 / 100 := by
  native_decide

theorem binomial_poisson_close_checks :
    poissonUnitMassApprox 0 - binOccupancyProb 100 100 0 ≤ 1 / 100 ∧
    binOccupancyProb 100 100 1 - poissonUnitMassApprox 1 ≤ 1 / 100 ∧
    binOccupancyProb 100 100 2 - poissonUnitMassApprox 2 ≤ 1 / 100 := by
  native_decide

/-! ## 5. Random surjections -/

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of surjections from an `n`-set onto an `m`-set: `S(n,m) * m!`. -/
def surjectionCount (n m : ℕ) : ℕ :=
  stirling2 n m * Nat.factorial m

/-- Probability that a random map from `n` labelled balls to `m` bins is onto. -/
def randomSurjectionRatio (n m : ℕ) : ℚ :=
  (surjectionCount n m : ℚ) / (m : ℚ) ^ n

theorem stirling2_small_values :
    stirling2 3 2 = 3 ∧
    stirling2 4 2 = 7 ∧
    stirling2 4 3 = 6 ∧
    stirling2 5 3 = 25 := by
  native_decide

theorem random_surjection_ratio_checks :
    surjectionCount 3 2 = stirling2 3 2 * Nat.factorial 2 ∧
    randomSurjectionRatio 3 2 = 3 / 4 ∧
    randomSurjectionRatio 4 2 = 7 / 8 ∧
    randomSurjectionRatio 4 3 = 4 / 9 ∧
    randomSurjectionRatio 5 3 = 50 / 81 := by
  native_decide

/-! ## 6. Multinomial coefficients -/

/-- Product of factorials of the block sizes. -/
def factorialProduct : List ℕ → ℕ
  | [] => 1
  | k :: ks => Nat.factorial k * factorialProduct ks

/-- Multinomial coefficient `n! / (k_1! * ... * k_m!)`. -/
def multinomial (n : ℕ) (parts : List ℕ) : ℕ :=
  Nat.factorial n / factorialProduct parts

theorem multinomial_specific_partitions :
    multinomial 6 [2, 2, 2] = 90 ∧
    multinomial 6 [3, 2, 1] = 60 ∧
    multinomial 6 [4, 1, 1] = 30 ∧
    multinomial 5 [2, 1, 1, 1] = 60 := by
  native_decide

theorem multinomial_factorial_forms :
    Nat.factorial 6 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 2) = 90 ∧
    Nat.factorial 6 / (Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 60 ∧
    Nat.factorial 6 / (Nat.factorial 4 * Nat.factorial 1 * Nat.factorial 1) = 30 ∧
    Nat.factorial 5 /
        (Nat.factorial 2 * Nat.factorial 1 * Nat.factorial 1 * Nat.factorial 1) = 60 := by
  native_decide

end RandomAllocations
