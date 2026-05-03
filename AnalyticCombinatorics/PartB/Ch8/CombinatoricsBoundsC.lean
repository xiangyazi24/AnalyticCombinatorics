import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace CombinatoricsBoundsC

open Finset

/-!
# Combinatorial bounds from saddle-point and probabilistic methods

Small computable checks for the Markov, Chebyshev, Chernoff, birthday,
coupon-collector, and occupancy estimates appearing around Chapter VIII of
Analytic Combinatorics.
-/

-- Markov inequality instances: `P(X >= a) <= E[X] / a`.

def probabilityGE {n : ℕ} (prob : Fin n → Rat) (x : Fin n → ℕ) (a : ℕ) : Rat :=
  ∑ i : Fin n, if a ≤ x i then prob i else 0

def expectation {n : ℕ} (prob : Fin n → Rat) (x : Fin n → ℕ) : Rat :=
  ∑ i : Fin n, prob i * (x i : Rat)

def bernoulliQuarterProb : Fin 2 → Rat :=
  ![(3 : Rat) / 4, (1 : Rat) / 4]

def bernoulliValue : Fin 2 → ℕ :=
  ![0, 1]

def fairDieProb : Fin 6 → Rat :=
  ![(1 : Rat) / 6, (1 : Rat) / 6, (1 : Rat) / 6,
    (1 : Rat) / 6, (1 : Rat) / 6, (1 : Rat) / 6]

def fairDieValue : Fin 6 → ℕ :=
  ![1, 2, 3, 4, 5, 6]

def threePointProb : Fin 3 → Rat :=
  ![(1 : Rat) / 2, (1 : Rat) / 3, (1 : Rat) / 6]

def threePointValue : Fin 3 → ℕ :=
  ![0, 2, 5]

theorem bernoulliQuarter_prob_sum :
    (∑ i : Fin 2, bernoulliQuarterProb i) = 1 := by native_decide

theorem fairDie_prob_sum :
    (∑ i : Fin 6, fairDieProb i) = 1 := by native_decide

theorem threePoint_prob_sum :
    (∑ i : Fin 3, threePointProb i) = 1 := by native_decide

theorem markov_bernoulliQuarter_at_one :
    probabilityGE bernoulliQuarterProb bernoulliValue 1 ≤
      expectation bernoulliQuarterProb bernoulliValue / 1 := by native_decide

theorem markov_fairDie_at_four :
    probabilityGE fairDieProb fairDieValue 4 ≤
      expectation fairDieProb fairDieValue / 4 := by native_decide

theorem markov_threePoint_at_three :
    probabilityGE threePointProb threePointValue 3 ≤
      expectation threePointProb threePointValue / 3 := by native_decide

-- Binomial distribution: the mean is `n * p`.

def binomialMass (n : ℕ) (p : Rat) (k : ℕ) : Rat :=
  (Nat.choose n k : Rat) * p ^ k * (1 - p) ^ (n - k)

def binomialMean (n : ℕ) (p : Rat) : Rat :=
  ∑ k : Fin (n + 1), (k.val : Rat) * binomialMass n p k.val

def binomialTailProbability (n : ℕ) (p : Rat) (threshold : ℕ) : Rat :=
  ∑ k : Fin (n + 1), if threshold ≤ k.val then binomialMass n p k.val else 0

theorem binomialMean_ten_half :
    binomialMean 10 ((1 : Rat) / 2) = (10 : Rat) * ((1 : Rat) / 2) := by native_decide

theorem binomialMean_eight_quarter :
    binomialMean 8 ((1 : Rat) / 4) = (8 : Rat) * ((1 : Rat) / 4) := by native_decide

theorem binomialMean_six_third :
    binomialMean 6 ((1 : Rat) / 3) = (6 : Rat) * ((1 : Rat) / 3) := by native_decide

-- Chebyshev bound values: `P(|X - mu| >= k * sigma) <= 1 / k^2`.

def chebyshevRhs (k : ℕ) : Rat :=
  1 / ((k : Rat) ^ 2)

def chebyshevRhsTable : Fin 4 → Rat :=
  ![(1 : Rat) / 4, (1 : Rat) / 9, (1 : Rat) / 16, (1 : Rat) / 25]

theorem chebyshevRhs_table :
    (fun i : Fin 4 => chebyshevRhs (i.val + 2)) = chebyshevRhsTable := by native_decide

-- Chernoff-type binomial bound:
-- `P(X >= (1 + delta) * n * p) <= (e^delta / (1 + delta)^(1 + delta))^(n * p)`.

def eUpperApprox : Rat :=
  (68 : Rat) / 25

def chernoffThreshold (n : ℕ) (p : Rat) (delta : ℕ) : Rat :=
  (1 + (delta : Rat)) * (n : Rat) * p

def chernoffBaseApprox (delta : ℕ) : Rat :=
  eUpperApprox ^ delta / ((1 + (delta : Rat)) ^ (delta + 1))

def chernoffBoundApprox (mean : ℕ) (delta : ℕ) : Rat :=
  chernoffBaseApprox delta ^ mean

theorem chernoffThreshold_ten_half_delta_one :
    chernoffThreshold 10 ((1 : Rat) / 2) 1 = 10 := by native_decide

theorem chernoffBaseApprox_delta_one :
    chernoffBaseApprox 1 = (17 : Rat) / 25 := by native_decide

theorem chernoffFactor_ten_half_delta_one :
    chernoffBoundApprox 5 1 = ((17 : Rat) / 25) ^ 5 := by native_decide

theorem chernoffFactor_ten_half_delta_one_lt_one :
    chernoffBoundApprox 5 1 < 1 := by native_decide

theorem chernoffTail_ten_half_delta_one :
    binomialTailProbability 10 ((1 : Rat) / 2) 10 ≤ chernoffBoundApprox 5 1 := by native_decide

-- Birthday problem.  `Q(n, days)` is the no-collision probability.

def fallingFactorial (m n : ℕ) : ℕ :=
  (Finset.range n).prod (fun i => m - i)

def birthdayQPair (n days : ℕ) : ℕ × ℕ :=
  (fallingFactorial days n, days ^ n)

def birthdayQFactorialPair (n days : ℕ) : ℕ × ℕ :=
  (days.factorial / (days - n).factorial, days ^ n)

def birthdayQ (n days : ℕ) : Rat :=
  (fallingFactorial days n : Rat) / ((days : Rat) ^ n)

def birthdayCollisionProbability (n days : ℕ) : Rat :=
  1 - birthdayQ n days

def birthdayCollisionPair (n days : ℕ) : ℕ × ℕ :=
  let q := birthdayQPair n days
  (q.2 - q.1, q.2)

def birthdayQ365PairTable : Fin 10 → ℕ × ℕ :=
  ![(365, 365),
    (132860, 133225),
    (48228180, 48627125),
    (17458601160, 17748900625),
    (6302555018760, 6478348728125),
    (2268919806753600, 2364597285765625),
    (814542210624542400, 863078009304453125),
    (291606111403586179200, 315023473396125390625),
    (104103381771080265974400, 114983567789585767578125),
    (37060803910504574686886400, 41969002243198805166015625)]

def birthdayCollision365PairTable : Fin 10 → ℕ × ℕ :=
  ![(0, 365),
    (365, 133225),
    (398945, 48627125),
    (290299465, 17748900625),
    (175793709365, 6478348728125),
    (95677479012025, 2364597285765625),
    (48535798679910725, 863078009304453125),
    (23417361992539211425, 315023473396125390625),
    (10880186018505501603725, 114983567789585767578125),
    (4908198332694230479129225, 41969002243198805166015625)]

theorem birthdayQ365_pair_table :
    (fun i : Fin 10 => birthdayQPair (i.val + 1) 365) = birthdayQ365PairTable := by native_decide

theorem birthdayCollision365_pair_table :
    (fun i : Fin 10 => birthdayCollisionPair (i.val + 1) 365) =
      birthdayCollision365PairTable := by native_decide

theorem birthdayQ365_factorial_pair_small_table :
    (fun i : Fin 5 => birthdayQFactorialPair (i.val + 1) 365) =
      (fun i : Fin 5 => birthdayQPair (i.val + 1) 365) := by native_decide

theorem birthdayQ365_ten_reduced :
    birthdayQ 10 365 =
      (20307289813975109417472 : Rat) / 22996713557917153515625 := by native_decide

-- Coupon collector expectation and variance checks.

def harmonic (n : ℕ) : Rat :=
  ∑ i ∈ Finset.range n, 1 / ((i + 1 : ℕ) : Rat)

def squareHarmonic (n : ℕ) : Rat :=
  ∑ i ∈ Finset.range n, 1 / ((((i + 1 : ℕ) : Rat) ^ 2))

def couponCollectorExpected (n : ℕ) : Rat :=
  (n : Rat) * harmonic n

def couponCollectorVarianceExact (n : ℕ) : Rat :=
  (n : Rat) ^ 2 * squareHarmonic n - (n : Rat) * harmonic n

def couponCollectorVarianceApprox (n : ℕ) : Rat :=
  (n : Rat) ^ 2 * squareHarmonic n

def couponCollectorExpectedTable : Fin 8 → Rat :=
  ![1, 3, (11 : Rat) / 2, (25 : Rat) / 3,
    (137 : Rat) / 12, (147 : Rat) / 10, (363 : Rat) / 20, (761 : Rat) / 35]

def couponCollectorVarianceExactTable : Fin 8 → Rat :=
  ![0, 2, (27 : Rat) / 4, (130 : Rat) / 9,
    (3625 : Rat) / 144, (3899 : Rat) / 100,
    (201341 : Rat) / 3600, (838034 : Rat) / 11025]

def couponCollectorVarianceApproxTable : Fin 8 → Rat :=
  ![1, 5, (49 : Rat) / 4, (205 : Rat) / 9,
    (5269 : Rat) / 144, (5369 : Rat) / 100,
    (266681 : Rat) / 3600, (1077749 : Rat) / 11025]

theorem couponCollectorExpected_table :
    (fun i : Fin 8 => couponCollectorExpected (i.val + 1)) =
      couponCollectorExpectedTable := by native_decide

theorem couponCollectorVarianceExact_table :
    (fun i : Fin 8 => couponCollectorVarianceExact (i.val + 1)) =
      couponCollectorVarianceExactTable := by native_decide

theorem couponCollectorVarianceApprox_table :
    (fun i : Fin 8 => couponCollectorVarianceApprox (i.val + 1)) =
      couponCollectorVarianceApproxTable := by native_decide

theorem couponCollectorVarianceExact_le_approx_table :
    ∀ i : Fin 8,
      couponCollectorVarianceExact (i.val + 1) ≤ couponCollectorVarianceApprox (i.val + 1) := by native_decide

theorem couponCollectorVarianceApprox_upper_bound_table :
    ∀ i : Fin 8,
      couponCollectorVarianceApprox (i.val + 1) ≤
        ((i.val + 1 : ℕ) : Rat) ^ 2 * (2 - 1 / (((i.val + 1 : ℕ) : Rat))) := by native_decide

-- Occupancy: expected empty bins is `m * (1 - 1 / m)^n`.

def expectedEmptyBins (m n : ℕ) : Rat :=
  (m : Rat) * ((((m - 1 : ℕ) : Rat) / (m : Rat)) ^ n)

def occupancyPairs : Fin 5 → ℕ × ℕ :=
  ![(10, 10), (5, 5), (4, 8), (6, 3), (8, 4)]

def occupancyExpectedTable : Fin 5 → Rat :=
  ![(3486784401 : Rat) / 1000000000,
    (1024 : Rat) / 625,
    (6561 : Rat) / 16384,
    (125 : Rat) / 36,
    (2401 : Rat) / 512]

theorem occupancyExpected_table :
    (fun i : Fin 5 =>
      let pair := occupancyPairs i
      expectedEmptyBins pair.1 pair.2) = occupancyExpectedTable := by native_decide

theorem occupancyExpected_ten_ten_rational_check :
    expectedEmptyBins 10 10 = 10 * (((9 : Rat) / 10) ^ 10) := by native_decide

theorem occupancyExpected_ten_ten_value :
    expectedEmptyBins 10 10 = (3486784401 : Rat) / 1000000000 := by native_decide

end CombinatoricsBoundsC
