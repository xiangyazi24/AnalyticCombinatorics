import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.RandomAllocationSchemes

open Finset Nat


/-!
  Analytic Combinatorics — Part B
  Chapter IX — Random Allocation Schemes.

  Numerical verifications for the balls-into-bins model:
  • Occupancy distributions and surjective allocations
  • Birthday problem and collision probabilities
  • Coupon collector expected time and variance
  • Bin occupancy statistics and Poisson approximation
  • Stirling–surjection correspondence
  • Threshold phenomena
-/

/-! ## 1. Basic allocation counts -/

/-- Total allocations of n distinguishable balls into m distinguishable bins. -/
def totalAllocations (m n : ℕ) : ℕ := m ^ n

theorem totalAllocations_3_2 : totalAllocations 3 2 = 9 := by native_decide
theorem totalAllocations_2_3 : totalAllocations 2 3 = 8 := by native_decide
theorem totalAllocations_10_0 : totalAllocations 10 0 = 1 := by native_decide

/-- Surjective allocations via inclusion–exclusion: n balls, all m bins non-empty. -/
def surjections (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1) ^ k * (m.choose k : ℤ) * ((m - k : ℤ)) ^ n

theorem surjections_2_2 : surjections 2 2 = 2 := by native_decide
theorem surjections_3_3 : surjections 3 3 = 6 := by native_decide
theorem surjections_3_4 : surjections 3 4 = 36 := by native_decide
theorem surjections_4_4 : surjections 4 4 = 24 := by native_decide

/-! ## 2. Birthday problem — collision probabilities -/

/-- Probability of no collision: n balls in m bins, all in distinct bins. -/
def noCollisionProb (m n : ℕ) : ℚ :=
  if n = 0 then 1
  else if n > m then 0
  else ∏ i ∈ Finset.range n, ((m - i : ℤ) : ℚ) / (m : ℚ)

/-- Probability of at least one collision. -/
def collisionProb (m n : ℕ) : ℚ := 1 - noCollisionProb m n

theorem noCollisionProb_365_1 : noCollisionProb 365 1 = 1 := by native_decide
theorem collisionProb_365_2 : collisionProb 365 2 = 1 / 365 := by native_decide
theorem noCollisionProb_4_3 : noCollisionProb 4 3 = 3 / 8 := by native_decide

theorem birthday_23_exceeds_half :
    collisionProb 365 23 > 1 / 2 := by native_decide

/-- Expected number of r-subsets sharing a common bin (m bins, n balls). -/
def expectedRCoincidences (m n r : ℕ) : ℚ :=
  (n.choose r : ℚ) / ((m : ℚ) ^ (r - 1))

theorem expectedPairCoincidences_365_23 :
    expectedRCoincidences 365 23 2 = 253 / 365 := by native_decide

/-! ## 3. Coupon collector -/

/-- Harmonic number H_n = ∑_{k=1}^{n} 1/k. -/
def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ)

theorem harmonicNumber_1 : harmonicNumber 1 = 1 := by native_decide
theorem harmonicNumber_3 : harmonicNumber 3 = 11 / 6 := by native_decide
theorem harmonicNumber_4 : harmonicNumber 4 = 25 / 12 := by native_decide

/-- Expected draws to collect all n coupon types: n · H_n. -/
def couponCollectorExpected (n : ℕ) : ℚ := (n : ℚ) * harmonicNumber n

theorem couponCollector_1 : couponCollectorExpected 1 = 1 := by native_decide
theorem couponCollector_2 : couponCollectorExpected 2 = 3 := by native_decide
theorem couponCollector_3 : couponCollectorExpected 3 = 11 / 2 := by native_decide

/-- Expected draws in phase k: transitioning from k−1 to k distinct coupons. -/
def couponPhaseExpected (n k : ℕ) : ℚ :=
  if k = 0 ∨ k > n then 0
  else (n : ℚ) / ((n - (k - 1) : ℤ) : ℚ)

theorem couponPhase_3_1 : couponPhaseExpected 3 1 = 1 := by native_decide
theorem couponPhase_3_2 : couponPhaseExpected 3 2 = 3 / 2 := by native_decide
theorem couponPhase_3_3 : couponPhaseExpected 3 3 = 3 := by native_decide

theorem couponCollector_sum_phases_3 :
    couponCollectorExpected 3 =
      couponPhaseExpected 3 1 + couponPhaseExpected 3 2 + couponPhaseExpected 3 3 := by
  native_decide

/-- Second-order harmonic number H_n^{(2)} = ∑_{k=1}^{n} 1/k². -/
def harmonicNumber2 (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / ((k + 1 : ℕ) : ℚ) ^ 2

theorem harmonicNumber2_1 : harmonicNumber2 1 = 1 := by native_decide
theorem harmonicNumber2_3 : harmonicNumber2 3 = 49 / 36 := by native_decide

/-- Variance of the coupon collector time: n² · H_n^{(2)} − n · H_n. -/
def couponCollectorVariance (n : ℕ) : ℚ :=
  (n : ℚ) ^ 2 * harmonicNumber2 n - (n : ℚ) * harmonicNumber n

theorem couponCollectorVariance_2 : couponCollectorVariance 2 = 2 := by native_decide
theorem couponCollectorVariance_3 : couponCollectorVariance 3 = 27 / 4 := by native_decide

/-! ## 4. Bin occupancy statistics -/

/-- Probability that a specific bin is empty: ((m−1)/m)^n. -/
def binEmptyProb (m n : ℕ) : ℚ :=
  ((m - 1 : ℤ) : ℚ) ^ n / ((m : ℚ) ^ n)

/-- Expected number of empty bins: m · P(bin empty). -/
def expectedEmptyBins (m n : ℕ) : ℚ :=
  (m : ℚ) * binEmptyProb m n

theorem expectedEmptyBins_4_1 : expectedEmptyBins 4 1 = 3 := by native_decide
theorem expectedEmptyBins_4_2 : expectedEmptyBins 4 2 = 9 / 4 := by native_decide
theorem expectedEmptyBins_10_0 : expectedEmptyBins 10 0 = 10 := by native_decide

/-- Probability that a specific bin has exactly j balls (binomial per-bin model). -/
def binLoadProb (m n j : ℕ) : ℚ :=
  (n.choose j : ℚ) * ((m - 1 : ℤ) : ℚ) ^ (n - j) / ((m : ℚ) ^ n)

/-- Expected number of bins with exactly j balls. -/
def expectedBinsWithLoad (m n j : ℕ) : ℚ :=
  (m : ℚ) * binLoadProb m n j

theorem binsWithLoad_zero_eq_empty :
    expectedBinsWithLoad 4 2 0 = expectedEmptyBins 4 2 := by native_decide

theorem expectedBinsWithLoad_4_2_1 : expectedBinsWithLoad 4 2 1 = 3 / 2 := by native_decide
theorem expectedBinsWithLoad_4_2_2 : expectedBinsWithLoad 4 2 2 = 1 / 4 := by native_decide

theorem bins_load_sum_4_2 :
    expectedBinsWithLoad 4 2 0 + expectedBinsWithLoad 4 2 1 +
    expectedBinsWithLoad 4 2 2 = 4 := by native_decide

/-! ## 5. Stirling numbers and the surjection correspondence -/

/-- Stirling number of the second kind S(n, k). -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide
theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide

theorem stirling_surjection_link :
    surjections 3 4 = (Nat.factorial 3 : ℤ) * (stirling2 4 3 : ℤ) := by native_decide

/-- Bell number B(n) = ∑_k S(n,k): total partitions of an n-set. -/
def bellNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bellNumber_4 : bellNumber 4 = 15 := by native_decide
theorem bellNumber_5 : bellNumber 5 = 52 := by native_decide

/-! ## 6. Multinomial allocation profiles -/

/-- Multinomial coefficient: n! / (k₁! · k₂! · ⋯ · k_r!). -/
def multinomial (n : ℕ) (ks : List ℕ) : ℕ :=
  Nat.factorial n / (ks.map Nat.factorial).prod

theorem multinomial_2_11 : multinomial 2 [1, 1] = 2 := by native_decide
theorem multinomial_4_211 : multinomial 4 [2, 1, 1] = 12 := by native_decide
theorem multinomial_6_222 : multinomial 6 [2, 2, 2] = 90 := by native_decide

/-! ## 7. Threshold phenomena -/

/-- Birthday threshold: ⌊√(2m)⌋ approximates the collision onset in m bins. -/
def birthdayThreshold (m : ℕ) : ℕ := Nat.sqrt (2 * m)

theorem birthdayThreshold_365 : birthdayThreshold 365 = 27 := by native_decide
theorem birthdayThreshold_1000 : birthdayThreshold 1000 = 44 := by native_decide

/-- Coupon-collector threshold: m · H_m draws to occupy all m bins. -/
def couponThreshold (m : ℕ) : ℚ := couponCollectorExpected m

theorem couponThreshold_4 : couponThreshold 4 = 25 / 3 := by native_decide
theorem couponThreshold_5 : couponThreshold 5 = 137 / 12 := by native_decide

/-! ## 8. Poisson approximation via truncated exponential -/

/-- Truncated exponential: ∑_{k=0}^{N} λ^k / k! (rational for integer λ). -/
def truncatedExp (lam N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), (lam : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem truncatedExp_1_3 : truncatedExp 1 3 = 8 / 3 := by native_decide
theorem truncatedExp_2_4 : truncatedExp 2 4 = 7 := by native_decide

/-- Poisson weight: λ^k / k! (unnormalized PMF term). -/
def poissonWeight (lam k : ℕ) : ℚ :=
  (lam : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem poissonWeight_1_0 : poissonWeight 1 0 = 1 := by native_decide
theorem poissonWeight_1_1 : poissonWeight 1 1 = 1 := by native_decide
theorem poissonWeight_2_3 : poissonWeight 2 3 = 4 / 3 := by native_decide

/-- Approximate Poisson(λ) PMF via truncation at N. -/
def poissonApproxPMF (lam k N : ℕ) : ℚ :=
  poissonWeight lam k / truncatedExp lam N

theorem poissonApproxPMF_1_0_3 :
    poissonApproxPMF 1 0 3 = 3 / 8 := by native_decide

theorem poissonApproxPMF_1_1_3 :
    poissonApproxPMF 1 1 3 = 3 / 8 := by native_decide

theorem poissonApprox_sum_1_3 :
    poissonApproxPMF 1 0 3 + poissonApproxPMF 1 1 3 +
    poissonApproxPMF 1 2 3 + poissonApproxPMF 1 3 3 = 1 := by native_decide



structure RandomAllocationSchemesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomAllocationSchemesBudgetCertificate.controlled
    (c : RandomAllocationSchemesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomAllocationSchemesBudgetCertificate.budgetControlled
    (c : RandomAllocationSchemesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomAllocationSchemesBudgetCertificate.Ready
    (c : RandomAllocationSchemesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomAllocationSchemesBudgetCertificate.size
    (c : RandomAllocationSchemesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomAllocationSchemes_budgetCertificate_le_size
    (c : RandomAllocationSchemesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomAllocationSchemesBudgetCertificate :
    RandomAllocationSchemesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomAllocationSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomAllocationSchemesBudgetCertificate.controlled,
      sampleRandomAllocationSchemesBudgetCertificate]
  · norm_num [RandomAllocationSchemesBudgetCertificate.budgetControlled,
      sampleRandomAllocationSchemesBudgetCertificate]

example :
    sampleRandomAllocationSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomAllocationSchemesBudgetCertificate.size := by
  apply randomAllocationSchemes_budgetCertificate_le_size
  constructor
  · norm_num [RandomAllocationSchemesBudgetCertificate.controlled,
      sampleRandomAllocationSchemesBudgetCertificate]
  · norm_num [RandomAllocationSchemesBudgetCertificate.budgetControlled,
      sampleRandomAllocationSchemesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomAllocationSchemesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomAllocationSchemesBudgetCertificate.controlled,
      sampleRandomAllocationSchemesBudgetCertificate]
  · norm_num [RandomAllocationSchemesBudgetCertificate.budgetControlled,
      sampleRandomAllocationSchemesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomAllocationSchemesBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomAllocationSchemesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RandomAllocationSchemesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomAllocationSchemesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomAllocationSchemesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.RandomAllocationSchemes
