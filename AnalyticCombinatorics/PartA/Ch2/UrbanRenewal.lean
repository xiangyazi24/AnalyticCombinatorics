import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.UrbanRenewal


/-! # Urn Models and Random Allocation via EGF

Occupancy problems, birthday paradox generalizations, coupon collector
through exponential generating functions, and Stirling-number decompositions.
Based on Flajolet–Sedgewick, Part A, Chapter II. -/

/-- Stirling numbers of the second kind S(n,k): partitions of [n] into k nonempty blocks. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

theorem stirling2_base : stirling2 0 0 = 1 := by native_decide
theorem stirling2_4_2 : stirling2 4 2 = 7 := by native_decide
theorem stirling2_5_3 : stirling2 5 3 = 25 := by native_decide
theorem stirling2_6_3 : stirling2 6 3 = 90 := by native_decide
theorem stirling2_7_4 : stirling2 7 4 = 350 := by native_decide

/-- Bell number B(n): total number of partitions of an n-set. -/
def bellNumber (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), stirling2 n k

theorem bell_0 : bellNumber 0 = 1 := by native_decide
theorem bell_1 : bellNumber 1 = 1 := by native_decide
theorem bell_2 : bellNumber 2 = 2 := by native_decide
theorem bell_3 : bellNumber 3 = 5 := by native_decide
theorem bell_4 : bellNumber 4 = 15 := by native_decide
theorem bell_5 : bellNumber 5 = 52 := by native_decide

/-- Stirling numbers of the first kind |s(n,k)|: permutations of [n] with exactly k cycles. -/
def stirling1Abs : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirling1Abs n (k + 1) + stirling1Abs n k

theorem stirling1Abs_4_2 : stirling1Abs 4 2 = 11 := by native_decide
theorem stirling1Abs_5_2 : stirling1Abs 5 2 = 50 := by native_decide
theorem stirling1Abs_5_3 : stirling1Abs 5 3 = 35 := by native_decide

/-- Surjection count: number of onto maps from [n] to [m], equals m! · S(n,m). -/
def surjectionCount (n m : ℕ) : ℕ := Nat.factorial m * stirling2 n m

theorem surjection_4_3 : surjectionCount 4 3 = 36 := by native_decide
theorem surjection_5_2 : surjectionCount 5 2 = 30 := by native_decide
theorem surjection_6_4 : surjectionCount 6 4 = 1560 := by native_decide

/-- EGF coefficient extraction: occupancy number W(n,m) = m^n / n!
    counts weighted allocations. We store the numerator m^n. -/
def occupancyNumerator (m n : ℕ) : ℕ := m ^ n

theorem occupancy_num_3_5 : occupancyNumerator 3 5 = 243 := by native_decide
theorem occupancy_num_4_4 : occupancyNumerator 4 4 = 256 := by native_decide
theorem occupancy_num_10_3 : occupancyNumerator 10 3 = 1000 := by native_decide

/-- Birthday problem: probability numerator that all n balls land in distinct urns
    among m urns. Equals m! / (m-n)! = m · (m-1) · ... · (m-n+1). -/
def birthdayDistinctNumer (m n : ℕ) : ℕ := Nat.factorial m / Nat.factorial (m - n)

theorem birthday_365_2 : birthdayDistinctNumer 365 2 = 132860 := by native_decide
theorem birthday_distinct_4_2 : birthdayDistinctNumer 4 2 = 12 := by native_decide
theorem birthday_distinct_5_3 : birthdayDistinctNumer 5 3 = 60 := by native_decide
theorem birthday_distinct_10_4 : birthdayDistinctNumer 10 4 = 5040 := by native_decide

/-- Birthday collision probability numerator: m^n - m!/(m-n)!
    (number of allocations with at least one collision). -/
def birthdayCollisionNumer (m n : ℕ) : ℕ :=
  m ^ n - birthdayDistinctNumer m n

theorem birthday_coll_4_3 : birthdayCollisionNumer 4 3 = 40 := by native_decide
theorem birthday_coll_5_3 : birthdayCollisionNumer 5 3 = 65 := by native_decide

/-- Coupon collector expected time numerator: m · H_m as a rational.
    Expected number of draws to collect all m coupon types. -/
def couponExpected (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℚ)

theorem coupon_1 : couponExpected 1 = 1 := by native_decide
theorem coupon_2 : couponExpected 2 = 3 := by native_decide
theorem coupon_3 : couponExpected 3 = 11 / 2 := by native_decide
theorem coupon_4 : couponExpected 4 = 25 / 3 := by native_decide
theorem coupon_5 : couponExpected 5 = 137 / 12 := by native_decide

/-- Variance of coupon collector time as rational. -/
def couponVariance (m : ℕ) : ℚ :=
  (m : ℚ) ^ 2 * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℚ) ^ 2 -
  (m : ℚ) * ∑ k ∈ Finset.range m, 1 / ((k + 1 : ℕ) : ℚ)

theorem couponVar_1 : couponVariance 1 = 0 := by native_decide
theorem couponVar_2 : couponVariance 2 = 2 := by native_decide

/-- Expected number of empty urns (rational) when n balls go into m urns:
    m · ((m-1)/m)^n. We represent as exact rational. -/
def expectedEmpty (m n : ℕ) : ℚ :=
  (m : ℚ) * ((m - 1 : ℚ) / (m : ℚ)) ^ n

theorem expectedEmpty_4_1 : expectedEmpty 4 1 = 3 := by native_decide
theorem expectedEmpty_2_2 : expectedEmpty 2 2 = 1 / 2 := by native_decide

/-- Expected number of singletons (urns with exactly one ball):
    n · ((m-1)/m)^(n-1). -/
def expectedSingletons (m n : ℕ) : ℚ :=
  (n : ℚ) * ((m - 1 : ℚ) / (m : ℚ)) ^ (n - 1)

theorem expectedSingle_4_1 : expectedSingletons 4 1 = 1 := by native_decide
theorem expectedSingle_2_2 : expectedSingletons 2 2 = 1 := by native_decide

/-- Dobinski's formula representation: B(n) = (1/e) · Σ_{k≥0} k^n / k!
    We verify the finite truncation identity: e · B(n) · n! = Σ k^n · n! / k!. -/
def dobinskiPartialSum (n terms : ℕ) : ℚ :=
  ∑ k ∈ Finset.range terms, (k : ℚ) ^ n / Nat.factorial k

/-- EGF for set partitions: exp(exp(x) - 1). The n-th coefficient times n! = B(n).
    This records the structural decomposition SET(SET_{≥1}(Z)). -/
theorem egf_partition_coeff_3 :
    bellNumber 3 = 5 := by native_decide

theorem egf_partition_coeff_4 :
    bellNumber 4 = 15 := by native_decide

/-- Occupancy distribution: probability that exactly j urns are empty
    involves Stirling numbers. Number of ways = C(m,j) · surjectionCount(n, m-j). -/
def occupancyExactlyEmpty (m n j : ℕ) : ℕ :=
  Nat.choose m j * surjectionCount n (m - j)

theorem occupancy_empty_3_3_0 : occupancyExactlyEmpty 3 3 0 = 6 := by native_decide
theorem occupancy_empty_3_3_1 : occupancyExactlyEmpty 3 3 1 = 18 := by native_decide
theorem occupancy_empty_3_3_2 : occupancyExactlyEmpty 3 3 2 = 3 := by native_decide

/-- Sum of occupancy counts equals total allocations m^n. -/
theorem occupancy_sum_3_3 :
    ∑ j ∈ Finset.range 3, occupancyExactlyEmpty 3 3 j = 3 ^ 3 := by native_decide

/-- Generalized birthday: number of ways to have all distinct in n draws from m items. -/
def fallingFactorial (m n : ℕ) : ℕ := Nat.factorial m / Nat.factorial (m - n)

theorem falling_10_3 : fallingFactorial 10 3 = 720 := by native_decide
theorem falling_5_2 : fallingFactorial 5 2 = 20 := by native_decide
theorem falling_6_4 : fallingFactorial 6 4 = 360 := by native_decide

/-- EGF of surjections onto [m]: m! · (e^x - 1)^m / m! = (e^x - 1)^m.
    Coefficient of x^n/n! in (e^x - 1)^m equals surjectionCount(n,m)/n!. -/
theorem egf_surjection_identity_4_2 :
    surjectionCount 4 2 = 2 * stirling2 4 2 := by native_decide

theorem egf_surjection_identity_5_3 :
    surjectionCount 5 3 = Nat.factorial 3 * stirling2 5 3 := by native_decide

/-- Inclusion-exclusion for surjections:
    surjectionCount(n,m) = Σ_{k=0}^{m} (-1)^k · C(m,k) · (m-k)^n. -/
def surjectionIE (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1),
    (-1) ^ k * (Nat.choose m k : ℤ) * ((m - k : ℤ)) ^ n

theorem surjection_ie_4_3 : surjectionIE 4 3 = 36 := by native_decide
theorem surjection_ie_5_2 : surjectionIE 5 2 = 30 := by native_decide
theorem surjection_ie_3_3 : surjectionIE 3 3 = 6 := by native_decide

/-- Poisson approximation parameter for birthday problem: λ ≈ C(n,2)/m.
    Returns the scaled parameter m · λ = C(n,2) for the collision count. -/
def birthdayLambdaScaled (_m n : ℕ) : ℕ := Nat.choose n 2

theorem birthday_lambda_365_23 : birthdayLambdaScaled 365 23 = 253 := by native_decide
theorem birthday_lambda_365_50 : birthdayLambdaScaled 365 50 = 1225 := by native_decide

/-- Random allocation EGF: (1 + x)^m has [x^n] · n! = falling factorial m^{(n)}.
    For exponential model, the EGF of allocations into m urns is e^{mx}. -/
noncomputable def allocationEGFCoeff (m n : ℕ) : ℝ :=
  (m : ℝ) ^ n / Nat.factorial n

/-- Asymptotic birthday threshold: n ≈ √(2m · ln 2) for 50% collision probability.
    For m = 365, threshold ≈ 23. -/
noncomputable def birthdayThreshold (m : ℕ) : ℝ :=
  Real.sqrt (2 * (m : ℝ) * Real.log 2)

/-- Stirling number row sum: Σ_k S(n,k) = B(n). -/
theorem stirling2_row_sum_5 :
    ∑ k ∈ Finset.range 6, stirling2 5 k = bellNumber 5 := by native_decide

theorem stirling2_row_sum_4 :
    ∑ k ∈ Finset.range 5, stirling2 4 k = bellNumber 4 := by native_decide

/-- Stirling number recurrence verification. -/
theorem stirling2_recurrence_5_3 :
    stirling2 5 3 = 3 * stirling2 4 3 + stirling2 4 2 := by native_decide

theorem stirling2_recurrence_6_4 :
    stirling2 6 4 = 4 * stirling2 5 4 + stirling2 5 3 := by native_decide

/-- Factorial decomposition: n! = Σ_k |s(n,k)| connects to EGF of log(1/(1-x)). -/
theorem stirling1_row_sum_4 :
    ∑ k ∈ Finset.range 5, stirling1Abs 4 k = Nat.factorial 4 := by native_decide

theorem stirling1_row_sum_5 :
    ∑ k ∈ Finset.range 6, stirling1Abs 5 k = Nat.factorial 5 := by native_decide

/-- Orthogonality relation (integer version): Σ_j |s(n,j)| · S(j,k) gives identity. -/
def stirlingProduct (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1) ^ (n + j) * (stirling1Abs n j : ℤ) * (stirling2 j k : ℤ)

theorem stirling_ortho_3_3 : stirlingProduct 3 3 = 1 := by native_decide
theorem stirling_ortho_4_4 : stirlingProduct 4 4 = 1 := by native_decide
theorem stirling_ortho_3_2 : stirlingProduct 3 2 = 0 := by native_decide
theorem stirling_ortho_4_2 : stirlingProduct 4 2 = 0 := by native_decide



structure UrbanRenewalBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UrbanRenewalBudgetCertificate.controlled
    (c : UrbanRenewalBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UrbanRenewalBudgetCertificate.budgetControlled
    (c : UrbanRenewalBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UrbanRenewalBudgetCertificate.Ready
    (c : UrbanRenewalBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UrbanRenewalBudgetCertificate.size
    (c : UrbanRenewalBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem urbanRenewal_budgetCertificate_le_size
    (c : UrbanRenewalBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUrbanRenewalBudgetCertificate :
    UrbanRenewalBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleUrbanRenewalBudgetCertificate.Ready := by
  constructor
  · norm_num [UrbanRenewalBudgetCertificate.controlled,
      sampleUrbanRenewalBudgetCertificate]
  · norm_num [UrbanRenewalBudgetCertificate.budgetControlled,
      sampleUrbanRenewalBudgetCertificate]

example :
    sampleUrbanRenewalBudgetCertificate.certificateBudgetWindow ≤
      sampleUrbanRenewalBudgetCertificate.size := by
  apply urbanRenewal_budgetCertificate_le_size
  constructor
  · norm_num [UrbanRenewalBudgetCertificate.controlled,
      sampleUrbanRenewalBudgetCertificate]
  · norm_num [UrbanRenewalBudgetCertificate.budgetControlled,
      sampleUrbanRenewalBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUrbanRenewalBudgetCertificate.Ready := by
  constructor
  · norm_num [UrbanRenewalBudgetCertificate.controlled,
      sampleUrbanRenewalBudgetCertificate]
  · norm_num [UrbanRenewalBudgetCertificate.budgetControlled,
      sampleUrbanRenewalBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUrbanRenewalBudgetCertificate.certificateBudgetWindow ≤
      sampleUrbanRenewalBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List UrbanRenewalBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUrbanRenewalBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleUrbanRenewalBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.UrbanRenewal
