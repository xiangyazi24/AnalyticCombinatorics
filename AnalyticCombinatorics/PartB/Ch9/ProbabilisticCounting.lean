import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.ProbabilisticCounting

/-! # Ch IX -- Probabilistic counting and cardinality estimation

Finite computable checks for bit-pattern probabilities, geometric tails,
Flajolet-Martin/LogLog-style estimates, birthday thresholds, and
inclusion-exclusion identities.
-/


/-! ## 1. HyperLogLog-style bit patterns -/

/-- Powers of two used as denominators for leftmost-one bit probabilities. -/
def pow2Table : Fin 12 -> Nat :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

/-- The table entries are `2^k`. -/
theorem pow2Table_eq_pow :
    forall k : Fin 12, pow2Table k = 2 ^ k.val := by native_decide

/-- `P(leftmost 1 at position k) = 1 / 2^k`, with positions starting at `1`. -/
def leftmostOneProbability (k : Nat) : Rat :=
  1 / ((2 : Rat) ^ k)

/-- Denominators for positions `1..8`: `2,4,...,256`. -/
def leftmostOneDenominatorTable : Fin 8 -> Nat :=
  ![2, 4, 8, 16, 32, 64, 128, 256]

/-- The `k`th leftmost-one probability denominator is `2^k`. -/
theorem leftmostOneDenominatorTable_eq :
    forall k : Fin 8, leftmostOneDenominatorTable k = 2 ^ (k.val + 1) := by native_decide

/-- Finite check of `P(leftmost 1 at position k) = 1/2^k` for positions `1..8`. -/
theorem leftmostOneProbability_eq :
    forall k : Fin 8,
      leftmostOneProbability (k.val + 1) =
        1 / ((leftmostOneDenominatorTable k : Nat) : Rat) := by native_decide

/-! ## 2. Geometric distribution partial sums -/

/-- Geometric distribution mass: `P(X = k) = (1-p)^(k-1) * p`. -/
def geometricMass (p : Rat) (k : Nat) : Rat :=
  (1 - p) ^ (k - 1) * p

/-- For `p = 1/3`, the first terms are `1/3, 2/9, 4/27, ...`. -/
def geometricOneThirdTable : Fin 6 -> Rat :=
  ![1 / 3, 2 / 9, 4 / 27, 8 / 81, 16 / 243, 32 / 729]

/-- The table follows `P(X=k) = (1-p)^(k-1) * p`. -/
theorem geometricOneThirdTable_eq_mass :
    forall k : Fin 6,
      geometricOneThirdTable k = geometricMass (1 / 3) (k.val + 1) := by native_decide

/-- First-`n` geometric sums: `sum_{k=1}^n (1-p)^(k-1)p = 1-(1-p)^n`. -/
theorem geometricOneThirdPartialSum_eq :
    forall n : Fin 6,
      (∑ i : Fin (n.val + 1), geometricMass (1 / 3) (i.val + 1)) =
        1 - (2 / 3 : Rat) ^ (n.val + 1) := by native_decide

/-- Scaled first-`n` sums for the `p = 1/2` geometric law. -/
def geometricHalfPartialScaled (n : Nat) : Nat :=
  ∑ i : Fin n, 2 ^ (n - (i.val + 1))

/-- Values of `2^n * sum_{k=1}^n 1/2^k` for `n = 1..10`. -/
def geometricHalfPartialScaledTable : Fin 10 -> Nat :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023]

/-- `sum_{k=1}^n 1/2^k = (2^n-1)/2^n`, verified after scaling by `2^n`. -/
theorem geometricHalfPartialScaled_eq :
    forall n : Fin 10,
      geometricHalfPartialScaled (n.val + 1) = 2 ^ (n.val + 1) - 1 := by native_decide

/-- The precomputed table matches the scaled partial sums. -/
theorem geometricHalfPartialScaledTable_eq :
    forall n : Fin 10,
      geometricHalfPartialScaledTable n = geometricHalfPartialScaled (n.val + 1) := by native_decide

/-! ## 3. Expected value of the `p = 1/2` geometric distribution -/

/-- `2^n * sum_{k=1}^n k/2^k`. -/
def expectedHalfPartialScaled (n : Nat) : Nat :=
  ∑ i : Fin n, (i.val + 1) * 2 ^ (n - (i.val + 1))

/-- Values of `2^n * sum_{k=1}^n k/2^k` for `n = 1..10`. -/
def expectedHalfPartialScaledTable : Fin 10 -> Nat :=
  ![1, 4, 11, 26, 57, 120, 247, 502, 1013, 2036]

/-- `sum_{k=1}^n k/2^k = 2 - (n+2)/2^n`, verified after scaling by `2^n`. -/
theorem expectedHalfPartialScaled_eq :
    forall n : Fin 10,
      expectedHalfPartialScaled (n.val + 1) =
        2 ^ (n.val + 2) - (n.val + 3) := by native_decide

/-- The finite values are increasing toward the limit `2`. -/
theorem expectedHalfPartialScaled_gap_to_two :
    forall n : Fin 10,
      2 * 2 ^ (n.val + 1) - expectedHalfPartialScaled (n.val + 1) =
        n.val + 3 := by native_decide

/-- The precomputed table matches the scaled expected-value sums. -/
theorem expectedHalfPartialScaledTable_eq :
    forall n : Fin 10,
      expectedHalfPartialScaledTable n = expectedHalfPartialScaled (n.val + 1) := by native_decide

/-! ## 4. Flajolet-Martin estimates -/

/-- Fixed-point scale for the Flajolet-Martin correction constant. -/
def fmScale : Nat := 100000

/-- Fixed-point `phi ~= 0.77351`, represented as `77351 / 100000`. -/
def fmPhiScaled : Nat := 77351

/-- Integer Flajolet-Martin estimate for `2^R / phi`, using `phi ~= 0.77351`. -/
def flajoletMartinEstimate (r : Nat) : Nat :=
  fmScale * 2 ^ r / fmPhiScaled

/-- Estimates `floor(2^R / 0.77351)` for `R = 0..9`. -/
def flajoletMartinEstimateTable : Fin 10 -> Nat :=
  ![1, 2, 5, 10, 20, 41, 82, 165, 330, 661]

/-- The table computes `2^R / phi` with `phi` represented by `77351/100000`. -/
theorem flajoletMartinEstimateTable_eq :
    forall r : Fin 10,
      flajoletMartinEstimateTable r = flajoletMartinEstimate r.val := by native_decide

/-- The raw register estimate is `2^R`; the FM estimate applies the `1/phi` correction. -/
theorem flajoletMartin_raw_vs_corrected :
    forall r : Fin 10,
      2 ^ r.val <= flajoletMartinEstimate r.val := by native_decide

/-! ## 5. Birthday threshold checks -/

/-- Lower decimal bound for `pi`: `pi > 314/100`. -/
def piLowerHundred : Nat := 314

/-- Upper classical rational bound for `pi`: `pi < 355/113`. -/
def piUpperNumerator : Nat := 355

/-- Denominator in the upper bound `pi < 355/113`. -/
def piUpperDenominator : Nat := 113

/-- Integer check: `23^2 * 2 < 365 * pi`, using `pi > 314/100`. -/
theorem birthday23Below_scaled :
    23 ^ 2 * 2 * 100 < 365 * piLowerHundred := by native_decide

/-- Integer check: `23.9^2 * 2 < 365 * pi`, using `pi > 314/100`. -/
theorem birthday239Below_scaled :
    239 ^ 2 * 2 < 365 * piLowerHundred := by native_decide

/-- Integer check: `24^2 * 2 > 365 * pi`, using `pi < 355/113`. -/
theorem birthday24Above_scaled :
    24 ^ 2 * 2 * piUpperDenominator > 365 * piUpperNumerator := by native_decide

/-! ## 6. LogLog counting model -/

/-- Powers of two used as exact cardinalities for LogLog checks. -/
def logLogCardinalityTable : Fin 9 -> Nat :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256]

/-- Fixed-point additive constant for a sample LogLog model, scaled by `100`. -/
def logLogConstantScaled : Nat := 33

/-- Scaled model `E[max bit position] = log2(n) + constant` for `n = 2^k`. -/
def logLogExpectedMaxScaled (k : Nat) : Nat :=
  100 * k + logLogConstantScaled

/-- Values of `100 * (log2(2^k) + 0.33)` for `k = 0..8`. -/
def logLogExpectedMaxScaledTable : Fin 9 -> Nat :=
  ![33, 133, 233, 333, 433, 533, 633, 733, 833]

/-- For powers of two, the logarithmic term is exactly the exponent. -/
theorem logLogCardinalityTable_eq_pow :
    forall k : Fin 9, logLogCardinalityTable k = 2 ^ k.val := by native_decide

/-- Finite check of `E[max bit position] = log2(n) + constant` on powers of two. -/
theorem logLogExpectedMaxScaledTable_eq :
    forall k : Fin 9,
      logLogExpectedMaxScaledTable k = logLogExpectedMaxScaled k.val := by native_decide

/-- Raw cardinality scale recovered from a register value. -/
def rawCardinalityEstimate (k : Nat) : Nat :=
  2 ^ k

/-- The raw `2^k` scale is the cardinality scale used by bit-position sketches. -/
theorem pow2_relation_to_cardinality_estimates :
    forall k : Fin 9,
      logLogCardinalityTable k = rawCardinalityEstimate k.val := by native_decide

/-! ## 7. Inclusion-exclusion for union bounds -/

/-- A small stream of observed keys. -/
def keySetA : Finset Nat :=
  [1, 2, 3, 5, 8].toFinset

/-- Another small stream of observed keys. -/
def keySetB : Finset Nat :=
  [3, 5, 7, 11].toFinset

/-- A second pair of observed-key sets. -/
def keySetC : Finset Nat :=
  [0, 1, 4, 9].toFinset

/-- A second pair of observed-key sets. -/
def keySetD : Finset Nat :=
  [1, 4, 16, 25, 36].toFinset

/-- Inclusion-exclusion instance: `|A union B| = |A| + |B| - |A intersect B|`. -/
theorem inclusionExclusion_keySetAB :
    (keySetA ∪ keySetB).card =
      keySetA.card + keySetB.card - (keySetA ∩ keySetB).card := by
  native_decide

/-- Inclusion-exclusion instance: `|C union D| = |C| + |D| - |C intersect D|`. -/
theorem inclusionExclusion_keySetCD :
    (keySetC ∪ keySetD).card =
      keySetC.card + keySetD.card - (keySetC ∩ keySetD).card := by
  native_decide



structure ProbabilisticCountingBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProbabilisticCountingBudgetCertificate.controlled
    (c : ProbabilisticCountingBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ProbabilisticCountingBudgetCertificate.budgetControlled
    (c : ProbabilisticCountingBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ProbabilisticCountingBudgetCertificate.Ready
    (c : ProbabilisticCountingBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ProbabilisticCountingBudgetCertificate.size
    (c : ProbabilisticCountingBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem probabilisticCounting_budgetCertificate_le_size
    (c : ProbabilisticCountingBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleProbabilisticCountingBudgetCertificate :
    ProbabilisticCountingBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleProbabilisticCountingBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilisticCountingBudgetCertificate.controlled,
      sampleProbabilisticCountingBudgetCertificate]
  · norm_num [ProbabilisticCountingBudgetCertificate.budgetControlled,
      sampleProbabilisticCountingBudgetCertificate]

example :
    sampleProbabilisticCountingBudgetCertificate.certificateBudgetWindow ≤
      sampleProbabilisticCountingBudgetCertificate.size := by
  apply probabilisticCounting_budgetCertificate_le_size
  constructor
  · norm_num [ProbabilisticCountingBudgetCertificate.controlled,
      sampleProbabilisticCountingBudgetCertificate]
  · norm_num [ProbabilisticCountingBudgetCertificate.budgetControlled,
      sampleProbabilisticCountingBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleProbabilisticCountingBudgetCertificate.Ready := by
  constructor
  · norm_num [ProbabilisticCountingBudgetCertificate.controlled,
      sampleProbabilisticCountingBudgetCertificate]
  · norm_num [ProbabilisticCountingBudgetCertificate.budgetControlled,
      sampleProbabilisticCountingBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleProbabilisticCountingBudgetCertificate.certificateBudgetWindow ≤
      sampleProbabilisticCountingBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ProbabilisticCountingBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleProbabilisticCountingBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleProbabilisticCountingBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.ProbabilisticCounting
