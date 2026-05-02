/-
  Analytic Combinatorics — Part B
  Chapter IX — Random structures, finite probability checks.

  The analytic limit laws in Chapter IX are represented here by lightweight
  rational finite sums and Prop-valued predicates.  Small labelled examples are
  checked by native computation.
-/
import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch2.CycleIndex

set_option linter.style.nativeDecide false

open Finset

namespace RandomStructures

/-! ## Boltzmann probabilities -/

/-- Truncated Boltzmann probability mass at size `n` for OGF coefficients `a`.

The denominator is the finite partial sum through degree `n`, matching the
requested rational proxy for the analytic normalization `A(z)`. -/
def BoltzmannProbability (a : ℕ → ℕ) (z : ℚ) (n : ℕ) : ℚ :=
  (a n : ℚ) * z ^ n /
    (∑ k ∈ Finset.range (n + 1), (a k : ℚ) * z ^ k)

/-- Catalan numbers, used as binary-tree counts in the Chapter IX checks. -/
def catalanCount (n : ℕ) : ℕ :=
  (2 * n).choose n / (n + 1)

/-- The critical value of the Catalan OGF `C(z)` at `z = 1/4`. -/
def catalanOGFAtQuarter : ℚ :=
  2

/-- The `n`th summand in the expected binary-tree size at the critical
Boltzmann parameter `z = 1/4`. -/
def catalanCriticalExpectedSizeTerm (n : ℕ) : ℚ :=
  (n : ℚ) * (catalanCount n : ℚ) * ((1 / 4 : ℚ) ^ n) / catalanOGFAtQuarter

/-- Partial sums of the expected-size series for binary trees at `z = 1/4`. -/
def catalanCriticalExpectedSizePartial (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), catalanCriticalExpectedSizeTerm k

/-- The requested first partial sums, `n = 0, ..., 10`, are strictly increasing. -/
theorem catalanCriticalExpectedSizePartial_increasing_0_10 :
    catalanCriticalExpectedSizePartial 0 < catalanCriticalExpectedSizePartial 1 ∧
    catalanCriticalExpectedSizePartial 1 < catalanCriticalExpectedSizePartial 2 ∧
    catalanCriticalExpectedSizePartial 2 < catalanCriticalExpectedSizePartial 3 ∧
    catalanCriticalExpectedSizePartial 3 < catalanCriticalExpectedSizePartial 4 ∧
    catalanCriticalExpectedSizePartial 4 < catalanCriticalExpectedSizePartial 5 ∧
    catalanCriticalExpectedSizePartial 5 < catalanCriticalExpectedSizePartial 6 ∧
    catalanCriticalExpectedSizePartial 6 < catalanCriticalExpectedSizePartial 7 ∧
    catalanCriticalExpectedSizePartial 7 < catalanCriticalExpectedSizePartial 8 ∧
    catalanCriticalExpectedSizePartial 8 < catalanCriticalExpectedSizePartial 9 ∧
    catalanCriticalExpectedSizePartial 9 < catalanCriticalExpectedSizePartial 10 := by
  native_decide

/-- A small Boltzmann sanity check for binary-tree coefficients at `z = 1/4`. -/
theorem boltzmannProbability_catalan_quarter_size_three :
    BoltzmannProbability catalanCount (1 / 4) 3 = 5 / 93 := by
  native_decide

/-! ## Largest cycles in random permutations -/

/-- Number of `n`-permutations in which a distinguished long cycle has length
`ell`.  For `ell > n/2`, such a cycle is unique, so these counts can be summed
without overlap. -/
def permutationsWithCycleLength (n ell : ℕ) : ℕ :=
  if 1 ≤ ell ∧ ell ≤ n then
    n.choose ell * (ell - 1).factorial * (n - ell).factorial
  else
    0

/-- Count of `n`-permutations whose largest cycle has length greater than
`n/2`, computed by summing the unique long-cycle lengths. -/
def largestCycleGtHalfPermCount (n : ℕ) : ℕ :=
  ∑ ell ∈ Finset.range (n + 1),
    if n < 2 * ell then permutationsWithCycleLength n ell else 0

/-- Fraction of `n`-permutations whose largest cycle has length greater than
`n/2`. -/
def largestCycleGtHalfFraction (n : ℕ) : ℚ :=
  (largestCycleGtHalfPermCount n : ℚ) / n.factorial

theorem permutations_four_with_three_cycle :
    permutationsWithCycleLength 4 3 = 8 := by
  native_decide

theorem permutations_four_with_four_cycle :
    permutationsWithCycleLength 4 4 = 6 := by
  native_decide

/-- For `n = 4`, the favourable permutations are those with a 3-cycle or a
4-cycle. -/
theorem largestCycleGtHalfPermCount_four :
    largestCycleGtHalfPermCount 4 = 14 := by
  native_decide

theorem largestCycleGtHalfFraction_four :
    largestCycleGtHalfFraction 4 = 7 / 12 := by
  native_decide

/-! ## Random mappings -/

/-- Number of forests on `n` labelled vertices rooted at a fixed set of `r`
roots.  This is Cayley's rooted-forest count, with the all-roots case handled
separately to avoid a negative exponent. -/
def rootedForestCount (n r : ℕ) : ℕ :=
  if r = 0 then
    if n = 0 then 1 else 0
  else if r = n then
    1
  else
    r * n ^ (n - r - 1)

/-- Connected functional digraphs on `n` labelled vertices.

Choose the cyclic vertices, arrange them into one cycle, and attach the
remaining vertices as rooted forests directed toward that cycle. -/
def connectedMappingCount (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (n + 1),
    if 1 ≤ r ∧ r ≤ n then
      n.choose r * (r - 1).factorial * rootedForestCount n r
    else
      0

/-- Number of mappings of an `n`-element labelled set with exactly `k`
connected components.  The recurrence isolates the component containing a
distinguished label. -/
def mappingComponentCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
      ∑ m ∈ Finset.range (n + 1),
        n.choose m * connectedMappingCount (m + 1) *
          mappingComponentCount (n - m) k
termination_by n k => (n, k)
decreasing_by all_goals simp_wf; omega

/-- Total number of components over all mappings on `n` labelled vertices. -/
def totalMappingComponents (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k * mappingComponentCount n k

/-- Average number of connected components in a uniformly random mapping of
`[n]`, as an exact rational number. -/
def averageMappingComponents (n : ℕ) : ℚ :=
  (totalMappingComponents n : ℚ) / (n ^ n : ℕ)

/-- Prop form of the classical estimate `E components ~ (1/2) log n`, with a
rational surrogate `logSeq`. -/
def MappingComponentsHalfLogAsymptotic (logSeq : ℕ → ℚ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N,
    (1 / 2 - ε) * logSeq n ≤ averageMappingComponents n ∧
      averageMappingComponents n ≤ (1 / 2 + ε) * logSeq n

/-- The component-count recurrence sums to all mappings, `n^n`, for `n = 1,
..., 5`. -/
theorem mappingComponentCount_row_sums_1_5 :
    (∑ k ∈ Finset.range (1 + 1), mappingComponentCount 1 k) = 1 ^ 1 ∧
    (∑ k ∈ Finset.range (2 + 1), mappingComponentCount 2 k) = 2 ^ 2 ∧
    (∑ k ∈ Finset.range (3 + 1), mappingComponentCount 3 k) = 3 ^ 3 ∧
    (∑ k ∈ Finset.range (4 + 1), mappingComponentCount 4 k) = 4 ^ 4 ∧
    (∑ k ∈ Finset.range (5 + 1), mappingComponentCount 5 k) = 5 ^ 5 := by
  native_decide

/-- Exact average component counts for random mappings of sizes `1, ..., 5`. -/
theorem averageMappingComponents_values_1_5 :
    averageMappingComponents 1 = 1 ∧
    averageMappingComponents 2 = 5 / 4 ∧
    averageMappingComponents 3 = 38 / 27 ∧
    averageMappingComponents 4 = 195 / 128 ∧
    averageMappingComponents 5 = 5049 / 3125 := by
  native_decide

/-! ## Gaussian-tail interface -/

/-- Kolmogorov-Smirnov style Gaussian-tail placeholder.

The sequence `a` supplies integer numerator counts, while `μ` and `σ` are
rational centering and scaling surrogates.  The predicate only records the
eventual positive scale and a rational tail envelope, leaving analytic
distribution functions to later files. -/
def HasGaussianTail (a : ℕ → ℕ) (μ σ : ℕ → ℚ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < σ n) ∧
    ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (a n : ℚ) ≤ μ n + ε * σ n


end RandomStructures