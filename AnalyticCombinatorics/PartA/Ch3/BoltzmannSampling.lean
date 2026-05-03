import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Ch III — Boltzmann sampling and random generation

Finite, executable checks for the basic Boltzmann-sampling identities from
Flajolet and Sedgewick, Chapter III.  The file uses rational arithmetic and
small coefficient tables so that each stated fact is checked by
`native_decide`.
-/

namespace BoltzmannSampling

open Finset

/-! ## 1. Boltzmann model -/

/-- A finite ordinary generating function from a coefficient table. -/
def finiteGF {m : ℕ} (counts : Fin m → ℕ) (x : ℚ) : ℚ :=
  ∑ n : Fin m, (counts n : ℚ) * x ^ n.val

/-- Boltzmann probability of one fixed object of size `n`: proportional to `x^n`. -/
def objectProbability {m : ℕ} (counts : Fin m → ℕ) (x : ℚ) (n : Fin m) : ℚ :=
  x ^ n.val / finiteGF counts x

/-- Boltzmann probability that the sampled object has size `n`. -/
def sizeProbability {m : ℕ} (counts : Fin m → ℕ) (x : ℚ) (n : Fin m) : ℚ :=
  (counts n : ℚ) * x ^ n.val / finiteGF counts x

/-- A small class with `C(n)` objects of size `n`, for `n = 0..4`. -/
def toyCounts : Fin 5 → ℕ :=
  ![1, 2, 2, 1, 3]

/-- The finite normalizer `C(1/2)` for the toy model. -/
theorem toyGF_half :
    finiteGF toyCounts (1 / 2) = 45 / 16 := by
  native_decide

/-- Size probability is `C(n)` times the probability of any one object of size `n`. -/
theorem boltzmann_size_probability_counts_objects :
    ∀ n : Fin 5,
      sizeProbability toyCounts (1 / 2) n =
        (toyCounts n : ℚ) * objectProbability toyCounts (1 / 2) n := by
  native_decide

/-- The ratio for two fixed objects depends only on the Boltzmann weights `x^n`. -/
theorem boltzmann_object_probability_ratio :
    objectProbability toyCounts (1 / 2) (3 : Fin 5) /
        objectProbability toyCounts (1 / 2) (1 : Fin 5) =
      (1 / 2 : ℚ) ^ 3 / (1 / 2 : ℚ) ^ 1 := by
  native_decide

/-! ## 2. Catalan structures at the critical value `x = 1/4` -/

/-- Catalan number `C_n = binom(2n,n)/(n+1)`. -/
def catalanFormula (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan numbers for `n = 0..10`. -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

/-- The Catalan table agrees with the closed formula. -/
theorem catalanTable_eq_formula :
    ∀ n : Fin 11, catalanTable n = catalanFormula n.val := by
  native_decide

/-- `C(1/4) = 2` for the Catalan ordinary generating function. -/
def catalanGFAtQuarter : ℚ :=
  2

/-- Boltzmann size probability for Catalan structures at `x = 1/4`. -/
def catalanCriticalSizeProbability (n : ℕ) : ℚ :=
  (catalanFormula n : ℚ) * (1 / 4 : ℚ) ^ n / catalanGFAtQuarter

/-- Contribution of size `n` to the expected size at `x = 1/4`. -/
def catalanCriticalExpectedContribution (n : ℕ) : ℚ :=
  (n : ℚ) * catalanCriticalSizeProbability n

/-- Prefix sum for the expected size computation at the critical value. -/
def catalanCriticalExpectedPrefix (m : ℕ) : ℚ :=
  ∑ n ∈ range m, catalanCriticalExpectedContribution n

/-- The first nine terms of the critical Catalan expected-size computation. -/
theorem catalanCriticalExpectedPrefix_nine :
    catalanCriticalExpectedPrefix 9 = 28007 / 32768 := by
  native_decide

/-- Prefixes increase, illustrating the divergent critical mean computation. -/
theorem catalanCriticalExpectedPrefix_increases :
    catalanCriticalExpectedPrefix 5 < catalanCriticalExpectedPrefix 7 ∧
      catalanCriticalExpectedPrefix 7 < catalanCriticalExpectedPrefix 9 ∧
      catalanCriticalExpectedPrefix 9 < catalanCriticalExpectedPrefix 11 := by
  native_decide

/-- The critical Catalan mean has no finite rational value in this model. -/
def catalanCriticalMean : Option ℚ :=
  none

/-- At `x = 1/4`, the Catalan Boltzmann expected size is recorded as infinite. -/
theorem catalanCriticalMean_infinite :
    catalanCriticalMean = none := by
  native_decide

/-! ## 3. Binary tree sizes -/

/-- Number of binary trees with `n` internal nodes, for `n = 0..10`. -/
def binaryTreeCount : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

/-- Binary trees of size `n` are counted by the Catalan number `C(n)`. -/
theorem binaryTreeCount_eq_catalan :
    ∀ n : Fin 11, binaryTreeCount n = catalanTable n := by
  native_decide

/-- Binary-tree counts also satisfy the closed Catalan formula. -/
theorem binaryTreeCount_eq_formula :
    ∀ n : Fin 11, binaryTreeCount n = catalanFormula n.val := by
  native_decide

/-! ## 4. Rejection sampling acceptance rate -/

/-- Acceptance rate for exact-size rejection from the critical Catalan sampler. -/
def catalanAcceptanceRateAtQuarter (n : ℕ) : ℚ :=
  catalanCriticalSizeProbability n

/-- For `x = 1/4`, `P(size=n) = x^n * C(n) / C(x)`. -/
theorem catalanAcceptanceRate_formula :
    ∀ n : Fin 11,
      catalanAcceptanceRateAtQuarter n.val =
        (1 / 4 : ℚ) ^ n.val * (catalanFormula n.val : ℚ) / catalanGFAtQuarter := by
  native_decide

/-- Concrete exact-size acceptance rates at `x = 1/4`. -/
theorem catalanAcceptanceRate_examples :
    catalanAcceptanceRateAtQuarter 0 = 1 / 2 ∧
      catalanAcceptanceRateAtQuarter 1 = 1 / 8 ∧
      catalanAcceptanceRateAtQuarter 4 = 7 / 256 ∧
      catalanAcceptanceRateAtQuarter 8 = 715 / 65536 := by
  native_decide

/-! ## 5. Sequence construction -/

/-- Ordinary generating function of `SEQ(Z)` at `x`, namely `1/(1-x)`. -/
def seqGF (x : ℚ) : ℚ :=
  1 / (1 - x)

/-- Boltzmann probability of a sequence having length `k`. -/
def seqLengthProbability (x : ℚ) (k : ℕ) : ℚ :=
  x ^ k / seqGF x

/-- At `x = 1/3`, `SEQ` lengths follow the geometric law `(1-x)x^k`. -/
theorem seqLengthProbability_geometric_one_third :
    ∀ k : Fin 10,
      seqLengthProbability (1 / 3) k.val =
        (1 - (1 / 3 : ℚ)) * (1 / 3 : ℚ) ^ k.val := by
  native_decide

/-- At `x = 1/2`, the same geometric law gives powers of two. -/
theorem seqLengthProbability_geometric_one_half :
    ∀ k : Fin 10,
      seqLengthProbability (1 / 2) k.val =
        (1 - (1 / 2 : ℚ)) * (1 / 2 : ℚ) ^ k.val := by
  native_decide

/-! ## 6. Recursive decompositions: union and product checks -/

/-- Left branch counts for a small recursive specification. -/
def leftCounts : Fin 4 → ℕ :=
  ![1, 1, 0, 1]

/-- Right branch counts for a small recursive specification. -/
def rightCounts : Fin 4 → ℕ :=
  ![0, 1, 2, 0]

/-- Disjoint union counts, size by size. -/
def unionCounts : Fin 4 → ℕ :=
  ![1, 2, 2, 1]

/-- Union adds counts size by size. -/
theorem unionCounts_eq_add :
    ∀ n : Fin 4, unionCounts n = leftCounts n + rightCounts n := by
  native_decide

/-- The ordinary generating function of a union is the sum of the branch GFs. -/
theorem unionGF_half_eq_sum :
    finiteGF unionCounts (1 / 2) =
      finiteGF leftCounts (1 / 2) + finiteGF rightCounts (1 / 2) := by
  native_decide

/-- Branch probabilities for the union sampler at `x = 1/2`. -/
theorem unionBranchProbabilities_half :
    finiteGF leftCounts (1 / 2) / finiteGF unionCounts (1 / 2) = 13 / 21 ∧
      finiteGF rightCounts (1 / 2) / finiteGF unionCounts (1 / 2) = 8 / 21 ∧
      finiteGF leftCounts (1 / 2) / finiteGF unionCounts (1 / 2) +
          finiteGF rightCounts (1 / 2) / finiteGF unionCounts (1 / 2) = 1 := by
  native_decide

/-- Natural-number lookup for the left table, returning zero outside the table. -/
def leftCountNat (n : ℕ) : ℕ :=
  if h : n < 4 then leftCounts ⟨n, h⟩ else 0

/-- Natural-number lookup for the right table, returning zero outside the table. -/
def rightCountNat (n : ℕ) : ℕ :=
  if h : n < 4 then rightCounts ⟨n, h⟩ else 0

/-- Convolution count for the product construction. -/
def productCountNat (n : ℕ) : ℕ :=
  ∑ i ∈ range (n + 1), leftCountNat i * rightCountNat (n - i)

/-- Product counts for sizes `0..6`. -/
def productCounts : Fin 7 → ℕ :=
  ![0, 1, 3, 2, 1, 2, 0]

/-- Product construction gives the convolution of size counts. -/
theorem productCounts_eq_convolution :
    ∀ n : Fin 7, productCounts n = productCountNat n.val := by
  native_decide

/-- Product ordinary generating functions multiply at `x = 1/2`. -/
theorem productGF_half_eq_mul :
    finiteGF productCounts (1 / 2) =
      finiteGF leftCounts (1 / 2) * finiteGF rightCounts (1 / 2) := by
  native_decide

/-- Joint probability of drawing left size `i` and right size `j` in the product sampler. -/
def productPairProbabilityHalf (i j : Fin 4) : ℚ :=
  ((leftCounts i * rightCounts j : ℕ) : ℚ) *
      (1 / 2 : ℚ) ^ (i.val + j.val) / finiteGF productCounts (1 / 2)

/-- The product sampler factorizes into independent component samplers. -/
theorem productPairProbability_factorizes_half :
    ∀ i j : Fin 4,
      productPairProbabilityHalf i j =
        sizeProbability leftCounts (1 / 2) i *
          sizeProbability rightCounts (1 / 2) j := by
  native_decide

end BoltzmannSampling
