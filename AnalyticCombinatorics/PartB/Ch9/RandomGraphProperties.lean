import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.RandomGraphProperties


/-! # Random graph property thresholds

Small computable checks for standard `G(n,p)` quantities from the random graph
threshold discussion in Chapter IX of Flajolet and Sedgewick.
-/

/-! ## Triangles in `G(n,p)` -/

/-- Expected number of triangles in `G(n,p)`: `choose n 3 * p^3`. -/
def expectedTriangles (n : ℕ) (p : ℚ) : ℚ :=
  (Nat.choose n 3 : ℚ) * p ^ 3

example : expectedTriangles 4 (1 / 2 : ℚ) = (1 / 2 : ℚ) := by native_decide
example : expectedTriangles 5 (1 / 2 : ℚ) = (5 / 4 : ℚ) := by native_decide
example : expectedTriangles 6 (1 / 2 : ℚ) = (5 / 2 : ℚ) := by native_decide

example : 8 * expectedTriangles 4 (1 / 2 : ℚ) = (Nat.choose 4 3 : ℚ) := by native_decide
example : 8 * expectedTriangles 5 (1 / 2 : ℚ) = (Nat.choose 5 3 : ℚ) := by native_decide
example : 8 * expectedTriangles 6 (1 / 2 : ℚ) = (Nat.choose 6 3 : ℚ) := by native_decide

/-! ## Edges at the sparse threshold `p = c / n` -/

/-- Expected number of edges in `G(n,p)`: `choose n 2 * p`. -/
def expectedEdges (n : ℕ) (p : ℚ) : ℚ :=
  (Nat.choose n 2 : ℚ) * p

/-- Expected edges when `p = c/n`, equal to `c*(n-1)/2` for `n > 0`. -/
def expectedEdgesAtThreshold (n : ℕ) (c : ℚ) : ℚ :=
  expectedEdges n (c / (n : ℚ))

example : expectedEdgesAtThreshold 10 1 = (1 * (10 - 1) / 2 : ℚ) := by native_decide
example : expectedEdgesAtThreshold 20 1 = (1 * (20 - 1) / 2 : ℚ) := by native_decide
example : expectedEdgesAtThreshold 50 1 = (1 * (50 - 1) / 2 : ℚ) := by native_decide

example : expectedEdgesAtThreshold 10 1 = (9 / 2 : ℚ) := by native_decide
example : expectedEdgesAtThreshold 20 1 = (19 / 2 : ℚ) := by native_decide
example : expectedEdgesAtThreshold 50 1 = (49 / 2 : ℚ) := by native_decide

/-! ## Isolated vertices and the no-isolated-vertex threshold -/

/-- The usual logarithmic threshold scale for no isolated vertices. -/
noncomputable def noIsolatedVertexThreshold (n : ℕ) : ℝ :=
  Real.log (n : ℝ) / (n : ℝ)

/-- Expected number of isolated vertices in `G(n,p)`: `n * (1-p)^(n-1)`. -/
def expectedIsolatedVertices (n : ℕ) (p : ℚ) : ℚ :=
  (n : ℚ) * (1 - p) ^ (n - 1)

/-- Integer numerator for `n * (1 - k/n)^(n-1)`. -/
def isolatedNumeratorAtIntegerOverN (n k : ℕ) : ℕ :=
  n * (n - k) ^ (n - 1)

/-- Integer denominator for `n * (1 - k/n)^(n-1)`. -/
def isolatedDenominatorAtIntegerOverN (n : ℕ) : ℕ :=
  n ^ (n - 1)

/-- The `k = 1` ratio `n*(n-1)^(n-1) / n^(n-1)`. -/
def isolatedUnitRatio (n : ℕ) : ℕ × ℕ :=
  (isolatedNumeratorAtIntegerOverN n 1, isolatedDenominatorAtIntegerOverN n)

example :
    expectedIsolatedVertices 10 (1 / 10 : ℚ) =
      ((10 * 9 ^ 9 : ℕ) : ℚ) / (10 ^ 9 : ℕ) := by native_decide

example :
    expectedIsolatedVertices 20 (1 / 20 : ℚ) =
      ((20 * 19 ^ 19 : ℕ) : ℚ) / (20 ^ 19 : ℕ) := by native_decide

example :
    expectedIsolatedVertices 50 (1 / 50 : ℚ) =
      ((50 * 49 ^ 49 : ℕ) : ℚ) / (50 ^ 49 : ℕ) := by native_decide

example : isolatedUnitRatio 10 = (10 * 9 ^ 9, 10 ^ 9) := by native_decide
example : isolatedUnitRatio 20 = (20 * 19 ^ 19, 20 ^ 19) := by native_decide
example : isolatedUnitRatio 50 = (50 * 49 ^ 49, 50 ^ 49) := by native_decide

example :
    isolatedNumeratorAtIntegerOverN 10 2 ≤ isolatedNumeratorAtIntegerOverN 10 1 :=
  by native_decide

example :
    isolatedNumeratorAtIntegerOverN 20 2 ≤ isolatedNumeratorAtIntegerOverN 20 1 :=
  by native_decide

example :
    isolatedNumeratorAtIntegerOverN 50 2 ≤ isolatedNumeratorAtIntegerOverN 50 1 :=
  by native_decide

/-! ## Chromatic number and greedy coloring -/

/-- Greedy coloring bound, represented by its numerical assertion. -/
abbrev greedyChromaticBound (chromaticNumber maximumDegree : ℕ) : Prop :=
  chromaticNumber ≤ maximumDegree + 1

/-- Maximum degree of the complete graph `K_n`. -/
def completeGraphMaxDegree (n : ℕ) : ℕ :=
  n - 1

/-- Chromatic number of the complete graph `K_n`. -/
def completeGraphChromaticNumber (n : ℕ) : ℕ :=
  n

example : completeGraphMaxDegree 1 = 0 := by native_decide
example : completeGraphMaxDegree 5 = 4 := by native_decide
example : completeGraphMaxDegree 10 = 9 := by native_decide

example :
    greedyChromaticBound (completeGraphChromaticNumber 5) (completeGraphMaxDegree 5) :=
  by native_decide

example :
    greedyChromaticBound (completeGraphChromaticNumber 10) (completeGraphMaxDegree 10) :=
  by native_decide

/-! ## Clique number and independence number -/

/-- Product lower bound `alpha(G) * omega(G) >= n`, represented numerically. -/
abbrev independenceCliqueProductBound (n independenceNumber cliqueNumber : ℕ) : Prop :=
  n ≤ independenceNumber * cliqueNumber

/-- Clique number of `K_n`. -/
def completeGraphCliqueNumber (n : ℕ) : ℕ :=
  n

/-- Independence number of `K_n`. -/
def completeGraphIndependenceNumber (n : ℕ) : ℕ :=
  if n = 0 then 0 else 1

example : completeGraphCliqueNumber 5 = 5 := by native_decide
example : completeGraphIndependenceNumber 5 = 1 := by native_decide

example :
    completeGraphIndependenceNumber 5 * completeGraphCliqueNumber 5 = 5 := by
  native_decide

example :
    independenceCliqueProductBound 5
      (completeGraphIndependenceNumber 5)
      (completeGraphCliqueNumber 5) := by
  native_decide

/-! ## Expected degree in `G(n,1/2)` -/

/-- Expected degree of a vertex in `G(n,p)`: `(n-1)*p`. -/
def expectedDegree (n : ℕ) (p : ℚ) : ℚ :=
  ((n - 1 : ℕ) : ℚ) * p

example : expectedDegree 5 (1 / 2 : ℚ) = ((5 - 1) / 2 : ℚ) := by native_decide
example : expectedDegree 7 (1 / 2 : ℚ) = ((7 - 1) / 2 : ℚ) := by native_decide
example : expectedDegree 9 (1 / 2 : ℚ) = ((9 - 1) / 2 : ℚ) := by native_decide
example : expectedDegree 11 (1 / 2 : ℚ) = ((11 - 1) / 2 : ℚ) := by native_decide

example : expectedDegree 5 (1 / 2 : ℚ) = 2 := by native_decide
example : expectedDegree 7 (1 / 2 : ℚ) = 3 := by native_decide
example : expectedDegree 9 (1 / 2 : ℚ) = 4 := by native_decide
example : expectedDegree 11 (1 / 2 : ℚ) = 5 := by native_decide

/-- Greedy chromatic bound sample for a complete graph. -/
theorem completeGraph_greedy_bound_ten :
    greedyChromaticBound
      (completeGraphChromaticNumber 10) (completeGraphMaxDegree 10) := by
  native_decide

/-- Expected degree sample in `G(n,1/2)`. -/
theorem expectedDegree_eleven_half :
    expectedDegree 11 (1 / 2 : ℚ) = 5 := by
  native_decide



structure RandomGraphPropertiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomGraphPropertiesBudgetCertificate.controlled
    (c : RandomGraphPropertiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomGraphPropertiesBudgetCertificate.budgetControlled
    (c : RandomGraphPropertiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomGraphPropertiesBudgetCertificate.Ready
    (c : RandomGraphPropertiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomGraphPropertiesBudgetCertificate.size
    (c : RandomGraphPropertiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomGraphProperties_budgetCertificate_le_size
    (c : RandomGraphPropertiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomGraphPropertiesBudgetCertificate :
    RandomGraphPropertiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomGraphPropertiesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphPropertiesBudgetCertificate.controlled,
      sampleRandomGraphPropertiesBudgetCertificate]
  · norm_num [RandomGraphPropertiesBudgetCertificate.budgetControlled,
      sampleRandomGraphPropertiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomGraphPropertiesBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphPropertiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomGraphPropertiesBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomGraphPropertiesBudgetCertificate.controlled,
      sampleRandomGraphPropertiesBudgetCertificate]
  · norm_num [RandomGraphPropertiesBudgetCertificate.budgetControlled,
      sampleRandomGraphPropertiesBudgetCertificate]

example :
    sampleRandomGraphPropertiesBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomGraphPropertiesBudgetCertificate.size := by
  apply randomGraphProperties_budgetCertificate_le_size
  constructor
  · norm_num [RandomGraphPropertiesBudgetCertificate.controlled,
      sampleRandomGraphPropertiesBudgetCertificate]
  · norm_num [RandomGraphPropertiesBudgetCertificate.budgetControlled,
      sampleRandomGraphPropertiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RandomGraphPropertiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomGraphPropertiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRandomGraphPropertiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.RandomGraphProperties
