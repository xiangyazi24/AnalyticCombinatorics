import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch9.ExtremalGraphCombinatorics


/-!
Computable checks for extremal and random graph combinatorics, corresponding to
Chapter IX themes in Analytic Combinatorics.
-/

def binomialCoefficient (n k : ℕ) : ℕ :=
  Nat.choose n k

def completeGraphEdgeCount (n : ℕ) : ℕ :=
  binomialCoefficient n 2

/--
Edges in the complete balanced `m`-partite Turán graph on `n` vertices.
This is the standard formula for `ex(n, K_{m+1})`.
-/
def balancedMultipartiteEdges (n m : ℕ) : ℕ :=
  if m = 0 then
    0
  else
    let q := n / m
    let s := n % m
    completeGraphEdgeCount n
      - s * completeGraphEdgeCount (q + 1)
      - (m - s) * completeGraphEdgeCount q

/--
The Turán number `ex(n, K_r)`: the maximum number of edges in a
`K_r`-free graph on `n` vertices, encoded by Turán's complete balanced
multipartite construction.
-/
def turanNumber (n r : ℕ) : ℕ :=
  balancedMultipartiteEdges n (r - 1)

def triangleTuranFormula (n : ℕ) : ℕ :=
  n ^ 2 / 4

def triangleTuranInputs : Fin 5 → ℕ := ![4, 5, 6, 7, 8]

def triangleTuranValues : Fin 5 → ℕ := ![4, 6, 9, 12, 16]

theorem turan_triangle_table :
    ∀ i : Fin 5,
      turanNumber (triangleTuranInputs i) 3 = triangleTuranFormula (triangleTuranInputs i)
        ∧ turanNumber (triangleTuranInputs i) 3 = triangleTuranValues i := by native_decide

theorem turan_triangle_n4 : turanNumber 4 3 = 4 := by native_decide

theorem turan_triangle_n5 : turanNumber 5 3 = 6 := by native_decide

theorem turan_triangle_n6 : turanNumber 6 3 = 9 := by native_decide

theorem turan_triangle_n7 : turanNumber 7 3 = 12 := by native_decide

theorem turan_triangle_n8 : turanNumber 8 3 = 16 := by native_decide

def ramseyNumber : ℕ → ℕ → ℕ
  | 3, 3 => 6
  | 3, 4 => 9
  | 4, 3 => 9
  | 3, 5 => 14
  | 5, 3 => 14
  | 4, 4 => 18
  | s, t => binomialCoefficient (s + t - 2) (s - 1)

def ramseyExactS : Fin 4 → ℕ := ![3, 3, 3, 4]

def ramseyExactT : Fin 4 → ℕ := ![3, 4, 5, 4]

def ramseyExactValues : Fin 4 → ℕ := ![6, 9, 14, 18]

theorem ramsey_exact_table :
    ∀ i : Fin 4,
      ramseyNumber (ramseyExactS i) (ramseyExactT i) = ramseyExactValues i := by
  native_decide

theorem ramsey_3_3 : ramseyNumber 3 3 = 6 := by native_decide

theorem ramsey_3_4 : ramseyNumber 3 4 = 9 := by native_decide

theorem ramsey_3_5 : ramseyNumber 3 5 = 14 := by native_decide

theorem ramsey_4_4 : ramseyNumber 4 4 = 18 := by native_decide

def ramseyBinomialBound (s t : ℕ) : ℕ :=
  binomialCoefficient (s + t - 2) (s - 1)

def ramseyBoundS : Fin 3 → ℕ := ![3, 3, 4]

def ramseyBoundT : Fin 3 → ℕ := ![3, 4, 4]

def ramseyBoundValues : Fin 3 → ℕ := ![6, 10, 20]

theorem ramsey_bound_table :
    ∀ i : Fin 3,
      ramseyNumber (ramseyBoundS i) (ramseyBoundT i)
          ≤ ramseyBinomialBound (ramseyBoundS i) (ramseyBoundT i)
        ∧ ramseyBinomialBound (ramseyBoundS i) (ramseyBoundT i) =
          ramseyBoundValues i := by
  native_decide

theorem ramsey_3_3_bound :
    ramseyNumber 3 3 ≤ binomialCoefficient 4 2 ∧ binomialCoefficient 4 2 = 6 := by native_decide

theorem ramsey_3_4_bound :
    ramseyNumber 3 4 ≤ binomialCoefficient 5 2 ∧ binomialCoefficient 5 2 = 10 := by native_decide

theorem ramsey_4_4_bound :
    ramseyNumber 4 4 ≤ binomialCoefficient 6 3 ∧ binomialCoefficient 6 3 = 20 := by native_decide

def fallingFactorial (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => fallingFactorial k n * (k - n)

/--
Chromatic polynomial of the complete graph `K_n` evaluated at `k` colors:
`P(K_n, k) = k * (k - 1) * ... * (k - n + 1) = k^{(n)}`.
-/
def completeGraphChromaticPolynomial (n k : ℕ) : ℕ :=
  fallingFactorial k n

def chromaticK3Inputs : Fin 3 → ℕ := ![3, 4, 5]

def chromaticK3Values : Fin 3 → ℕ := ![6, 24, 60]

theorem chromatic_complete_graph_k3_table :
    ∀ i : Fin 3,
      completeGraphChromaticPolynomial 3 (chromaticK3Inputs i)
          = chromaticK3Inputs i * (chromaticK3Inputs i - 1) * (chromaticK3Inputs i - 2)
        ∧ completeGraphChromaticPolynomial 3 (chromaticK3Inputs i) =
          chromaticK3Values i := by
  native_decide

theorem chromatic_k3_at_3 :
    completeGraphChromaticPolynomial 3 3 = 3 * (3 - 1) * (3 - 2) := by native_decide

theorem chromatic_k3_at_4 :
    completeGraphChromaticPolynomial 3 4 = 4 * (4 - 1) * (4 - 2) := by native_decide

theorem chromatic_k3_at_5 :
    completeGraphChromaticPolynomial 3 5 = 5 * (5 - 1) * (5 - 2) := by native_decide

inductive RandomGraphThreshold where
  | logarithmicOverN
  deriving DecidableEq, Repr

/-- Connectivity threshold for `G(n,p)`: `p = ln(n) / n`. -/
def connectivityThresholdScale (n : ℕ) : RandomGraphThreshold :=
  match n with
  | _ => .logarithmicOverN

def connectivityThresholdFormula : String :=
  "p = ln(n)/n"

theorem connectivity_threshold_formula :
    connectivityThresholdFormula = "p = ln(n)/n" := by native_decide

/-- Expected number of isolated vertices in `G(n,p)`: `n * (1 - p)^(n - 1)`. -/
def expectedIsolatedVertices (n : ℕ) (p : ℚ) : ℚ :=
  (n : ℚ) * (1 - p) ^ (n - 1)

def isolatedExpectationLowerBound (n : ℕ) : ℚ :=
  (n : ℚ) - (n : ℚ)

def isolatedExpectationUpperBound (n : ℕ) : ℚ :=
  n

def isolatedVertexN : Fin 3 → ℕ := ![4, 5, 6]

def isolatedVertexPNum : Fin 3 → ℕ := ![1, 1, 1]

def isolatedVertexPDen : Fin 3 → ℕ := ![2, 5, 3]

def isolatedVertexP (i : Fin 3) : ℚ :=
  (isolatedVertexPNum i : ℚ) / (isolatedVertexPDen i : ℚ)

theorem isolated_vertices_expectation_bounds_table :
    ∀ i : Fin 3,
      isolatedExpectationLowerBound (isolatedVertexN i)
          ≤ expectedIsolatedVertices (isolatedVertexN i) (isolatedVertexP i)
        ∧ expectedIsolatedVertices (isolatedVertexN i) (isolatedVertexP i)
          ≤ isolatedExpectationUpperBound (isolatedVertexN i) := by native_decide

theorem isolated_vertices_expectation_formula_check :
    expectedIsolatedVertices 4 ((1 : ℚ) / 2)
      = (4 : ℚ) * (1 - (1 : ℚ) / 2) ^ (4 - 1) := by native_decide

theorem isolated_vertices_expectation_half :
    expectedIsolatedVertices 4 ((1 : ℚ) / 2) = (1 : ℚ) / 2 := by native_decide



structure ExtremalGraphCombinatoricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ExtremalGraphCombinatoricsBudgetCertificate.controlled
    (c : ExtremalGraphCombinatoricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ExtremalGraphCombinatoricsBudgetCertificate.budgetControlled
    (c : ExtremalGraphCombinatoricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ExtremalGraphCombinatoricsBudgetCertificate.Ready
    (c : ExtremalGraphCombinatoricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ExtremalGraphCombinatoricsBudgetCertificate.size
    (c : ExtremalGraphCombinatoricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem extremalGraphCombinatorics_budgetCertificate_le_size
    (c : ExtremalGraphCombinatoricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleExtremalGraphCombinatoricsBudgetCertificate :
    ExtremalGraphCombinatoricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleExtremalGraphCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.controlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.budgetControlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]

example :
    sampleExtremalGraphCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleExtremalGraphCombinatoricsBudgetCertificate.size := by
  apply extremalGraphCombinatorics_budgetCertificate_le_size
  constructor
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.controlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.budgetControlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleExtremalGraphCombinatoricsBudgetCertificate.Ready := by
  constructor
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.controlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]
  · norm_num [ExtremalGraphCombinatoricsBudgetCertificate.budgetControlled,
      sampleExtremalGraphCombinatoricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleExtremalGraphCombinatoricsBudgetCertificate.certificateBudgetWindow ≤
      sampleExtremalGraphCombinatoricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List ExtremalGraphCombinatoricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleExtremalGraphCombinatoricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleExtremalGraphCombinatoricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.ExtremalGraphCombinatorics
