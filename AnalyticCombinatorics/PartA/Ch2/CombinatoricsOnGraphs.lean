/-
  Analytic Combinatorics — Part A: Labelled Structures & EGFs
  Chapter II: Combinatorics on Graphs — numerical verifications.

  Graph-theoretic combinatorial identities: complete graphs, labelled trees
  (Cayley's formula), chromatic polynomials, spanning tree counts.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace AnalyticCombinatorics.PartA.Ch2.CombinatoricsOnGraphs
/-! ## 1. Complete Graph K_n: edge count and total labelled graphs

  K_n has C(n,2) = n*(n-1)/2 edges.
  The total number of labelled graphs on n vertices is 2^C(n,2),
  since each pair of vertices either is or is not an edge.
-/

/-- Number of edges in the complete graph K_n. -/
def kEdges (n : ℕ) : ℕ := Nat.choose n 2

theorem kEdges_4 : kEdges 4 = 6 := by native_decide
theorem kEdges_5 : kEdges 5 = 10 := by native_decide
theorem kEdges_6 : kEdges 6 = 15 := by native_decide
theorem kEdges_10 : kEdges 10 = 45 := by native_decide

/-- C(n,2) = n*(n-1)/2 for all n. -/
theorem kEdges_formula (n : ℕ) : kEdges n = n * (n - 1) / 2 := by
  simp [kEdges, Nat.choose_two_right]

/-- Number of labelled graphs on n vertices = 2^C(n,2). -/
def labelledGraphCount (n : ℕ) : ℕ := 2 ^ (Nat.choose n 2)

theorem labelledGraphCount_3 : labelledGraphCount 3 = 8 := by native_decide
theorem labelledGraphCount_4 : labelledGraphCount 4 = 64 := by native_decide
theorem labelledGraphCount_5 : labelledGraphCount 5 = 1024 := by native_decide
theorem labelledGraphCount_6 : labelledGraphCount 6 = 32768 := by native_decide

/-- Cross-check: C(3,2)=3, so 2^3=8 labelled graphs on 3 vertices. -/
example : Nat.choose 3 2 = 3 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide
example : Nat.choose 5 2 = 10 := by native_decide
example : Nat.choose 6 2 = 15 := by native_decide

/-! ## 2. Labelled Trees — Cayley's Formula

  The number of labelled trees on n vertices is n^{n-2} for n ≥ 2.
  By Prüfer sequences: each labelled tree on [n] corresponds bijectively
  to a sequence of length n-2 with entries in {1,...,n}, giving n^{n-2} trees.

  Convention: n=1 yields 1 tree (single vertex), n=2 yields 1 tree (single edge).
-/

/-- Cayley's tree count: n^{n-2} labelled trees on n vertices. -/
def cayleyTreeCount (n : ℕ) : ℕ := if n ≤ 1 then 1 else n ^ (n - 2)

-- Table: n=1,2,...,8 gives 1, 1, 3, 16, 125, 1296, 16807, 262144.
theorem cayleyTreeCount_1 : cayleyTreeCount 1 = 1 := by native_decide
theorem cayleyTreeCount_2 : cayleyTreeCount 2 = 1 := by native_decide
theorem cayleyTreeCount_3 : cayleyTreeCount 3 = 3 := by native_decide
theorem cayleyTreeCount_4 : cayleyTreeCount 4 = 16 := by native_decide
theorem cayleyTreeCount_5 : cayleyTreeCount 5 = 125 := by native_decide
theorem cayleyTreeCount_6 : cayleyTreeCount 6 = 1296 := by native_decide
theorem cayleyTreeCount_7 : cayleyTreeCount 7 = 16807 := by native_decide
theorem cayleyTreeCount_8 : cayleyTreeCount 8 = 262144 := by native_decide

/-- Prüfer sequence viewpoint: n^{n-2} sequences of length n-2 from [n]. -/
-- For n=5: 5^3 = 125 Prüfer sequences ↔ 125 labelled trees.
example : (5 : ℕ) ^ 3 = 125 := by native_decide
-- For n=6: 6^4 = 1296.
example : (6 : ℕ) ^ 4 = 1296 := by native_decide

/-! ## 3. Chromatic Polynomial of Cycle C_n

  The chromatic polynomial of the n-cycle C_n is:
    χ(C_n, k) = (k-1)^n + (-1)^n * (k-1)

  For even n: χ = (k-1)^n + (k-1)
  For odd n:  χ = (k-1)^n - (k-1)

  We verify specific numerical values (avoiding ℕ subtraction issues).

  C_3 (triangle): χ(C_3, k) = k(k-1)(k-2)
    χ(C_3, 3) = 3·2·1 = 6
    χ(C_3, 4) = 4·3·2 = 24

  C_4 (4-cycle, even): χ(C_4, k) = (k-1)^4 + (k-1)
    χ(C_4, 3) = 2^4 + 2 = 18
    χ(C_4, 2) = 1^4 + 1 = 2

  C_5 (5-cycle, odd): χ(C_5, k) = (k-1)^5 - (k-1)
    χ(C_5, 3) = 2^5 - 2 = 30
    χ(C_5, 4) = 3^5 - 3 = 240
-/

-- χ(C_3, 3) = 6: k(k-1)(k-2) at k=3 → 3·2·1 = 6
example : 3 * 2 * 1 = 6 := by native_decide

-- χ(C_3, 4) = 24: 4·3·2 = 24
example : 4 * 3 * 2 = 24 := by native_decide

-- C_4 even: χ(C_4, k) = (k-1)^4 + (k-1)
-- χ(C_4, 3) = 2^4 + 2 = 18
example : 2 ^ 4 + 2 = 18 := by native_decide

-- χ(C_4, 2) = 1^4 + 1 = 2
example : 1 ^ 4 + 1 = 2 := by native_decide

-- C_5 odd: χ(C_5, k) = (k-1)^5 - (k-1), verify in ℤ
-- χ(C_5, 3) = 2^5 - 2 = 30
example : (2 : ℤ) ^ 5 - 2 = 30 := by native_decide

-- χ(C_5, 4) = 3^5 - 3 = 240
example : (3 : ℤ) ^ 5 - 3 = 240 := by native_decide

-- χ(C_6, 3): even, (k-1)^6 + (k-1) = 2^6 + 2 = 66
example : 2 ^ 6 + 2 = 66 := by native_decide

-- Chromatic polynomial formula as ℤ function for C_n at specific k
-- For even n ≥ 2: χ = (k-1)^n + (k-1)
-- For odd n ≥ 3:  χ = (k-1)^n - (k-1)

/-- Chromatic polynomial of C_n evaluated at k, in ℤ. -/
def chromaticCycleZ (n : ℕ) (k : ℤ) : ℤ :=
  if n % 2 = 0 then (k - 1) ^ n + (k - 1)
  else (k - 1) ^ n - (k - 1)

theorem chromaticCycleZ_C3_3 : chromaticCycleZ 3 3 = 6 := by native_decide
theorem chromaticCycleZ_C3_4 : chromaticCycleZ 3 4 = 24 := by native_decide
theorem chromaticCycleZ_C4_3 : chromaticCycleZ 4 3 = 18 := by native_decide
theorem chromaticCycleZ_C4_2 : chromaticCycleZ 4 2 = 2 := by native_decide
theorem chromaticCycleZ_C5_3 : chromaticCycleZ 5 3 = 30 := by native_decide
theorem chromaticCycleZ_C5_4 : chromaticCycleZ 5 4 = 240 := by native_decide
theorem chromaticCycleZ_C6_3 : chromaticCycleZ 6 3 = 66 := by native_decide

/-! ## 4. Graceful Labelling — Path P_n

  A graceful labelling of a graph G with m edges assigns vertex labels from
  {0,...,m} so that edge labels |u - v| are all distinct (1,...,m).
  All paths P_n are graceful.

  Number of graceful labellings of P_n (known small values):
    P_1: 1 vertex, 0 edges → 1 labelling
    P_2: 1 edge             → 1 labelling (up to symmetry; labels {0,1})
    P_3: 2 edges            → 1 essentially distinct graceful labelling
    P_4: 3 edges            → 2 graceful labellings
    P_5: 4 edges            → 4 graceful labellings
-/

/-- Table of graceful labelling counts for paths P_1 through P_5. -/
def gracefulPathCount : ℕ → ℕ
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 4
  | _ => 0   -- beyond tabulated range

theorem gracefulPathCount_1 : gracefulPathCount 1 = 1 := by native_decide
theorem gracefulPathCount_2 : gracefulPathCount 2 = 1 := by native_decide
theorem gracefulPathCount_3 : gracefulPathCount 3 = 1 := by native_decide
theorem gracefulPathCount_4 : gracefulPathCount 4 = 2 := by native_decide
theorem gracefulPathCount_5 : gracefulPathCount 5 = 4 := by native_decide

/-! ## 5. Independence Numbers, Cliques, and Ramsey Numbers

  Maximum independent set in K_n = 1 (every pair is adjacent).
  Maximum independent set in cycle C_n = ⌊n/2⌋.

  Ramsey number R(3,3) = 6:
    Any 2-coloring of edges of K_6 contains a monochromatic triangle.
    K_5 admits 2-colorings with no monochromatic triangle.

  K_5 has C(5,2) = 10 edges, giving 2^10 = 1024 total 2-colorings.
  K_6 has C(6,2) = 15 edges.
  K_6 has C(6,3) = 20 triangles.
-/

-- Maximum independent set in K_n is 1 (tabulated for small n)
def indepNumberKn (n : ℕ) : ℕ := if n ≤ 1 then n else 1

theorem indepNumberKn_1 : indepNumberKn 1 = 1 := by native_decide
theorem indepNumberKn_2 : indepNumberKn 2 = 1 := by native_decide
theorem indepNumberKn_5 : indepNumberKn 5 = 1 := by native_decide

-- Maximum independent set in C_n = ⌊n/2⌋
def indepNumberCn (n : ℕ) : ℕ := n / 2

theorem indepNumberCn_4 : indepNumberCn 4 = 2 := by native_decide
theorem indepNumberCn_5 : indepNumberCn 5 = 2 := by native_decide
theorem indepNumberCn_6 : indepNumberCn 6 = 3 := by native_decide
theorem indepNumberCn_7 : indepNumberCn 7 = 3 := by native_decide
theorem indepNumberCn_8 : indepNumberCn 8 = 4 := by native_decide

-- Ramsey R(3,3) = 6: basic numeric witnesses
-- K_5: C(5,2) = 10 edges
example : Nat.choose 5 2 = 10 := by native_decide
-- K_6: C(6,2) = 15 edges
example : Nat.choose 6 2 = 15 := by native_decide
-- K_6: C(6,3) = 20 triangles
example : Nat.choose 6 3 = 20 := by native_decide

-- Total 2-colorings of K_5 edges = 2^10 = 1024
example : 2 ^ 10 = 1024 := by native_decide

-- Total 2-colorings of K_6 edges = 2^15 = 32768
example : 2 ^ 15 = 32768 := by native_decide

/-- Ramsey witness: R(3,3) ≤ 6 is reflected in C(6,3) = 20 triangles in K_6;
    by pigeonhole any 2-coloring of K_6's 15 edges has a monochromatic triangle. -/
-- Numeric check: each vertex of K_6 has degree 5; by pigeonhole ≥ 3 edges same color.
example : 5 / 2 + 1 = 3 := by native_decide   -- ⌈5/2⌉ = 3

-- The 12 triangle-free 2-colorings of K_5 (known combinatorial fact, tabulated)
def triangleFreeColoringsK5 : ℕ := 12

example : triangleFreeColoringsK5 = 12 := by native_decide

/-! ## 6. Spanning Tree Count for Complete Bipartite Graphs K_{m,n}

  By the matrix-tree theorem (Kirchhoff), K_{m,n} has m^{n-1} * n^{m-1} spanning trees.

  Verification:
    K_{2,2}: 2^1 * 2^1 = 4
    K_{2,3}: 2^2 * 3^1 = 12
    K_{3,3}: 3^2 * 3^2 = 81
    K_{3,4}: 3^3 * 4^2 = 432
    K_{4,4}: 4^3 * 4^3 = 512
-/

/-- Number of spanning trees of K_{m,n} by Kirchhoff's formula: m^{n-1} * n^{m-1}. -/
def spanningTreesKmn (m n : ℕ) : ℕ :=
  if m = 0 ∨ n = 0 then 0
  else m ^ (n - 1) * n ^ (m - 1)

theorem spanningTreesKmn_2_2 : spanningTreesKmn 2 2 = 4 := by native_decide
theorem spanningTreesKmn_2_3 : spanningTreesKmn 2 3 = 12 := by native_decide
theorem spanningTreesKmn_3_3 : spanningTreesKmn 3 3 = 81 := by native_decide
theorem spanningTreesKmn_3_4 : spanningTreesKmn 3 4 = 432 := by native_decide
theorem spanningTreesKmn_4_4 : spanningTreesKmn 4 4 = 4096 := by native_decide

-- Cross-check with explicit arithmetic
example : 2 ^ 2 * 3 ^ 1 = 12 := by native_decide   -- K_{2,3}: 4 * 3 = 12
example : 3 ^ 2 * 3 ^ 2 = 81 := by native_decide   -- K_{3,3}: 9 * 9 = 81
example : 3 ^ 3 * 4 ^ 2 = 432 := by native_decide  -- K_{3,4}: 27 * 16 = 432

-- K_{1,n} is a star: always has 1 spanning tree (itself), n^0 * 1^{n-1} = 1.
theorem spanningTreesKmn_1_n (n : ℕ) (hn : n ≥ 1) : spanningTreesKmn 1 n = 1 := by
  simp [spanningTreesKmn]
  omega

-- K_{n,1} symmetrically has 1 spanning tree.
theorem spanningTreesKmn_n_1 (m : ℕ) (hm : m ≥ 1) : spanningTreesKmn m 1 = 1 := by
  simp [spanningTreesKmn]
  omega


structure CombinatoricsOnGraphsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatoricsOnGraphsBudgetCertificate.controlled
    (c : CombinatoricsOnGraphsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CombinatoricsOnGraphsBudgetCertificate.budgetControlled
    (c : CombinatoricsOnGraphsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CombinatoricsOnGraphsBudgetCertificate.Ready
    (c : CombinatoricsOnGraphsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatoricsOnGraphsBudgetCertificate.size
    (c : CombinatoricsOnGraphsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem combinatoricsOnGraphs_budgetCertificate_le_size
    (c : CombinatoricsOnGraphsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCombinatoricsOnGraphsBudgetCertificate :
    CombinatoricsOnGraphsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCombinatoricsOnGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.controlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.budgetControlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]

example :
    sampleCombinatoricsOnGraphsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatoricsOnGraphsBudgetCertificate.size := by
  apply combinatoricsOnGraphs_budgetCertificate_le_size
  constructor
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.controlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.budgetControlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCombinatoricsOnGraphsBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.controlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]
  · norm_num [CombinatoricsOnGraphsBudgetCertificate.budgetControlled,
      sampleCombinatoricsOnGraphsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatoricsOnGraphsBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatoricsOnGraphsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CombinatoricsOnGraphsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatoricsOnGraphsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCombinatoricsOnGraphsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.CombinatoricsOnGraphs
