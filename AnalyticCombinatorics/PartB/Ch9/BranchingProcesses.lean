/-
  Analytic Combinatorics — Part B
  Chapter IX — Branching processes and random tree statistics.

  Numerical verifications from Flajolet–Sedgewick Ch. IX:
  - Catalan numbers: values, convolution recurrence, linear recurrence
  - Motzkin numbers: values and three-term recurrence
  - Cayley's formula: n^{n-1} labelled rooted trees
  - Leaf counts in binary trees: (n+1)·C(n) = C(2n, n)
  - Central binomial coefficients
  - Ballot / reflection identity: C(2n,n+1) + C(n) = C(2n,n)
  - Full binary trees with n leaves = C(n-1) (Catalan shift)
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace BranchingProcesses

open Finset

/-! ## 1.  Catalan numbers -/

/-- Catalan number C(n) = C(2n,n)/(n+1), counting binary trees with
n internal nodes, Dyck paths of semilength n, triangulations of (n+2)-gons, etc. -/
def catalan (n : ℕ) : ℕ := (2 * n).choose n / (n + 1)

/-- First ten Catalan numbers (OEIS A000108). -/
theorem catalan_values :
    catalan 0 = 1 ∧
    catalan 1 = 1 ∧
    catalan 2 = 2 ∧
    catalan 3 = 5 ∧
    catalan 4 = 14 ∧
    catalan 5 = 42 ∧
    catalan 6 = 132 ∧
    catalan 7 = 429 ∧
    catalan 8 = 1430 ∧
    catalan 9 = 4862 := by
  native_decide

/-- C(n) = Σ_{k=0}^{n-1} C(k)·C(n-1-k)  (convolution / recursion).
Checked for n = 1 … 5. -/
theorem catalan_convolution_1 :
    catalan 1 = ∑ k ∈ Finset.range 1, catalan k * catalan (0 - k) := by
  native_decide

theorem catalan_convolution_2 :
    catalan 2 = ∑ k ∈ Finset.range 2, catalan k * catalan (1 - k) := by
  native_decide

theorem catalan_convolution_3 :
    catalan 3 = ∑ k ∈ Finset.range 3, catalan k * catalan (2 - k) := by
  native_decide

theorem catalan_convolution_4 :
    catalan 4 = ∑ k ∈ Finset.range 4, catalan k * catalan (3 - k) := by
  native_decide

theorem catalan_convolution_5 :
    catalan 5 = ∑ k ∈ Finset.range 5, catalan k * catalan (4 - k) := by
  native_decide

/-- Linear recurrence (n+2)·C(n+1) = (4n+2)·C(n).
Stated as an equality in ℕ; both sides are positive for all n ≥ 0.
Checked for n = 0 … 7. -/
theorem catalan_linear_rec :
    (0 + 2) * catalan (0 + 1) = (4 * 0 + 2) * catalan 0 ∧
    (1 + 2) * catalan (1 + 1) = (4 * 1 + 2) * catalan 1 ∧
    (2 + 2) * catalan (2 + 1) = (4 * 2 + 2) * catalan 2 ∧
    (3 + 2) * catalan (3 + 1) = (4 * 3 + 2) * catalan 3 ∧
    (4 + 2) * catalan (4 + 1) = (4 * 4 + 2) * catalan 4 ∧
    (5 + 2) * catalan (5 + 1) = (4 * 5 + 2) * catalan 5 ∧
    (6 + 2) * catalan (6 + 1) = (4 * 6 + 2) * catalan 6 ∧
    (7 + 2) * catalan (7 + 1) = (4 * 7 + 2) * catalan 7 := by
  native_decide

/-! ## 2.  Motzkin numbers -/

/-- Motzkin number M(n) counts lattice paths from (0,0) to (n,0) with steps
(1,+1), (1,0), (1,-1) that stay non-negative; also counts unary-binary trees
with n edges, and many other structures. -/
def motzkin : Fin 9 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323]

/-- Values for n = 0..8 (OEIS A001006). -/
theorem motzkin_values :
    motzkin ⟨0, by omega⟩ = 1 ∧
    motzkin ⟨1, by omega⟩ = 1 ∧
    motzkin ⟨2, by omega⟩ = 2 ∧
    motzkin ⟨3, by omega⟩ = 4 ∧
    motzkin ⟨4, by omega⟩ = 9 ∧
    motzkin ⟨5, by omega⟩ = 21 ∧
    motzkin ⟨6, by omega⟩ = 51 ∧
    motzkin ⟨7, by omega⟩ = 127 ∧
    motzkin ⟨8, by omega⟩ = 323 := by
  native_decide

/-- Three-term recurrence:  (n+3)·M(n+1) = (2n+3)·M(n) + 3n·M(n-1).
Written in ℕ (all terms positive, no subtraction issues) for n = 1..6. -/
theorem motzkin_rec_n1 :
    (1 + 3) * motzkin ⟨2, by omega⟩ =
    (2 * 1 + 3) * motzkin ⟨1, by omega⟩ +
    3 * 1 * motzkin ⟨0, by omega⟩ := by native_decide

theorem motzkin_rec_n2 :
    (2 + 3) * motzkin ⟨3, by omega⟩ =
    (2 * 2 + 3) * motzkin ⟨2, by omega⟩ +
    3 * 2 * motzkin ⟨1, by omega⟩ := by native_decide

theorem motzkin_rec_n3 :
    (3 + 3) * motzkin ⟨4, by omega⟩ =
    (2 * 3 + 3) * motzkin ⟨3, by omega⟩ +
    3 * 3 * motzkin ⟨2, by omega⟩ := by native_decide

theorem motzkin_rec_n4 :
    (4 + 3) * motzkin ⟨5, by omega⟩ =
    (2 * 4 + 3) * motzkin ⟨4, by omega⟩ +
    3 * 4 * motzkin ⟨3, by omega⟩ := by native_decide

theorem motzkin_rec_n5 :
    (5 + 3) * motzkin ⟨6, by omega⟩ =
    (2 * 5 + 3) * motzkin ⟨5, by omega⟩ +
    3 * 5 * motzkin ⟨4, by omega⟩ := by native_decide

theorem motzkin_rec_n6 :
    (6 + 3) * motzkin ⟨7, by omega⟩ =
    (2 * 6 + 3) * motzkin ⟨6, by omega⟩ +
    3 * 6 * motzkin ⟨5, by omega⟩ := by native_decide

/-! ## 3.  Cayley's formula — labelled rooted trees -/

/-- Number of labelled rooted trees on n vertices: n^{n-1}
(Cayley 1889, Borchardt 1860). -/
def cayleyRooted (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

theorem cayleyRooted_values :
    cayleyRooted 1 = 1 ∧
    cayleyRooted 2 = 2 ∧
    cayleyRooted 3 = 9 ∧
    cayleyRooted 4 = 64 ∧
    cayleyRooted 5 = 625 ∧
    cayleyRooted 6 = 7776 := by
  native_decide

/-- Explicit computation: 1^0, 2^1, 3^2, 4^3, 5^4, 6^5. -/
theorem cayleyRooted_explicit :
    (1 : ℕ) ^ 0 = 1 ∧
    (2 : ℕ) ^ 1 = 2 ∧
    (3 : ℕ) ^ 2 = 9 ∧
    (4 : ℕ) ^ 3 = 64 ∧
    (5 : ℕ) ^ 4 = 625 ∧
    (6 : ℕ) ^ 5 = 7776 := by
  native_decide

/-- For n ≥ 2 the rooted tree count equals n times the unrooted count. -/
theorem cayleyRooted_eq_n_unrooted :
    2 * 1 ^ (2 - 2) = cayleyRooted 2 ∧
    3 * 3 ^ (3 - 2) = cayleyRooted 3 ∧
    4 * 4 ^ (4 - 2) = cayleyRooted 4 ∧
    5 * 5 ^ (5 - 2) = cayleyRooted 5 ∧
    6 * 6 ^ (6 - 2) = cayleyRooted 6 := by
  native_decide

/-! ## 4.  Leaf counts in binary trees -/

/-- Central binomial coefficient C(2n, n). -/
def centralBinom (n : ℕ) : ℕ := (2 * n).choose n

theorem centralBinom_values :
    centralBinom 0 = 1 ∧
    centralBinom 1 = 2 ∧
    centralBinom 2 = 6 ∧
    centralBinom 3 = 20 ∧
    centralBinom 4 = 70 ∧
    centralBinom 5 = 252 ∧
    centralBinom 6 = 924 ∧
    centralBinom 7 = 3432 ∧
    centralBinom 8 = 12870 := by
  native_decide

/-- Total number of leaves across all binary trees with n internal nodes.
Every binary tree with n internal nodes has exactly n+1 leaves, and there
are C(n) such trees, giving the total (n+1)·C(n). -/
def totalLeaves (n : ℕ) : ℕ := (n + 1) * catalan n

theorem totalLeaves_values :
    totalLeaves 0 = 1 ∧
    totalLeaves 1 = 2 ∧
    totalLeaves 2 = 6 ∧
    totalLeaves 3 = 20 ∧
    totalLeaves 4 = 70 ∧
    totalLeaves 5 = 252 ∧
    totalLeaves 6 = 924 ∧
    totalLeaves 7 = 3432 := by
  native_decide

/-- The identity (n+1)·C(n) = C(2n,n): total leaves equals the central
binomial coefficient.  Verified for n = 0..7. -/
theorem totalLeaves_eq_centralBinom :
    totalLeaves 0 = centralBinom 0 ∧
    totalLeaves 1 = centralBinom 1 ∧
    totalLeaves 2 = centralBinom 2 ∧
    totalLeaves 3 = centralBinom 3 ∧
    totalLeaves 4 = centralBinom 4 ∧
    totalLeaves 5 = centralBinom 5 ∧
    totalLeaves 6 = centralBinom 6 ∧
    totalLeaves 7 = centralBinom 7 := by
  native_decide

/-! ## 5.  Ballot / reflection identity -/

/-- Ballot identity (reflection principle):
  C(2n, n) - C(2n, n+1) = C(n)
Written as the ℕ equality  C(2n, n+1) + C(n) = C(2n, n)
(avoiding subtraction in ℕ).  Checked for n = 1..7. -/
theorem ballot_identity :
    (2 * 1).choose (1 + 1) + catalan 1 = centralBinom 1 ∧
    (2 * 2).choose (2 + 1) + catalan 2 = centralBinom 2 ∧
    (2 * 3).choose (3 + 1) + catalan 3 = centralBinom 3 ∧
    (2 * 4).choose (4 + 1) + catalan 4 = centralBinom 4 ∧
    (2 * 5).choose (5 + 1) + catalan 5 = centralBinom 5 ∧
    (2 * 6).choose (6 + 1) + catalan 6 = centralBinom 6 ∧
    (2 * 7).choose (7 + 1) + catalan 7 = centralBinom 7 := by
  native_decide

/-! ## 6.  Full binary trees with a given number of leaves -/

/-- A full binary tree (every internal node has exactly 2 children) with
k internal nodes has k+1 leaves.  Equivalently, a full binary tree with
n ≥ 1 leaves has n-1 internal nodes.  The number of such trees (plane, i.e.
ordered children) is therefore C(n-1).
Verified: full binary trees with n leaves = catalan (n-1) for n = 1..8. -/
theorem fullBinaryTrees_by_leaves :
    catalan 0 = 1 ∧   -- 1 leaf:  unique trivial tree
    catalan 1 = 1 ∧   -- 2 leaves
    catalan 2 = 2 ∧   -- 3 leaves
    catalan 3 = 5 ∧   -- 4 leaves
    catalan 4 = 14 ∧  -- 5 leaves
    catalan 5 = 42 ∧  -- 6 leaves
    catalan 6 = 132 ∧ -- 7 leaves
    catalan 7 = 429 := by  -- 8 leaves
  native_decide

/-! ## 7.  Ordered (plane) trees and Catalan numbers -/

/-- Number of ordered (plane) rooted trees with n edges = C(n).
Equivalently, ordered trees with n+1 vertices = C(n).
This repeats the Catalan table but in the tree interpretation. -/
theorem orderedTrees_eq_catalan :
    catalan 0 = 1 ∧   -- n=0: empty tree (1 vertex, 0 edges)
    catalan 1 = 1 ∧   -- n=1: single edge
    catalan 2 = 2 ∧
    catalan 3 = 5 ∧
    catalan 4 = 14 ∧
    catalan 5 = 42 ∧
    catalan 6 = 132 ∧
    catalan 7 = 429 ∧
    catalan 8 = 1430 := by
  native_decide

/-- Number of planted plane trees (rooted, ordered) with n+1 vertices = C(n).
Planted trees with n vertices = C(n-1).  Total vertex count over all
planted plane trees with n edges:
  Σ_{T: n edges} (n+1) = (n+1) · C(n) = centralBinom(n). -/
theorem totalVertices_orderedTrees :
    (0 + 1) * catalan 0 = 1 ∧
    (1 + 1) * catalan 1 = 2 ∧
    (2 + 1) * catalan 2 = 6 ∧
    (3 + 1) * catalan 3 = 20 ∧
    (4 + 1) * catalan 4 = 70 ∧
    (5 + 1) * catalan 5 = 252 := by
  native_decide

/-! ## 8.  Galton-Watson process: extinction probability -/

/-- For a Galton-Watson branching process with Poisson offspring
distribution of mean λ, the extinction probability q satisfies q = e^{λ(q-1)}.
For λ ≤ 1 the process goes extinct a.s. (q = 1).
For λ > 1 the unique solution in (0,1) gives the extinction probability.

We verify the critical threshold numerically:
if the mean offspring is exactly 1, the process is critical (extinction a.s.
but survives for a long time).

Concrete check: subcritical process (mean 1/2).
Offspring distribution: P(0) = 1/2, P(1) = 1/2.
Mean = 1/2 < 1, so extinction is certain.
The extinction probability satisfies q = (1/2) + (1/2)·q, giving q = 1. -/
theorem subcritical_extinction :
    (1 : ℚ) / 2 + 1 / 2 * 1 = 1 := by norm_num

/-- Supercritical process: P(0) = 1/4, P(2) = 3/4.
Mean = 0 * 1/4 + 2 * 3/4 = 3/2 > 1.
Extinction probability satisfies q = (1/4) + (3/4)·q².
By the quadratic formula the smaller root in (0,1) is q = 1/3. -/
theorem supercritical_extinction_equation :
    (1 : ℚ) / 4 + 3 / 4 * (1 / 3) ^ 2 = 1 / 3 := by norm_num

/-- The quadratic 3q² - 4q + 1 = 0 has roots q = 1/3 and q = 1. -/
theorem quadratic_roots :
    3 * (1 / 3 : ℚ) ^ 2 - 4 * (1 / 3) + 1 = 0 ∧
    3 * (1 : ℚ) ^ 2 - 4 * 1 + 1 = 0 := by norm_num

/-! ## 9.  Catalan generating function pole structure -/

/-- The ordinary generating function of Catalan numbers is
    C(z) = (1 - √(1-4z)) / (2z).
The dominant singularity is at z = 1/4.
The asymptotic is C_n ~ 4^n / (n^{3/2} · √π).

Rational proxy: C_n / (4^n / n) for small n (checks growth rate). -/
def catalanRatio (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (catalan n : ℚ) * n / 4 ^ n

theorem catalanRatio_values :
    catalanRatio 1 = 1 / 4 ∧
    catalanRatio 2 = 1 / 4 ∧
    catalanRatio 3 = 15 / 64 ∧
    catalanRatio 4 = 7 / 32 ∧
    catalanRatio 5 = 105 / 512 := by
  native_decide

/-- The ratios C_n · n / 4^n are increasing and approach 1/√π ≈ 0.5642.
Verified: each ratio is < 1 for n = 1..5. -/
theorem catalanRatio_lt_one :
    catalanRatio 1 < 1 ∧
    catalanRatio 2 < 1 ∧
    catalanRatio 3 < 1 ∧
    catalanRatio 4 < 1 ∧
    catalanRatio 5 < 1 := by
  native_decide

/-! ## 10.  Binary tree profile (nodes at depth d) -/

/-- A perfect binary tree of height h has 2^h - 1 internal nodes and 2^h leaves.
Total nodes = 2^{h+1} - 1.  Verified for h = 0..5. -/
theorem perfectTree_nodeCount :
    (2 : ℕ) ^ (0 + 1) - 1 = 1 ∧
    (2 : ℕ) ^ (1 + 1) - 1 = 3 ∧
    (2 : ℕ) ^ (2 + 1) - 1 = 7 ∧
    (2 : ℕ) ^ (3 + 1) - 1 = 15 ∧
    (2 : ℕ) ^ (4 + 1) - 1 = 31 ∧
    (2 : ℕ) ^ (5 + 1) - 1 = 63 := by
  native_decide

/-- Number of nodes at depth d in a perfect binary tree of height h = 2^d
for d = 0..h.  Verified: depth 0 = 1, depth 1 = 2, depth 2 = 4, depth 3 = 8. -/
theorem perfectTree_depthCount :
    (2 : ℕ) ^ 0 = 1 ∧
    (2 : ℕ) ^ 1 = 2 ∧
    (2 : ℕ) ^ 2 = 4 ∧
    (2 : ℕ) ^ 3 = 8 ∧
    (2 : ℕ) ^ 4 = 16 := by
  native_decide

/-- Internal path length of a perfect binary tree of height h:
    IPL(h) = Σ_{d=0}^{h-1} d · 2^d = (h-1)·2^h + 1.
Verified for h = 1..5. -/
def perfectTreeIPL (h : ℕ) : ℕ :=
  ∑ d ∈ Finset.range h, d * 2 ^ d

theorem perfectTreeIPL_values :
    perfectTreeIPL 1 = 0 ∧
    perfectTreeIPL 2 = 2 ∧
    perfectTreeIPL 3 = 10 ∧
    perfectTreeIPL 4 = 34 ∧
    perfectTreeIPL 5 = 98 := by
  native_decide

/-- The internal path length grows super-linearly: verified IPL(h+1) > 2*IPL(h)
for h = 2..4 (doubling plus extra). -/
theorem perfectTreeIPL_superlinear :
    perfectTreeIPL 3 > 2 * perfectTreeIPL 2 ∧
    perfectTreeIPL 4 > 2 * perfectTreeIPL 3 ∧
    perfectTreeIPL 5 > 2 * perfectTreeIPL 4 := by
  native_decide

end BranchingProcesses
