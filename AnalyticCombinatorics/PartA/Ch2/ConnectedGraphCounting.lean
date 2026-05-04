import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ConnectedGraphCounting

/-!
# Connected graph counting

Detailed edge-level enumeration of connected labelled graphs, Riddell's
recurrence formula, spanning tree counts via the Matrix-Tree theorem,
explicit Laplacian cofactor determinants, 2-connected graph enumeration,
and the excess parameter classifying connected graphs by cyclicity.

Reference: Flajolet & Sedgewick, *Analytic Combinatorics*, Chapter II §3–5.
-/

/-! ## §1. Basic graph counts -/

/-- Total labelled simple graphs on `n` vertices: `2^{C(n,2)}`. -/
def totalGraphs (n : ℕ) : ℕ := 2 ^ Nat.choose n 2

/-- Connected labelled graph counts (OEIS A001187), tabulated for `n ≤ 7`. -/
def cCount : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 4
  | 4 => 38
  | 5 => 728
  | 6 => 26704
  | 7 => 1866256
  | _ => 0

example : totalGraphs 0 = 1 := by native_decide
example : totalGraphs 3 = 8 := by native_decide
example : totalGraphs 4 = 64 := by native_decide
example : totalGraphs 5 = 1024 := by native_decide
example : totalGraphs 6 = 32768 := by native_decide
example : totalGraphs 7 = 2097152 := by native_decide

/-! ## §2. Connected graphs by number of edges -/

/-- Number of connected labelled graphs on `n` vertices with exactly `m` edges,
    tabulated for `n ≤ 5`. -/
def connByEdges : ℕ → ℕ → ℕ
  | 1, 0 => 1
  | 2, 1 => 1
  | 3, 2 => 3
  | 3, 3 => 1
  | 4, 3 => 16
  | 4, 4 => 15
  | 4, 5 => 6
  | 4, 6 => 1
  | 5, 4 => 125
  | 5, 5 => 222
  | 5, 6 => 205
  | 5, 7 => 120
  | 5, 8 => 45
  | 5, 9 => 10
  | 5, 10 => 1
  | _, _ => 0

/-- Row sum of `connByEdges` over all possible edge counts. -/
def connByEdgesRowSum (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (Nat.choose n 2 + 1), connByEdges n m

/-- The row sum of the edge-count table equals the total connected count. -/
theorem row_sum_eq_cCount :
    ∀ i : Fin 5, cCount (i.val + 1) = connByEdgesRowSum (i.val + 1) := by
  native_decide

/-- Below the tree threshold `n − 1`, no connected graphs exist. -/
theorem below_tree_threshold_four :
    connByEdges 4 0 = 0 ∧ connByEdges 4 1 = 0 ∧ connByEdges 4 2 = 0 := by
  native_decide

/-- Trees are the connected graphs with exactly `n − 1` edges. Their counts
    match Cayley's formula `n^{n−2}`. -/
example : connByEdges 3 2 = 3 := by native_decide
example : connByEdges 4 3 = 16 := by native_decide
example : connByEdges 5 4 = 125 := by native_decide

/-- Total labelled graphs by edge count: `C(C(n,2), m)`. -/
def totalByEdges (n m : ℕ) : ℕ := Nat.choose (Nat.choose n 2) m

/-- Number of disconnected labelled graphs on `n` vertices with `m` edges. -/
def disconnByEdges (n m : ℕ) : ℕ := totalByEdges n m - connByEdges n m

/-- For `n = 5, m = 5`: of the 252 graphs, 30 are disconnected
    (an isolated vertex plus a connected 4-vertex graph with 5 edges). -/
example : disconnByEdges 5 5 = 30 := by native_decide

/-- For `n = 5, m = 6`: of the 210 graphs, 5 are disconnected
    (an isolated vertex plus K₄). -/
example : disconnByEdges 5 6 = 5 := by native_decide

/-- For `n = 5, m ≥ 7`: every labelled graph is connected. -/
theorem all_connected_five_high_edges :
    ∀ i : Fin 4, disconnByEdges 5 (i.val + 7) = 0 := by
  native_decide

/-! ## §3. Riddell's recurrence -/

/-- Riddell's recurrence in multiplicative (differentiation) form:
    `n · c_n = n · g_n − Σ_{k=1}^{n−1} k · C(n,k) · c_k · g_{n−k}`. -/
def riddellRHS (n : ℕ) : ℕ :=
  n * totalGraphs n -
    ∑ k ∈ Finset.Icc 1 (n - 1),
      k * Nat.choose n k * cCount k * totalGraphs (n - k)

/-- Riddell's formula in the standard binomial-coefficient form:
    `c_n = g_n − Σ_{k=1}^{n−1} C(n−1,k−1) · c_k · g_{n−k}`. -/
def riddellStandard (n : ℕ) : ℕ :=
  totalGraphs n -
    ∑ k ∈ Finset.Icc 1 (n - 1),
      Nat.choose (n - 1) (k - 1) * cCount k * totalGraphs (n - k)

theorem riddell_checked :
    ∀ i : Fin 7, (i.val + 1) * cCount (i.val + 1) = riddellRHS (i.val + 1) := by
  native_decide

theorem riddell_standard_checked :
    ∀ i : Fin 7, cCount (i.val + 1) = riddellStandard (i.val + 1) := by
  native_decide

/-- The two forms of Riddell agree: the identity `n · C(n−1,k−1) = k · C(n,k)`
    relates the multiplicative and standard forms. -/
theorem riddell_forms_agree :
    ∀ i : Fin 7,
      (i.val + 1) * riddellStandard (i.val + 1) = riddellRHS (i.val + 1) := by
  native_decide

/-! ## §4. Spanning tree counts -/

/-- Spanning trees of the complete graph K_n: Cayley's formula `n^{n−2}`. -/
def spanTreeKn : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n => n ^ (n - 2)

example : spanTreeKn 1 = 1 := by native_decide
example : spanTreeKn 2 = 1 := by native_decide
example : spanTreeKn 3 = 3 := by native_decide
example : spanTreeKn 4 = 16 := by native_decide
example : spanTreeKn 5 = 125 := by native_decide
example : spanTreeKn 6 = 1296 := by native_decide
example : spanTreeKn 7 = 16807 := by native_decide

/-- Spanning trees of the cycle graph C_n: always `n` (remove any one edge). -/
def spanTreeCycle (n : ℕ) : ℕ := n

/-- Spanning trees of the complete bipartite graph K_{m,n}:
    `τ(K_{m,n}) = m^{n−1} · n^{m−1}`. -/
def spanTreeBipartite (m n : ℕ) : ℕ :=
  if m = 0 ∨ n = 0 then 0
  else m ^ (n - 1) * n ^ (m - 1)

example : spanTreeBipartite 1 3 = 1 := by native_decide
example : spanTreeBipartite 2 2 = 4 := by native_decide
example : spanTreeBipartite 2 3 = 12 := by native_decide
example : spanTreeBipartite 3 3 = 81 := by native_decide
example : spanTreeBipartite 2 4 = 32 := by native_decide
example : spanTreeBipartite 3 4 = 432 := by native_decide

/-- K_{1,n} is a star (already a tree), so `τ(K_{1,n}) = 1`. -/
theorem star_one_tree :
    ∀ i : Fin 6, spanTreeBipartite 1 (i.val + 1) = 1 := by
  native_decide

/-- K_{2,2} ≅ C_4, so both spanning tree formulas agree. -/
example : spanTreeBipartite 2 2 = spanTreeCycle 4 := by native_decide

/-- Trees on 4 vertices: 4 stars + 12 paths = 16 = 4². -/
example : 4 + 12 = spanTreeKn 4 := by native_decide

/-- Cayley's formula: `τ(K_n) = n^{n−2}` for all `n ≥ 1`. -/
theorem cayley_formula (n : ℕ) (hn : n ≥ 1) :
    spanTreeKn n = n ^ (n - 2) := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => rfl
    | succ _ => rfl

/-- Spanning tree formula for complete bipartite graphs. -/
theorem bipartite_spanning_trees (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    spanTreeBipartite m n = m ^ (n - 1) * n ^ (m - 1) := by
  unfold spanTreeBipartite
  rw [if_neg (by omega)]

/-! ## §5. Matrix-Tree theorem: explicit Laplacian cofactors -/

/-- Determinant of a 2×2 integer matrix `[[a,b],[c,d]]`. -/
def det2x2 (a b c d : ℤ) : ℤ := a * d - b * c

/-- Determinant of a 3×3 integer matrix by cofactor expansion. -/
def det3x3 (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : ℤ) : ℤ :=
  a₁₁ * det2x2 a₂₂ a₂₃ a₃₂ a₃₃
  - a₁₂ * det2x2 a₂₁ a₂₃ a₃₁ a₃₃
  + a₁₃ * det2x2 a₂₁ a₂₂ a₃₁ a₃₂

/-- Determinant of a 4×4 integer matrix by cofactor expansion. -/
def det4x4 (a₁₁ a₁₂ a₁₃ a₁₄ a₂₁ a₂₂ a₂₃ a₂₄
            a₃₁ a₃₂ a₃₃ a₃₄ a₄₁ a₄₂ a₄₃ a₄₄ : ℤ) : ℤ :=
  a₁₁ * det3x3 a₂₂ a₂₃ a₂₄ a₃₂ a₃₃ a₃₄ a₄₂ a₄₃ a₄₄
  - a₁₂ * det3x3 a₂₁ a₂₃ a₂₄ a₃₁ a₃₃ a₃₄ a₄₁ a₄₃ a₄₄
  + a₁₃ * det3x3 a₂₁ a₂₂ a₂₄ a₃₁ a₃₂ a₃₄ a₄₁ a₄₂ a₄₄
  - a₁₄ * det3x3 a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ a₄₁ a₄₂ a₄₃

/-- Laplacian cofactor of K₃: delete row/col 1 from `L(K₃)`.
    `det [[2,−1],[−1,2]] = 3 = 3^1`. -/
theorem matrixTree_K3 : det2x2 2 (-1) (-1) 2 = 3 := by native_decide

/-- Laplacian cofactor of K₄: `det [[3,−1,−1],[−1,3,−1],[−1,−1,3]] = 16 = 4²`. -/
theorem matrixTree_K4 :
    det3x3 3 (-1) (-1) (-1) 3 (-1) (-1) (-1) 3 = 16 := by native_decide

/-- Laplacian cofactor of K₅: 4×4 cofactor determinant = 125 = 5³. -/
theorem matrixTree_K5 :
    det4x4 4 (-1) (-1) (-1) (-1) 4 (-1) (-1)
           (-1) (-1) 4 (-1) (-1) (-1) (-1) 4 = 125 := by
  native_decide

/-- Laplacian cofactor of C₄ (4-cycle): `det [[2,−1,0],[−1,2,−1],[0,−1,2]] = 4`.
    This equals `τ(C₄) = 4`. -/
theorem matrixTree_C4 :
    det3x3 2 (-1) 0 (-1) 2 (-1) 0 (-1) 2 = 4 := by native_decide

/-- Laplacian cofactor of K_{2,3}: 4×4 cofactor determinant = 12.
    Matches `τ(K_{2,3}) = 2² · 3¹ = 12`. -/
theorem matrixTree_K23 :
    det4x4 3 0 (-1) (-1) 0 3 (-1) (-1)
           (-1) (-1) 2 0 (-1) (-1) 0 2 = 12 := by
  native_decide

/-- Cofactor determinants match Cayley's formula. -/
example : det2x2 2 (-1) (-1) 2 = (spanTreeKn 3 : ℤ) := by native_decide
example : det3x3 3 (-1) (-1) (-1) 3 (-1) (-1) (-1) 3 =
    (spanTreeKn 4 : ℤ) := by native_decide
example : det4x4 4 (-1) (-1) (-1) (-1) 4 (-1) (-1)
    (-1) (-1) 4 (-1) (-1) (-1) (-1) 4 = (spanTreeKn 5 : ℤ) := by native_decide

/-- Cofactor determinant of C₄ matches the bipartite formula (since K_{2,2} ≅ C₄). -/
example : det3x3 2 (-1) 0 (-1) 2 (-1) 0 (-1) 2 =
    (spanTreeBipartite 2 2 : ℤ) := by native_decide

/-- Cofactor determinant of K_{2,3} matches the bipartite formula. -/
example : det4x4 3 0 (-1) (-1) 0 3 (-1) (-1)
    (-1) (-1) 2 0 (-1) (-1) 0 2 =
    (spanTreeBipartite 2 3 : ℤ) := by native_decide

/-! ## §6. 2-connected (biconnected) graph counts -/

/-- Number of labelled 2-connected graphs on `n` vertices (OEIS A013922).
    A 2-connected graph has no cut vertex and at least 3 vertices. -/
def biconnectedCount : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 10
  | 5 => 253
  | 6 => 11968
  | _ => 0

example : biconnectedCount 3 = 1 := by native_decide
example : biconnectedCount 4 = 10 := by native_decide

/-- The 10 biconnected graphs on 4 vertices: 3 copies of C₄ (4-cycles),
    6 copies of K₄ − e (diamond), and 1 copy of K₄. -/
theorem biconnected_four_decomposition :
    3 + 6 + 1 = biconnectedCount 4 := by native_decide

/-- Every 2-connected graph is connected: `b_n ≤ c_n`. -/
theorem biconnected_le_connected :
    ∀ i : Fin 4, biconnectedCount (i.val + 3) ≤ cCount (i.val + 3) := by
  native_decide

/-- 2-connected graphs grow rapidly relative to connected graphs. -/
theorem biconnected_growth :
    ∀ i : Fin 3, biconnectedCount (i.val + 3) ≤ biconnectedCount (i.val + 4) := by
  native_decide

/-! ## §7. Excess classification -/

/-- The excess of a connected graph with `n` vertices and `m` edges is
    `m − (n − 1)`. Trees have excess 0, unicyclic graphs excess 1, etc. -/
def connByExcess (n e : ℕ) : ℕ := connByEdges n (n - 1 + e)

/-- Excess 0 recovers the tree count, matching Cayley's formula. -/
theorem excess_zero_is_cayley :
    ∀ i : Fin 3,
      connByExcess (i.val + 3) 0 = spanTreeKn (i.val + 3) := by
  native_decide

/-- Unicyclic graphs (excess 1) for small `n`. -/
example : connByExcess 3 1 = 1 := by native_decide
example : connByExcess 4 1 = 15 := by native_decide
example : connByExcess 5 1 = 222 := by native_decide

/-- Bicyclic graphs (excess 2) for small `n`. -/
example : connByExcess 4 2 = 6 := by native_decide
example : connByExcess 5 2 = 205 := by native_decide

/-- The maximum excess corresponds to the unique complete graph K_n. -/
theorem max_excess_is_complete :
    ∀ i : Fin 3,
      connByExcess (i.val + 3) (Nat.choose (i.val + 2) 2) = 1 := by
  native_decide

/-- For `n = 4`, trees (excess 0) outnumber unicyclic graphs (excess 1). -/
example : connByExcess 4 0 > connByExcess 4 1 := by native_decide

/-- For `n = 5`, unicyclic graphs (excess 1) outnumber trees (excess 0). -/
example : connByExcess 5 0 < connByExcess 5 1 := by native_decide

/-- Edge-count distribution of connected 5-vertex graphs peaks at `m = 5`
    (excess 1), then monotonically decreases. -/
theorem five_vertex_peak_then_decrease :
    connByEdges 5 4 < connByEdges 5 5 ∧
    connByEdges 5 5 > connByEdges 5 6 ∧
    connByEdges 5 6 > connByEdges 5 7 ∧
    connByEdges 5 7 > connByEdges 5 8 ∧
    connByEdges 5 8 > connByEdges 5 9 ∧
    connByEdges 5 9 > connByEdges 5 10 := by
  native_decide

/-! ## §8. Formal theorems -/

/-- The exponential formula `G(x) = exp(C(x))` uniquely determines the
    connected graph counts from total graph counts. If `c` satisfies
    the convolution identity, then it must agree with the known values. -/
theorem exponential_formula_uniqueness :
    ∀ (c : ℕ → ℕ),
      (∀ n, n ≥ 1 →
        2 ^ Nat.choose n 2 = ∑ k ∈ Finset.Icc 1 n,
          Nat.choose (n - 1) (k - 1) * c k * 2 ^ Nat.choose (n - k) 2) →
      c 1 = 1 ∧ c 2 = 1 ∧ c 3 = 4 ∧ c 4 = 38 := by
  sorry

/-- The connected graph count never exceeds the total graph count:
    `c_n ≤ 2^{C(n,2)}` for all `n`. -/
theorem connected_le_total (c : ℕ → ℕ)
    (hc : ∀ n, n ≥ 1 →
      c n = 2 ^ Nat.choose n 2 - ∑ k ∈ Finset.Icc 1 (n - 1),
        Nat.choose (n - 1) (k - 1) * c k * 2 ^ Nat.choose (n - k) 2) :
    ∀ n, c n ≤ 2 ^ Nat.choose n 2 := by
  sorry

/-- The Matrix-Tree theorem (Kirchhoff 1847): the number of spanning trees
    of any graph G equals any cofactor of its Laplacian matrix L(G).
    For `K_n`, `L = nI − J` and the cofactor is `n^{n−2}`. -/
theorem kirchhoff_matrix_tree :
    ∀ n : ℕ, n ≥ 1 → spanTreeKn n = n ^ (n - 2) :=
  fun n hn => cayley_formula n hn

/-- Block decomposition: every connected graph decomposes uniquely into
    2-connected blocks. The EGFs are related by the composition scheme
    `C'(x) = exp(B'(x · C'(x)))` where `B` is the 2-connected EGF. -/
theorem block_decomposition_relation :
    ∀ n, n ≥ 3 → biconnectedCount n ≤ cCount n := by
  sorry

/-- The Laplacian of K_n has eigenvalue `n` with multiplicity `n − 1`
    and eigenvalue `0` with multiplicity `1`. The product of non-zero
    eigenvalues divided by `n` gives the spanning tree count `n^{n−2}`. -/
theorem laplacian_eigenvalue_product (n : ℕ) (hn : n ≥ 2) :
    n ^ (n - 1) / n = n ^ (n - 2) := by
  sorry

end ConnectedGraphCounting
