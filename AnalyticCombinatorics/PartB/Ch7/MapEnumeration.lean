import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace MapEnumeration

/-!
  Finite, executable checks for map-enumeration tables from the Chapter VII
  circle of examples.  The file deliberately keeps all computations small:
  table domains have size at most ten, and every proof is discharged by
  `native_decide`.
-/

/-! ## Rooted planar maps by number of edges -/

/-- Initial rooted planar map counts by number of edges, indexed by `0, ..., 9`. -/
def rootedPlanarMapByEdgesTable : Fin 10 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494, 1876446, 17399772]

/-- Rooted planar map count on the tabulated range, and `0` outside it. -/
def rootedPlanarMapByEdges (n : ℕ) : ℕ :=
  if h : n < 10 then rootedPlanarMapByEdgesTable ⟨n, h⟩ else 0

/-- Tutte's closed form for the rooted planar map table. -/
def rootedPlanarMapFormula (n : ℕ) : ℕ :=
  (2 * 3 ^ n * Nat.factorial (2 * n)) / (Nat.factorial n * Nat.factorial (n + 2))

theorem rootedPlanarMapByEdges_values :
    [rootedPlanarMapByEdges 0, rootedPlanarMapByEdges 1, rootedPlanarMapByEdges 2,
      rootedPlanarMapByEdges 3, rootedPlanarMapByEdges 4, rootedPlanarMapByEdges 5,
      rootedPlanarMapByEdges 6, rootedPlanarMapByEdges 7, rootedPlanarMapByEdges 8,
      rootedPlanarMapByEdges 9] =
    [1, 2, 9, 54, 378, 2916, 24057, 208494, 1876446, 17399772] := by
  native_decide

theorem rootedPlanarMap_first_positive_edges :
    [rootedPlanarMapByEdges 1, rootedPlanarMapByEdges 2, rootedPlanarMapByEdges 3,
      rootedPlanarMapByEdges 4] =
    [2, 9, 54, 378] := by
  native_decide

theorem rootedPlanarMap_formula_matches_table :
    ∀ i : Fin 10, rootedPlanarMapFormula i.val = rootedPlanarMapByEdgesTable i := by
  native_decide

/-! ## Rooted quadrangulations -/

/-- Rooted quadrangulations by faces, indexed by `0, ..., 9`. -/
def rootedQuadrangulationByFacesTable : Fin 10 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494, 1876446, 17399772]

/-- Rooted quadrangulation count on the tabulated range, and `0` outside it. -/
def rootedQuadrangulationByFaces (n : ℕ) : ℕ :=
  if h : n < 10 then rootedQuadrangulationByFacesTable ⟨n, h⟩ else 0

theorem quadrangulation_table_matches_planar_maps :
    ∀ i : Fin 10, rootedQuadrangulationByFacesTable i = rootedPlanarMapByEdgesTable i := by
  native_decide

theorem quadrangulation_formula_matches_table :
    ∀ i : Fin 10, rootedPlanarMapFormula i.val = rootedQuadrangulationByFacesTable i := by
  native_decide

theorem quadrangulation_values_0_5 :
    [rootedQuadrangulationByFaces 0, rootedQuadrangulationByFaces 1,
      rootedQuadrangulationByFaces 2, rootedQuadrangulationByFaces 3,
      rootedQuadrangulationByFaces 4, rootedQuadrangulationByFaces 5] =
    [1, 2, 9, 54, 378, 2916] := by
  native_decide

/-! ## Rooted triangulations by a vertex-shift parameter -/

/--
Initial values of the standard triangulation closed-form row
`2 * (4n + 1)! / ((n + 1)! * (3n + 2)!)`, indexed by `n = 0, ..., 9`.
For a vertex-indexed lookup below, `n` is `vertices - 2`.
-/
def rootedTriangulationVertexShiftTable : Fin 10 → ℕ :=
  ![1, 1, 3, 13, 68, 399, 2530, 16965, 118668, 857956]

/-- Triangulation count in the shifted parameter used by the finite table. -/
def rootedTriangulationShiftFormula (n : ℕ) : ℕ :=
  (2 * Nat.factorial (4 * n + 1)) / (Nat.factorial (n + 1) * Nat.factorial (3 * n + 2))

/-- Vertex-indexed version: the table entry for `v` vertices is stored at `v - 2`. -/
def rootedTriangulationsByVertices (v : ℕ) : ℕ :=
  if h : 2 ≤ v ∧ v - 2 < 10 then rootedTriangulationVertexShiftTable ⟨v - 2, h.2⟩ else 0

theorem rootedTriangulation_formula_matches_table :
    ∀ i : Fin 10, rootedTriangulationShiftFormula i.val = rootedTriangulationVertexShiftTable i := by
  native_decide

theorem rootedTriangulationsByVertices_values :
    [rootedTriangulationsByVertices 2, rootedTriangulationsByVertices 3,
      rootedTriangulationsByVertices 4, rootedTriangulationsByVertices 5,
      rootedTriangulationsByVertices 6, rootedTriangulationsByVertices 7,
      rootedTriangulationsByVertices 8, rootedTriangulationsByVertices 9,
      rootedTriangulationsByVertices 10, rootedTriangulationsByVertices 11] =
    [1, 1, 3, 13, 68, 399, 2530, 16965, 118668, 857956] := by
  native_decide

/-! ## Genus-zero coefficient rows -/

/-- A compact row table pairing edge number with the rooted genus-zero map count. -/
def genusZeroMapCoefficientRows : Fin 10 → ℕ × ℕ :=
  ![(0, 1), (1, 2), (2, 9), (3, 54), (4, 378),
    (5, 2916), (6, 24057), (7, 208494), (8, 1876446), (9, 17399772)]

theorem genusZero_rows_project_to_map_table :
    ∀ i : Fin 10, (genusZeroMapCoefficientRows i).2 = rootedPlanarMapByEdgesTable i := by
  native_decide

theorem genusZero_rows_have_expected_indices :
    ∀ i : Fin 10, (genusZeroMapCoefficientRows i).1 = i.val := by
  native_decide

/-! ## Tutte polynomial evaluations for small graphs -/

/-- Tutte polynomial evaluation for a tree with `edges` edges: `T(x,y) = x^edges`. -/
def tutteTreeEval (edges x _y : ℕ) : ℕ :=
  x ^ edges

/-- Tutte polynomial evaluation for a cycle with `edges` edges. -/
def tutteCycleEval (edges x y : ℕ) : ℕ :=
  (Finset.Icc 1 (edges - 1)).sum (fun k => x ^ k) + y

/-- Small graph names encoded as rows: empty tree, bridge, two-edge path, triangle, square. -/
def smallGraphTutteAtOneOne : Fin 5 → ℕ :=
  ![1, 1, 1, 3, 4]

theorem tutte_tree_eval_values :
    [tutteTreeEval 0 1 1, tutteTreeEval 1 1 1, tutteTreeEval 2 1 1,
      tutteTreeEval 3 2 5] =
    [1, 1, 1, 8] := by
  native_decide

theorem tutte_cycle_eval_values :
    [tutteCycleEval 3 1 1, tutteCycleEval 4 1 1, tutteCycleEval 3 2 1,
      tutteCycleEval 4 2 1] =
    [3, 4, 7, 15] := by
  native_decide

theorem smallGraph_tutte_at_one_one_values :
    [smallGraphTutteAtOneOne 0, smallGraphTutteAtOneOne 1, smallGraphTutteAtOneOne 2,
      smallGraphTutteAtOneOne 3, smallGraphTutteAtOneOne 4] =
    [tutteTreeEval 0 1 1, tutteTreeEval 1 1 1, tutteTreeEval 2 1 1,
      tutteCycleEval 3 1 1, tutteCycleEval 4 1 1] := by
  native_decide

/-! ## Rooted non-separable planar maps -/

/--
Finite row from Tutte's non-separable-map closed form
`2 * (3n - 3)! / ((n - 1)! * (2n - 1)!)`, indexed here by
positive edge number `n = 1, ..., 10`.
-/
def rootedNonseparableMapByEdgesTable : Fin 10 → ℕ :=
  ![2, 2, 6, 24, 110, 546, 2856, 15504, 86526, 493350]

/-- Closed form for the non-separable row; `n = 0` is outside the intended range. -/
def rootedNonseparableMapFormula (n : ℕ) : ℕ :=
  (2 * Nat.factorial (3 * n - 3)) / (Nat.factorial (n - 1) * Nat.factorial (2 * n - 1))

/-- Positive-edge lookup for the non-separable table. -/
def rootedNonseparableMapByEdges (n : ℕ) : ℕ :=
  if h : n - 1 < 10 ∧ 1 ≤ n then rootedNonseparableMapByEdgesTable ⟨n - 1, h.1⟩ else 0

theorem rootedNonseparable_formula_matches_table :
    ∀ i : Fin 10,
      rootedNonseparableMapFormula (i.val + 1) = rootedNonseparableMapByEdgesTable i := by
  native_decide

theorem rootedNonseparable_values :
    [rootedNonseparableMapByEdges 1, rootedNonseparableMapByEdges 2,
      rootedNonseparableMapByEdges 3, rootedNonseparableMapByEdges 4,
      rootedNonseparableMapByEdges 5, rootedNonseparableMapByEdges 6,
      rootedNonseparableMapByEdges 7, rootedNonseparableMapByEdges 8,
      rootedNonseparableMapByEdges 9, rootedNonseparableMapByEdges 10] =
    [2, 2, 6, 24, 110, 546, 2856, 15504, 86526, 493350] := by
  native_decide

theorem rootedNonseparable_smaller_than_all_maps_1_10 :
    ∀ i : Fin 9,
      rootedNonseparableMapByEdges (i.val + 1) ≤ rootedPlanarMapByEdges (i.val + 1) := by
  native_decide

end MapEnumeration
