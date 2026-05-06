import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.EnumerativeGeometry

open Finset Nat


/-!
# Enumerative Geometry and Lattice Counting

Chapter I combinatorial geometry topics:
- Regions of hyperplane arrangements (lines in R², planes in R³)
- Lattice points in simplices
- Triangulations of convex polygons (Catalan numbers)
- Euler characteristic of surfaces / Platonic solids
- Pick's theorem numerical checks
- Dehn–Sommerville relations for simplicial polytopes
-/

/-! ## 1. Regions of hyperplane arrangements -/

/-- Number of regions created by n lines in general position in R².
    Formula: 1 + n + C(n,2) = 1 + n + n(n-1)/2. -/
def lineRegions (n : ℕ) : ℕ := 1 + n + Nat.choose n 2

theorem lineRegions_0 : lineRegions 0 = 1 := by native_decide
theorem lineRegions_1 : lineRegions 1 = 2 := by native_decide
theorem lineRegions_2 : lineRegions 2 = 4 := by native_decide
theorem lineRegions_3 : lineRegions 3 = 7 := by native_decide
theorem lineRegions_4 : lineRegions 4 = 11 := by native_decide
theorem lineRegions_5 : lineRegions 5 = 16 := by native_decide
theorem lineRegions_6 : lineRegions 6 = 22 := by native_decide

/-- All seven values of lineRegions at once. -/
theorem lineRegions_table :
    (List.map lineRegions [0,1,2,3,4,5,6]) = [1,2,4,7,11,16,22] := by
  native_decide

/-- Number of regions created by n planes in general position in R³.
    Formula: 1 + n + C(n,2) + C(n,3). -/
def planeRegions (n : ℕ) : ℕ := 1 + n + Nat.choose n 2 + Nat.choose n 3

theorem planeRegions_0 : planeRegions 0 = 1 := by native_decide
theorem planeRegions_1 : planeRegions 1 = 2 := by native_decide
theorem planeRegions_2 : planeRegions 2 = 4 := by native_decide
theorem planeRegions_3 : planeRegions 3 = 8 := by native_decide
theorem planeRegions_4 : planeRegions 4 = 15 := by native_decide
theorem planeRegions_5 : planeRegions 5 = 26 := by native_decide
theorem planeRegions_6 : planeRegions 6 = 42 := by native_decide

/-- All seven values of planeRegions at once. -/
theorem planeRegions_table :
    (List.map planeRegions [0,1,2,3,4,5,6]) = [1,2,4,8,15,26,42] := by
  native_decide

/-! ## 2. Lattice points in simplex -/

/-- Number of lattice points (x₁, x₂) with x_i ≥ 0 and x₁+x₂ ≤ n.
    Formula: C(n+2, 2). -/
def latticePointsSimplex2 (n : ℕ) : ℕ := Nat.choose (n + 2) 2

theorem latticePointsSimplex2_table :
    (List.map latticePointsSimplex2 [0,1,2,3,4,5,6,7,8]) =
      [1,3,6,10,15,21,28,36,45] := by
  native_decide

-- Individual checks
theorem latticePointsSimplex2_0 : latticePointsSimplex2 0 = 1 := by native_decide
theorem latticePointsSimplex2_1 : latticePointsSimplex2 1 = 3 := by native_decide
theorem latticePointsSimplex2_2 : latticePointsSimplex2 2 = 6 := by native_decide
theorem latticePointsSimplex2_3 : latticePointsSimplex2 3 = 10 := by native_decide
theorem latticePointsSimplex2_4 : latticePointsSimplex2 4 = 15 := by native_decide
theorem latticePointsSimplex2_5 : latticePointsSimplex2 5 = 21 := by native_decide
theorem latticePointsSimplex2_6 : latticePointsSimplex2 6 = 28 := by native_decide
theorem latticePointsSimplex2_7 : latticePointsSimplex2 7 = 36 := by native_decide
theorem latticePointsSimplex2_8 : latticePointsSimplex2 8 = 45 := by native_decide

/-- Number of lattice points (x₁, x₂, x₃) with x_i ≥ 0 and x₁+x₂+x₃ ≤ n.
    Formula: C(n+3, 3). -/
def latticePointsSimplex3 (n : ℕ) : ℕ := Nat.choose (n + 3) 3

theorem latticePointsSimplex3_table :
    (List.map latticePointsSimplex3 [0,1,2,3,4,5,6]) =
      [1,4,10,20,35,56,84] := by
  native_decide

-- Individual checks
theorem latticePointsSimplex3_0 : latticePointsSimplex3 0 = 1 := by native_decide
theorem latticePointsSimplex3_1 : latticePointsSimplex3 1 = 4 := by native_decide
theorem latticePointsSimplex3_2 : latticePointsSimplex3 2 = 10 := by native_decide
theorem latticePointsSimplex3_3 : latticePointsSimplex3 3 = 20 := by native_decide
theorem latticePointsSimplex3_4 : latticePointsSimplex3 4 = 35 := by native_decide
theorem latticePointsSimplex3_5 : latticePointsSimplex3 5 = 56 := by native_decide
theorem latticePointsSimplex3_6 : latticePointsSimplex3 6 = 84 := by native_decide

/-! ## 3. Triangulations of convex polygon -/

/-- Number of triangulations of a convex (n+2)-gon = Catalan number C_n.
    Formula: C(2n, n) / (n+1). -/
def triangulations (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- C_0 = 1: triangle has exactly 1 triangulation (itself)
theorem triangulations_0 : triangulations 0 = 1 := by native_decide
-- C_1 = 1: quadrilateral has 1 triangulation (add a diagonal)
theorem triangulations_1 : triangulations 1 = 1 := by native_decide
-- C_2 = 2: pentagon
theorem triangulations_2 : triangulations 2 = 2 := by native_decide
-- C_3 = 5: hexagon
theorem triangulations_3 : triangulations 3 = 5 := by native_decide
-- C_4 = 14: heptagon
theorem triangulations_4 : triangulations 4 = 14 := by native_decide
-- C_5 = 42: octagon
theorem triangulations_5 : triangulations 5 = 42 := by native_decide

theorem triangulations_table :
    (List.map triangulations [0,1,2,3,4,5]) = [1,1,2,5,14,42] := by
  native_decide

/-! ## 4. Euler characteristic of surfaces -/

/-! For a surface, the Euler characteristic is V - E + F.
    For the sphere (and any convex polyhedron), V - E + F = 2.
    We state these as addition equalities (avoiding subtraction in ℕ):
    V + F = E + 2. -/

-- Tetrahedron: V=4, E=6, F=4
theorem euler_tetrahedron : 4 + 4 = 6 + 2 := by native_decide

-- Cube: V=8, E=12, F=6
theorem euler_cube : 8 + 6 = 12 + 2 := by native_decide

-- Octahedron: V=6, E=12, F=8
theorem euler_octahedron : 6 + 8 = 12 + 2 := by native_decide

-- Dodecahedron: V=20, E=30, F=12
theorem euler_dodecahedron : 20 + 12 = 30 + 2 := by native_decide

-- Icosahedron: V=12, E=30, F=20
theorem euler_icosahedron : 12 + 20 = 30 + 2 := by native_decide

-- All five Platonic solids satisfy the Euler formula
theorem euler_all_platonic :
    (4 + 4 = 6 + 2) ∧   -- tetrahedron
    (8 + 6 = 12 + 2) ∧  -- cube
    (6 + 8 = 12 + 2) ∧  -- octahedron
    (20 + 12 = 30 + 2) ∧ -- dodecahedron
    (12 + 20 = 30 + 2) := by -- icosahedron
  native_decide

/-! ## 5. Pick's theorem numerical checks -/

/-! Pick's theorem: Area = I + B/2 - 1,
    where I = number of interior lattice points,
          B = number of boundary lattice points.
    We verify this as rational arithmetic. -/

-- Unit square: I=0, B=4, Area=1.
-- Check: 0 + 4/2 - 1 = 1
example : (0 : ℚ) + 4/2 - 1 = 1 := by native_decide

-- 3×3 square: I=4, B=12, Area=9.
-- Check: 4 + 12/2 - 1 = 9
example : (4 : ℚ) + 12/2 - 1 = 9 := by native_decide

-- Right triangle (0,0),(3,0),(0,3): I=1, B=9, Area=9/2.
-- (gcd(3,0)+gcd(0,3)+gcd(3,3)=3+3+3=9 boundary pts; interior=1)
-- Check: 1 + 9/2 - 1 = 9/2
example : (1 : ℚ) + (9 : ℚ)/2 - 1 = (9 : ℚ)/2 := by native_decide

-- Named theorems for Pick's checks
theorem picks_unit_square : (0 : ℚ) + 4/2 - 1 = 1 := by native_decide
theorem picks_3x3_square : (4 : ℚ) + 12/2 - 1 = 9 := by native_decide
-- Right triangle (0,0),(3,0),(0,3): I=1, B=9, Area=9/2
theorem picks_right_triangle_3_3 : (1 : ℚ) + (9 : ℚ)/2 - 1 = (9 : ℚ)/2 := by native_decide

-- 2×3 rectangle: I=2, B=10, Area=6.
-- Check: 2 + 10/2 - 1 = 6
theorem picks_2x3_rectangle : (2 : ℚ) + 10/2 - 1 = 6 := by native_decide

/-! ## 6. Dehn–Sommerville relations for simplicial polytopes -/

/-! For a simplicial 3-polytope, every 2-face is a triangle.
    This forces the relation: 2 * f₁ = 3 * f₂
    (each edge borders exactly 2 faces; each triangular face has 3 edges).
    Together with Euler: f₀ - f₁ + f₂ = 2 (i.e., f₀ + f₂ = f₁ + 2). -/

-- Octahedron: V=6, E=12, F=8. All faces are triangles.
-- 2-face count: 2*12 = 3*8 = 24.
theorem dehn_sommerville_octahedron_edge_face : 2 * 12 = 3 * 8 := by native_decide

-- Also satisfies Euler: 6 + 8 = 12 + 2
theorem dehn_sommerville_octahedron_euler : 6 + 8 = 12 + 2 := by native_decide

-- Icosahedron: V=12, E=30, F=20. All faces are triangles.
-- 2-face count: 2*30 = 3*20 = 60.
theorem dehn_sommerville_icosahedron_edge_face : 2 * 30 = 3 * 20 := by native_decide

-- Also satisfies Euler: 12 + 20 = 30 + 2
theorem dehn_sommerville_icosahedron_euler : 12 + 20 = 30 + 2 := by native_decide

-- Tetrahedron: V=4, E=6, F=4. All faces are triangles.
-- 2-face count: 2*6 = 3*4 = 12.
theorem dehn_sommerville_tetrahedron_edge_face : 2 * 6 = 3 * 4 := by native_decide

-- Also satisfies Euler: 4 + 4 = 6 + 2
theorem dehn_sommerville_tetrahedron_euler : 4 + 4 = 6 + 2 := by native_decide

-- Bundled: all three simplicial polytopes satisfy both relations
theorem dehn_sommerville_all :
    -- edge-face relation: 2*E = 3*F
    (2 * 12 = 3 * 8) ∧   -- octahedron
    (2 * 30 = 3 * 20) ∧  -- icosahedron
    (2 * 6 = 3 * 4) ∧    -- tetrahedron
    -- Euler relation: V + F = E + 2
    (6 + 8 = 12 + 2) ∧   -- octahedron
    (12 + 20 = 30 + 2) ∧ -- icosahedron
    (4 + 4 = 6 + 2) := by -- tetrahedron
  native_decide



structure EnumerativeGeometryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def EnumerativeGeometryBudgetCertificate.controlled
    (c : EnumerativeGeometryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def EnumerativeGeometryBudgetCertificate.budgetControlled
    (c : EnumerativeGeometryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def EnumerativeGeometryBudgetCertificate.Ready
    (c : EnumerativeGeometryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def EnumerativeGeometryBudgetCertificate.size
    (c : EnumerativeGeometryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem enumerativeGeometry_budgetCertificate_le_size
    (c : EnumerativeGeometryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleEnumerativeGeometryBudgetCertificate :
    EnumerativeGeometryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleEnumerativeGeometryBudgetCertificate.Ready := by
  constructor
  · norm_num [EnumerativeGeometryBudgetCertificate.controlled,
      sampleEnumerativeGeometryBudgetCertificate]
  · norm_num [EnumerativeGeometryBudgetCertificate.budgetControlled,
      sampleEnumerativeGeometryBudgetCertificate]

example :
    sampleEnumerativeGeometryBudgetCertificate.certificateBudgetWindow ≤
      sampleEnumerativeGeometryBudgetCertificate.size := by
  apply enumerativeGeometry_budgetCertificate_le_size
  constructor
  · norm_num [EnumerativeGeometryBudgetCertificate.controlled,
      sampleEnumerativeGeometryBudgetCertificate]
  · norm_num [EnumerativeGeometryBudgetCertificate.budgetControlled,
      sampleEnumerativeGeometryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleEnumerativeGeometryBudgetCertificate.Ready := by
  constructor
  · norm_num [EnumerativeGeometryBudgetCertificate.controlled,
      sampleEnumerativeGeometryBudgetCertificate]
  · norm_num [EnumerativeGeometryBudgetCertificate.budgetControlled,
      sampleEnumerativeGeometryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleEnumerativeGeometryBudgetCertificate.certificateBudgetWindow ≤
      sampleEnumerativeGeometryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List EnumerativeGeometryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleEnumerativeGeometryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleEnumerativeGeometryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.EnumerativeGeometry
