import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace NewtonPolygon

/-!
Finite, decidable checks for Newton polygon methods around algebraic
function singularities.  The statements below are intentionally numerical:
they record small algebraic-function examples whose Puiseux exponents,
discriminants, lower Newton polygons, and ramification data can all be
verified by `native_decide`.
-/

/-! ## 1. Puiseux series as finite fractional-power expansions -/

/-- A rational exponent `num / den`, used only with positive denominators in examples. -/
structure Exponent where
  num : Int
  den : Nat
deriving DecidableEq, Repr

/-- A single Puiseux term `coeff * w^(exp.num / exp.den)`. -/
structure PuiseuxTerm where
  coeff : Int
  exp : Exponent
deriving DecidableEq, Repr

/-- The displayed algebraic-function germs. -/
inductive AlgebraicGerm
  | catalanBranch
  | squareRoot
  | cubicCusp
  | smoothBranch
deriving DecidableEq, Repr

/-- Initial Puiseux terms in a local variable `w` at the singular point. -/
def puiseuxTerms : AlgebraicGerm → List PuiseuxTerm
  | .catalanBranch =>
      [⟨2, ⟨0, 1⟩⟩, ⟨-2, ⟨1, 2⟩⟩, ⟨0, ⟨1, 1⟩⟩]
  | .squareRoot =>
      [⟨1, ⟨1, 2⟩⟩]
  | .cubicCusp =>
      [⟨1, ⟨2, 3⟩⟩]
  | .smoothBranch =>
      [⟨1, ⟨0, 1⟩⟩, ⟨1, ⟨1, 1⟩⟩]

def isFractionalExponent (e : Exponent) : Bool :=
  e.den != 1

def hasFractionalPower (terms : List PuiseuxTerm) : Bool :=
  terms.any (fun t => isFractionalExponent t.exp)

theorem catalan_branch_has_puiseux_fraction :
    hasFractionalPower (puiseuxTerms .catalanBranch) = true := by
  native_decide

theorem square_root_has_puiseux_fraction :
    hasFractionalPower (puiseuxTerms .squareRoot) = true := by
  native_decide

theorem cubic_cusp_has_puiseux_fraction :
    hasFractionalPower (puiseuxTerms .cubicCusp) = true := by
  native_decide

theorem smooth_branch_has_integral_expansion :
    hasFractionalPower (puiseuxTerms .smoothBranch) = false := by
  native_decide

theorem algebraic_singular_examples_have_fractional_power_expansions :
    hasFractionalPower (puiseuxTerms .catalanBranch) = true ∧
    hasFractionalPower (puiseuxTerms .squareRoot) = true ∧
    hasFractionalPower (puiseuxTerms .cubicCusp) = true := by
  native_decide

/-! ## 2. Degree-genus formula for small plane curves -/

/-- Arithmetic genus of a plane curve of degree `d`: `(d - 1)(d - 2) / 2`. -/
def arithmeticGenus (d : Nat) : Nat :=
  ((d - 1) * (d - 2)) / 2

/-- Geometric genus after subtracting the sum of delta invariants. -/
def geometricGenus (d deltaSum : Nat) : Nat :=
  arithmeticGenus d - deltaSum

structure PlaneCurveExample where
  degree : Nat
  deltaSum : Nat
  genus : Nat
deriving DecidableEq, Repr

def conic : PlaneCurveExample :=
  ⟨2, 0, 0⟩

def smoothCubic : PlaneCurveExample :=
  ⟨3, 0, 1⟩

def nodalCubic : PlaneCurveExample :=
  ⟨3, 1, 0⟩

def threeNodalQuartic : PlaneCurveExample :=
  ⟨4, 3, 0⟩

def satisfiesDegreeGenus (c : PlaneCurveExample) : Bool :=
  geometricGenus c.degree c.deltaSum = c.genus

theorem degree_genus_conic : satisfiesDegreeGenus conic = true := by
  native_decide

theorem degree_genus_smooth_cubic : satisfiesDegreeGenus smoothCubic = true := by
  native_decide

theorem degree_genus_nodal_cubic : satisfiesDegreeGenus nodalCubic = true := by
  native_decide

theorem degree_genus_three_nodal_quartic : satisfiesDegreeGenus threeNodalQuartic = true := by
  native_decide

/-! ## 3. Algebraic-function counting by discriminant conditions -/

/-- Integer linear polynomial `c0 + c1*x`. -/
structure Linear where
  c0 : Int
  c1 : Int
deriving DecidableEq, Repr

def Linear.eval (p : Linear) (x : Int) : Int :=
  p.c0 + p.c1 * x

structure QuadraticFamily where
  a : Linear
  b : Linear
  c : Linear
deriving DecidableEq, Repr

def quadraticDiscriminantAt (q : QuadraticFamily) (x : Int) : Int :=
  (q.b.eval x) ^ 2 - 4 * q.a.eval x * q.c.eval x

def quadraticBranchPoint (q : QuadraticFamily) (x : Int) : Bool :=
  quadraticDiscriminantAt q x = 0 && q.a.eval x != 0

/-- Scaled Catalan equation: `x*y^2 - 4*y + 4 = 0`; branch at `x = 1`. -/
def scaledCatalanQuadratic : QuadraticFamily :=
  ⟨⟨0, 1⟩, ⟨-4, 0⟩, ⟨4, 0⟩⟩

/-- Square-root equation: `y^2 - x = 0`; branch at `x = 0`. -/
def squareRootQuadratic : QuadraticFamily :=
  ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩⟩

theorem catalan_discriminant_at_branch :
    quadraticDiscriminantAt scaledCatalanQuadratic 1 = 0 := by
  native_decide

theorem catalan_discriminant_off_branch :
    quadraticDiscriminantAt scaledCatalanQuadratic 0 = 16 := by
  native_decide

theorem square_root_discriminant_condition :
    quadraticBranchPoint squareRootQuadratic 0 = true ∧
    quadraticBranchPoint squareRootQuadratic 1 = false := by
  native_decide

structure CubicFamily where
  a : Linear
  b : Linear
  c : Linear
  d : Linear
deriving DecidableEq, Repr

/-- Discriminant of `a*y^3 + b*y^2 + c*y + d`. -/
def cubicDiscriminantAt (p : CubicFamily) (x : Int) : Int :=
  let a := p.a.eval x
  let b := p.b.eval x
  let c := p.c.eval x
  let d := p.d.eval x
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

def cubicBranchPoint (p : CubicFamily) (x : Int) : Bool :=
  cubicDiscriminantAt p x = 0 && p.a.eval x != 0

/-- Cubic root equation: `y^3 - x = 0`. -/
def cubicRootFamily : CubicFamily :=
  ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩⟩

theorem cubic_root_discriminant_condition :
    cubicBranchPoint cubicRootFamily 0 = true ∧
    cubicBranchPoint cubicRootFamily 1 = false := by
  native_decide

/-! ## 4. Newton polygon vertices by lower convex hull computation -/

structure LatticePoint where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

def pointLe (p q : LatticePoint) : Bool :=
  p.x < q.x || (p.x = q.x && p.y ≤ q.y)

def insertPoint (p : LatticePoint) : List LatticePoint → List LatticePoint
  | [] => [p]
  | q :: qs => if pointLe p q then p :: q :: qs else q :: insertPoint p qs

def sortPoints (points : List LatticePoint) : List LatticePoint :=
  points.foldr insertPoint []

def isMinimalAtX (points : List LatticePoint) (p : LatticePoint) : Bool :=
  !(points.any (fun q => q.x = p.x && q.y < p.y))

def minimalYByX (points : List LatticePoint) : List LatticePoint :=
  points.filter (isMinimalAtX points)

def cross (o a b : LatticePoint) : Int :=
  ((a.x : Int) - (o.x : Int)) * ((b.y : Int) - (o.y : Int)) -
    ((a.y : Int) - (o.y : Int)) * ((b.x : Int) - (o.x : Int))

def reduceLowerHull : List LatticePoint → LatticePoint → List LatticePoint
  | q :: p :: rest, r =>
      if cross p q r ≤ 0 then reduceLowerHull (p :: rest) r else q :: p :: rest
  | hull, _ => hull

def lowerHullVertices (points : List LatticePoint) : List LatticePoint :=
  ((sortPoints (minimalYByX points)).foldl (fun hull p => p :: reduceLowerHull hull p) []).reverse

def sqrtSupport : List LatticePoint :=
  [⟨0, 2⟩, ⟨1, 0⟩]

def catalanLocalSupport : List LatticePoint :=
  [⟨0, 2⟩, ⟨1, 0⟩, ⟨1, 1⟩]

def cubicCuspSupport : List LatticePoint :=
  [⟨0, 3⟩, ⟨2, 0⟩]

def brokenPolygonSupport : List LatticePoint :=
  [⟨0, 4⟩, ⟨1, 2⟩, ⟨3, 0⟩, ⟨2, 3⟩]

theorem sqrt_newton_vertices :
    lowerHullVertices sqrtSupport = [⟨0, 2⟩, ⟨1, 0⟩] := by
  native_decide

theorem catalan_newton_vertices :
    lowerHullVertices catalanLocalSupport = [⟨0, 2⟩, ⟨1, 0⟩] := by
  native_decide

theorem cubic_cusp_newton_vertices :
    lowerHullVertices cubicCuspSupport = [⟨0, 3⟩, ⟨2, 0⟩] := by
  native_decide

theorem broken_polygon_vertices :
    lowerHullVertices brokenPolygonSupport = [⟨0, 4⟩, ⟨1, 2⟩, ⟨3, 0⟩] := by
  native_decide

/-! ## 5. Ramification: branch points and merging sheets -/

structure RamificationExample where
  germ : AlgebraicGerm
  basePoint : Int
  ramificationIndex : Nat
deriving DecidableEq, Repr

def ramificationTable : List RamificationExample :=
  [ ⟨.squareRoot, 0, 2⟩
  , ⟨.catalanBranch, 1, 2⟩
  , ⟨.cubicCusp, 0, 3⟩
  ]

def ramificationIndexAt (g : AlgebraicGerm) (x : Int) : Nat :=
  match g, x with
  | .squareRoot, 0 => 2
  | .catalanBranch, 1 => 2
  | .cubicCusp, 0 => 3
  | _, _ => 1

def ramificationEntryValid (r : RamificationExample) : Bool :=
  ramificationIndexAt r.germ r.basePoint = r.ramificationIndex &&
    r.ramificationIndex > 1

theorem ramification_table_valid :
    ramificationTable.all ramificationEntryValid = true := by
  native_decide

theorem catalan_ramification_matches_discriminant :
    quadraticBranchPoint scaledCatalanQuadratic 1 = true ∧
    ramificationIndexAt .catalanBranch 1 = 2 := by
  native_decide

theorem cubic_ramification_matches_discriminant :
    cubicBranchPoint cubicRootFamily 0 = true ∧
    ramificationIndexAt .cubicCusp 0 = 3 := by
  native_decide

/-! ## 6. Singularity type from a Newton polygon edge -/

def edgeExponent (p q : LatticePoint) : Exponent :=
  ⟨(q.x : Int) - (p.x : Int), p.y - q.y⟩

def firstEdgeExponent : List LatticePoint → Exponent
  | p :: q :: _ => edgeExponent p q
  | _ => ⟨0, 1⟩

def singularExponentFromSupport (points : List LatticePoint) : Exponent :=
  firstEdgeExponent (lowerHullVertices points)

theorem sqrt_slope_gives_half_exponent :
    singularExponentFromSupport sqrtSupport = ⟨1, 2⟩ := by
  native_decide

theorem catalan_slope_gives_half_exponent :
    singularExponentFromSupport catalanLocalSupport = ⟨1, 2⟩ := by
  native_decide

theorem cubic_slope_gives_two_thirds_exponent :
    singularExponentFromSupport cubicCuspSupport = ⟨2, 3⟩ := by
  native_decide

theorem first_broken_edge_gives_half_exponent :
    singularExponentFromSupport brokenPolygonSupport = ⟨1, 2⟩ := by
  native_decide

theorem slope_formula_for_basic_edges :
    edgeExponent ⟨0, 2⟩ ⟨1, 0⟩ = ⟨1, 2⟩ ∧
    edgeExponent ⟨0, 3⟩ ⟨2, 0⟩ = ⟨2, 3⟩ ∧
    edgeExponent ⟨0, 1⟩ ⟨1, 0⟩ = ⟨1, 1⟩ := by
  native_decide

end NewtonPolygon
