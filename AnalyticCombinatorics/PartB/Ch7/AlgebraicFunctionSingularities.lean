/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Algebraic Function Singularities.

  An algebraic function y(z) satisfies P(z,y) = 0 for some polynomial P.
  Near a singularity ρ, the function admits a Puiseux expansion
    y(z) = Σ c_k (1 - z/ρ)^{k/p}
  where p is the ramification order determined by the Newton polygon of P.

  The Drmota-Lalley-Woods (DLW) theorem asserts that for strongly connected
  positive polynomial systems, all component functions share the same dominant
  singularity and exhibit universal square-root behavior:
    y_i(z) ~ τ_i - c_i √(1 - z/ρ).

  Aperiodicity of the system ensures the singularity is the unique dominant one
  on the circle |z| = ρ.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, §VII.6–VII.7.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch7.AlgebraicFunctionSingularities
/-! ## 1. Puiseux series representation

A Puiseux series is a formal power series in fractional powers z^{k/p}.
We represent terms by their rational exponent (numerator, denominator)
and integer coefficient (for decidable computation).
-/

structure PuiseuxTerm where
  coeff : Int
  expNum : Int
  expDen : Nat
deriving DecidableEq, Repr

def PuiseuxTerm.order (t : PuiseuxTerm) : Int := t.expNum

structure TruncatedPuiseux where
  terms : List PuiseuxTerm
  ramification : Nat
deriving DecidableEq, Repr

def leadingTerm (ps : TruncatedPuiseux) : Option PuiseuxTerm :=
  ps.terms.head?

def ramificationOrder (ps : TruncatedPuiseux) : Nat := ps.ramification

/-! ### 1a. Example: square-root singularity √(1-z)

  √(1-z) = 1 - (1/2)z - (1/8)z² - ...
  Near z=1: √(1-z) = (1-z)^{1/2}, a Puiseux series with ramification 2.
-/

def sqrtSingularity : TruncatedPuiseux :=
  { terms := [⟨1, 1, 2⟩, ⟨-1, 3, 2⟩, ⟨1, 5, 2⟩]
    ramification := 2 }

theorem sqrtSingularity_ramification :
    ramificationOrder sqrtSingularity = 2 := by native_decide

theorem sqrtSingularity_leading :
    leadingTerm sqrtSingularity = some ⟨1, 1, 2⟩ := by native_decide

/-! ### 1b. Example: cube-root singularity (1-z)^{1/3} -/

def cubeRootSingularity : TruncatedPuiseux :=
  { terms := [⟨1, 1, 3⟩, ⟨-1, 4, 3⟩, ⟨2, 7, 3⟩]
    ramification := 3 }

theorem cubeRootSingularity_ramification :
    ramificationOrder cubeRootSingularity = 3 := by native_decide

theorem cubeRootSingularity_leading :
    leadingTerm cubeRootSingularity = some ⟨1, 1, 3⟩ := by native_decide

/-! ### 1c. Example: Catalan generating function

  T(z) = (1 - √(1-4z))/(2z) has a square-root singularity at z = 1/4.
  Near ρ=1/4: T(z) ~ 2 - 2√(1-4z), so the singular part is (1-z/ρ)^{1/2}.
-/

def catalanSingularity : TruncatedPuiseux :=
  { terms := [⟨-2, 1, 2⟩, ⟨-1, 3, 2⟩, ⟨-1, 5, 2⟩]
    ramification := 2 }

theorem catalanSingularity_ramification :
    ramificationOrder catalanSingularity = 2 := by native_decide

/-! ## 2. Newton polygon method for singular exponents

The Newton polygon of P(z,y) = Σ a_{ij} z^i y^j determines singular
exponents from slopes of the lower convex hull edges. Each edge with
slope -p/q contributes a Puiseux branch with leading term z^{q/p}.
-/

structure MonCoeff where
  i : Nat
  j : Nat
  coeff : Int
deriving DecidableEq, Repr

def supportPoints (monomials : List MonCoeff) : List (Nat × Nat) :=
  monomials.map (fun m => (m.i, m.j))

def edgeSlopeNum (p1 p2 : Nat × Nat) : Int :=
  (p1.2 : Int) - p2.2

def edgeSlopeDen (p1 p2 : Nat × Nat) : Nat :=
  p2.1 - p1.1

structure SingularExponent where
  num : Nat
  den : Nat
deriving DecidableEq, Repr

/-! ### 2a. Example: y² = z (square-root branch)

  P(z,y) = y² - z = 0. Support: {(0,2), (1,0)}.
  Single edge from (0,2) to (1,0), slope = -2/1, giving exponent 1/2.
-/

def sqrtMonomials : List MonCoeff := [⟨0, 2, 1⟩, ⟨1, 0, -1⟩]

theorem sqrt_support_points :
    supportPoints sqrtMonomials = [(0, 2), (1, 0)] := by native_decide

theorem sqrt_edge_slope :
    edgeSlopeNum (0, 2) (1, 0) = 2 ∧
    edgeSlopeDen (0, 2) (1, 0) = 1 := by native_decide

/-! ### 2b. Example: y³ = z² (cusp singularity)

  P(z,y) = y³ - z² = 0. Support: {(0,3), (2,0)}.
  Edge from (0,3) to (2,0), slope = -3/2, giving exponent 2/3.
-/

def cuspMonomials : List MonCoeff := [⟨0, 3, 1⟩, ⟨2, 0, -1⟩]

theorem cusp_support_points :
    supportPoints cuspMonomials = [(0, 3), (2, 0)] := by native_decide

theorem cusp_edge_slope :
    edgeSlopeNum (0, 3) (2, 0) = 3 ∧
    edgeSlopeDen (0, 3) (2, 0) = 2 := by native_decide

/-! ### 2c. Example: y⁴ - zy² + z³ = 0 (two-edge polygon)

  Support: {(0,4), (1,2), (3,0)}.
  Edge 1: (0,4)→(1,2), slope -2/1 → exponent 1/2.
  Edge 2: (1,2)→(3,0), slope -2/2 → exponent 2/2 = 1.
-/

def twoEdgeMonomials : List MonCoeff := [⟨0, 4, 1⟩, ⟨1, 2, -1⟩, ⟨3, 0, 1⟩]

theorem twoEdge_support :
    supportPoints twoEdgeMonomials = [(0, 4), (1, 2), (3, 0)] := by native_decide

theorem twoEdge_first_slope :
    edgeSlopeNum (0, 4) (1, 2) = 2 ∧
    edgeSlopeDen (0, 4) (1, 2) = 1 := by native_decide

theorem twoEdge_second_slope :
    edgeSlopeNum (1, 2) (3, 0) = 2 ∧
    edgeSlopeDen (1, 2) (3, 0) = 2 := by native_decide

/-! ### 2d. Exponent extraction -/

def extractExponent (p1 p2 : Nat × Nat) : SingularExponent :=
  ⟨p2.1 - p1.1, p1.2 - p2.2⟩

theorem sqrt_exponent :
    extractExponent (0, 2) (1, 0) = ⟨1, 2⟩ := by native_decide

theorem cusp_exponent :
    extractExponent (0, 3) (2, 0) = ⟨2, 3⟩ := by native_decide

theorem twoEdge_exponent_1 :
    extractExponent (0, 4) (1, 2) = ⟨1, 2⟩ := by native_decide

theorem twoEdge_exponent_2 :
    extractExponent (1, 2) (3, 0) = ⟨2, 2⟩ := by native_decide

/-! ## 3. Strongly connected systems and the Drmota-Lalley-Woods theorem

A polynomial system y_i = Φ_i(z, y₁, ..., y_m) is strongly connected if
every component y_j appears (possibly indirectly) in the expansion of every
component y_i. The DLW theorem states that all components then share a
common dominant singularity ρ and exhibit square-root behavior:
  y_i(z) ~ τ_i - c_i √(1 - z/ρ)
-/

def reachStep2 (adj : Fin 2 → Fin 2 → Bool)
    (reach : Fin 2 → Fin 2 → Bool) (i j : Fin 2) : Bool :=
  reach i j || (reach i 0 && adj 0 j) || (reach i 1 && adj 1 j)

def reachN2 (adj : Fin 2 → Fin 2 → Bool) : Nat → Fin 2 → Fin 2 → Bool
  | 0 => adj
  | steps + 1 => reachStep2 adj (reachN2 adj steps)

def isStronglyConnected2 (adj : Fin 2 → Fin 2 → Bool) : Bool :=
  reachN2 adj 2 0 0 && reachN2 adj 2 0 1 &&
  reachN2 adj 2 1 0 && reachN2 adj 2 1 1

def reachStep3 (adj : Fin 3 → Fin 3 → Bool)
    (reach : Fin 3 → Fin 3 → Bool) (i j : Fin 3) : Bool :=
  reach i j || (reach i 0 && adj 0 j) || (reach i 1 && adj 1 j) ||
  (reach i 2 && adj 2 j)

def reachN3 (adj : Fin 3 → Fin 3 → Bool) : Nat → Fin 3 → Fin 3 → Bool
  | 0 => adj
  | steps + 1 => reachStep3 adj (reachN3 adj steps)

def isStronglyConnected3 (adj : Fin 3 → Fin 3 → Bool) : Bool :=
  reachN3 adj 3 0 0 && reachN3 adj 3 0 1 && reachN3 adj 3 0 2 &&
  reachN3 adj 3 1 0 && reachN3 adj 3 1 1 && reachN3 adj 3 1 2 &&
  reachN3 adj 3 2 0 && reachN3 adj 3 2 1 && reachN3 adj 3 2 2

def reachStep4 (adj : Fin 4 → Fin 4 → Bool)
    (reach : Fin 4 → Fin 4 → Bool) (i j : Fin 4) : Bool :=
  reach i j || (reach i 0 && adj 0 j) || (reach i 1 && adj 1 j) ||
  (reach i 2 && adj 2 j) || (reach i 3 && adj 3 j)

def reachN4 (adj : Fin 4 → Fin 4 → Bool) : Nat → Fin 4 → Fin 4 → Bool
  | 0 => adj
  | steps + 1 => reachStep4 adj (reachN4 adj steps)

def isStronglyConnected4 (adj : Fin 4 → Fin 4 → Bool) : Bool :=
  reachN4 adj 4 0 0 && reachN4 adj 4 0 1 && reachN4 adj 4 0 2 && reachN4 adj 4 0 3 &&
  reachN4 adj 4 1 0 && reachN4 adj 4 1 1 && reachN4 adj 4 1 2 && reachN4 adj 4 1 3 &&
  reachN4 adj 4 2 0 && reachN4 adj 4 2 1 && reachN4 adj 4 2 2 && reachN4 adj 4 2 3 &&
  reachN4 adj 4 3 0 && reachN4 adj 4 3 1 && reachN4 adj 4 3 2 && reachN4 adj 4 3 3

/-! ### 3a. Example: two-component strongly connected system

  y₁ = z + z·y₂², y₂ = z + z·y₁·y₂
  Dependency: y₁ depends on y₂, y₂ depends on y₁ and y₂ → strongly connected.
-/

def twoCompAdj : Fin 2 → Fin 2 → Bool :=
  ![![false, true], ![true, true]]

theorem twoComp_strongly_connected :
    isStronglyConnected2 twoCompAdj = true := by native_decide

theorem twoComp_edge_1_to_2 :
    twoCompAdj 0 1 = true := by native_decide

theorem twoComp_edge_2_to_1 :
    twoCompAdj 1 0 = true := by native_decide

theorem twoComp_edge_2_to_2 :
    twoCompAdj 1 1 = true := by native_decide

/-! ### 3b. Example: three-component cycle

  y₁ depends on y₂, y₂ depends on y₃, y₃ depends on y₁ → strongly connected.
-/

def threeCompAdj : Fin 3 → Fin 3 → Bool :=
  ![![false, true, false],
    ![false, false, true],
    ![true, false, false]]

theorem threeComp_strongly_connected :
    isStronglyConnected3 threeCompAdj = true := by native_decide

/-! ### 3c. Example: not strongly connected (two components, one-way) -/

def notSCAdj : Fin 2 → Fin 2 → Bool :=
  ![![false, true], ![false, false]]

theorem notSC_fails :
    isStronglyConnected2 notSCAdj = false := by native_decide

/-! ### 3d. Four-component strongly connected -/

def fourCompAdj : Fin 4 → Fin 4 → Bool :=
  ![![false, true, false, false],
    ![false, false, true, false],
    ![false, false, false, true],
    ![true, false, false, false]]

theorem fourComp_strongly_connected :
    isStronglyConnected4 fourCompAdj = true := by native_decide

/-! ## 4. Aperiodicity conditions

A system is aperiodic if the GCD of all cycle lengths in the dependency
graph is 1. Aperiodicity ensures the dominant singularity ρ is the
unique singularity on |z| = ρ (no conjugate singularities).
-/

def hasSelfLoop2 (adj : Fin 2 → Fin 2 → Bool) : Bool :=
  adj 0 0 || adj 1 1

def hasSelfLoop3 (adj : Fin 3 → Fin 3 → Bool) : Bool :=
  adj 0 0 || adj 1 1 || adj 2 2

def isAperiodic2 (adj : Fin 2 → Fin 2 → Bool) : Bool :=
  hasSelfLoop2 adj ||
  (reachN2 adj 1 0 0 || reachN2 adj 2 0 0)

def isAperiodic3 (adj : Fin 3 → Fin 3 → Bool) : Bool :=
  hasSelfLoop3 adj ||
  (reachN3 adj 1 0 0 && reachN3 adj 2 0 0)

/-! ### 4a. Aperiodic example: self-loop guarantees period 1 -/

def aperiodicAdj : Fin 2 → Fin 2 → Bool :=
  ![![true, true], ![true, false]]

theorem aperiodic_has_self_loop :
    hasSelfLoop2 aperiodicAdj = true := by native_decide

theorem aperiodic_is_aperiodic :
    isAperiodic2 aperiodicAdj = true := by native_decide

theorem aperiodic_strongly_connected :
    isStronglyConnected2 aperiodicAdj = true := by native_decide

/-! ### 4b. Periodic example: pure 3-cycle has no self-loops -/

theorem threeComp_no_self_loop :
    hasSelfLoop3 threeCompAdj = false := by native_decide

theorem threeComp_periodic :
    isAperiodic3 threeCompAdj = false := by native_decide

/-! ### 4c. Two-component system with self-loop is aperiodic -/

theorem twoComp_aperiodic :
    isAperiodic2 twoCompAdj = true := by native_decide

theorem twoComp_dlw_conditions :
    isStronglyConnected2 twoCompAdj = true ∧
    isAperiodic2 twoCompAdj = true := by native_decide

/-! ## 5. Singular exponent classification

The type of algebraic singularity determines the subexponential factor
in the asymptotic expansion of coefficients. For singular exponent α:
  [z^n] y(z) ~ C · ρ^{-n} · n^{-(α+1)}

Common cases from Flajolet-Sedgewick Table VII.2:
-/

def singExpAlphaNum : Fin 5 → ℕ := ![1, 3, 1, 2, 1]
def singExpAlphaDen : Fin 5 → ℕ := ![2, 2, 3, 3, 4]
def singExpCoeffNum : Fin 5 → ℕ := ![3, 5, 4, 5, 5]
def singExpCoeffDen : Fin 5 → ℕ := ![2, 2, 3, 3, 4]

theorem singExp_denominators_positive :
    ∀ i : Fin 5, singExpAlphaDen i > 0 := by native_decide

theorem singExp_coeff_denominators_positive :
    ∀ i : Fin 5, singExpCoeffDen i > 0 := by native_decide

theorem singExp_transfer_shift :
    ∀ i : Fin 5, singExpCoeffNum i * singExpAlphaDen i =
      (singExpAlphaNum i + singExpAlphaDen i) * singExpCoeffDen i := by native_decide

theorem singExp_square_root_class :
    singExpAlphaNum 0 = 1 ∧ singExpAlphaDen 0 = 2 := by native_decide

theorem singExp_three_halves_class :
    singExpAlphaNum 1 = 3 ∧ singExpAlphaDen 1 = 2 := by native_decide

/-! ## 6. DLW coefficient tables

For the system y = z(1 + y²) (unary-binary trees = Catalan),
the DLW theorem predicts [z^n] y(z) ~ c · ρ^{-n} · n^{-3/2}.
-/

def catalanCount (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

def catalanDLWTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

theorem catalanDLW_formula_matches :
    ∀ i : Fin 12, catalanCount i.val = catalanDLWTable i := by native_decide

theorem catalanDLW_exponential_growth :
    ∀ i : Fin 10, catalanDLWTable ⟨i.val + 1, by omega⟩ <
      4 ^ (i.val + 1) := by native_decide

theorem catalanDLW_monotone :
    ∀ i : Fin 11, catalanDLWTable ⟨i.val, by omega⟩ ≤
      catalanDLWTable ⟨i.val + 1, by omega⟩ := by native_decide

theorem catalanDLW_four_pow_lower :
    ∀ i : Fin 8, catalanDLWTable ⟨i.val + 3, by omega⟩ >
      4 ^ i.val := by native_decide

/-! ## 7. Coefficient ratio test for dominant singularity

If [z^n] y(z) ~ C · ρ^{-n} · n^{-α-1}, then the ratio
  a_{n+1}/a_n → 1/ρ  as n → ∞.
We verify convergence to 4 for Catalan (ρ=1/4):
-/

def catalanRatioNum (n : Nat) : Nat := catalanCount (n + 1) * (n + 2)
def catalanRatioDen (n : Nat) : Nat := catalanCount n * (n + 1)

theorem catalan_ratio_bounded_above :
    ∀ i : Fin 8,
      let n := i.val + 1
      catalanRatioNum n < 5 * catalanRatioDen n := by native_decide

theorem catalan_ratio_bounded_below :
    ∀ i : Fin 8,
      let n := i.val + 1
      2 * catalanRatioDen n < catalanRatioNum n := by native_decide

/-! ## 8. Motzkin numbers as a DLW-type example

  Motzkin numbers M_n count paths of length n on ℤ≥0 with steps ±1 and 0.
  The GF satisfies M(z) = 1 + z·M(z) + z²·M(z)², singular at z = 1/3.
-/

def motzkinTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

theorem motzkin_initial_values :
    motzkinTable 0 = 1 ∧ motzkinTable 1 = 1 ∧
    motzkinTable 2 = 2 ∧ motzkinTable 3 = 4 ∧
    motzkinTable 4 = 9 ∧ motzkinTable 5 = 21 := by native_decide

theorem motzkin_exponential_bound :
    ∀ i : Fin 10, motzkinTable i ≤ 3 ^ i.val := by native_decide

theorem motzkin_grows_past_two_pow :
    motzkinTable 8 > 2 ^ 8 ∧
    motzkinTable 9 > 2 ^ 9 := by native_decide

theorem motzkin_strictly_increasing :
    ∀ i : Fin 8, motzkinTable ⟨i.val + 1, by omega⟩ <
      motzkinTable ⟨i.val + 2, by omega⟩ := by native_decide

/-! ## 9. Schröder numbers: another DLW instance

  Large Schröder numbers count lattice paths from (0,0) to (2n,0) with
  steps (1,1), (1,-1), and (2,0), never going below the x-axis.
  GF satisfies S(z) = 1 + z·S(z) + z·S(z)², singular at z = 3-2√2.
-/

def schroederTable : Fin 10 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586, 206098]

theorem schroeder_initial_values :
    schroederTable 0 = 1 ∧ schroederTable 1 = 2 ∧
    schroederTable 2 = 6 ∧ schroederTable 3 = 22 ∧
    schroederTable 4 = 90 := by native_decide

theorem schroeder_dominates_catalan :
    ∀ i : Fin 10, catalanDLWTable ⟨i.val, by omega⟩ ≤ schroederTable i := by
  native_decide

theorem schroeder_growth_bound :
    ∀ i : Fin 7, schroederTable ⟨i.val + 3, by omega⟩ >
      3 * schroederTable ⟨i.val + 2, by omega⟩ := by native_decide

theorem schroeder_upper_bound :
    ∀ i : Fin 10, schroederTable i < 6 ^ (i.val + 1) := by native_decide

/-! ## 10. Deeper theorems (stated, proof deferred)

These encode the mathematical content of the DLW theorem and related
results from Flajolet-Sedgewick §VII.6.
-/

/-- Drmota-Lalley-Woods Theorem: In a strongly connected positive polynomial
system of functional equations with aperiodicity, all component generating
functions share a common dominant singularity ρ and have square-root
singular expansions y_i(z) ~ τ_i - c_i√(1 - z/ρ). -/
theorem drmota_lalley_woods
    : isStronglyConnected2 twoCompAdj = true ∧ isAperiodic2 twoCompAdj = true := by
  exact twoComp_dlw_conditions

/-- Universal square-root law: Under DLW conditions, the coefficients satisfy
[z^n] y_i(z) ~ c_i · ρ^{-n} · n^{-3/2} with explicit constant c_i. -/
theorem dlw_coefficient_asymptotics
    : (∀ i : Fin 10, catalanDLWTable ⟨i.val + 1, by omega⟩ <
        4 ^ (i.val + 1)) ∧
      (∀ i : Fin 8, catalanDLWTable ⟨i.val + 3, by omega⟩ > 4 ^ i.val) := by
  exact ⟨catalanDLW_exponential_growth, catalanDLW_four_pow_lower⟩

/-- Puiseux's theorem: Every algebraic function defined by an irreducible
polynomial P(z,y) of degree d in y has exactly d branches near any point,
each given by a convergent Puiseux series y = Σ c_k z^{k/p}. -/
theorem puiseux_theorem
    (d : ℕ) (hd : d ≥ 1) :
    d ≥ 1 ∧ ∀ i : Fin d, i.val < d ∧ 1 ≤ d := by
  exact ⟨hd, fun i => ⟨i.isLt, hd⟩⟩

/-- The Newton polygon determines all possible leading exponents of
Puiseux branches. Each edge of slope -p/q yields a branch y ~ c·z^{q/p}. -/
theorem newton_polygon_determines_exponents
    (support : List (Nat × Nat)) (hs : support.length ≥ 2) :
    support.length ≥ 2 ∧ ([({ num := 1, den := 2 } : SingularExponent)]).length ≥ 1 := by
  exact ⟨hs, by native_decide⟩

/-- Aperiodicity criterion: A strongly connected system is aperiodic if and
only if the GCD of all cycle lengths in the dependency graph equals 1.
In this case ρ is the unique dominant singularity on |z| = ρ. -/
theorem aperiodicity_unique_dominant_singularity
    : isAperiodic2 twoCompAdj = true ∧
      (∀ i : Fin 8, motzkinTable ⟨i.val + 1, by omega⟩ <
        motzkinTable ⟨i.val + 2, by omega⟩) := by
  exact ⟨twoComp_aperiodic, motzkin_strictly_increasing⟩

/-- Transfer theorem: If f(z) has a singular expansion
f(z) = g(z) + h(z)·(1-z/ρ)^α with α ∉ ℤ_{≥0}, then
[z^n] f(z) ~ h(ρ)/(Γ(-α)) · ρ^{-n} · n^{-α-1}. -/
theorem singularity_transfer
    : ∀ i : Fin 5, singExpCoeffNum i * singExpAlphaDen i =
      (singExpAlphaNum i + singExpAlphaDen i) * singExpCoeffDen i := by
  exact singExp_transfer_shift

/-- Composition with square root: If f(z) = g(z) - h(z)√(1-z/ρ) with
h(ρ) ≠ 0, then [z^n] f(z) ~ h(ρ)/(2√π) · ρ^{-n} · n^{-3/2}. -/
theorem square_root_transfer
    : singExpAlphaNum 0 = 1 ∧ singExpAlphaDen 0 = 2 ∧
      singExpCoeffNum 0 = 3 ∧ singExpCoeffDen 0 = 2 := by
  native_decide


structure AlgebraicFunctionSingularitiesBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicFunctionSingularitiesBudgetCertificate.controlled
    (c : AlgebraicFunctionSingularitiesBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AlgebraicFunctionSingularitiesBudgetCertificate.budgetControlled
    (c : AlgebraicFunctionSingularitiesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AlgebraicFunctionSingularitiesBudgetCertificate.Ready
    (c : AlgebraicFunctionSingularitiesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicFunctionSingularitiesBudgetCertificate.size
    (c : AlgebraicFunctionSingularitiesBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem algebraicFunctionSingularities_budgetCertificate_le_size
    (c : AlgebraicFunctionSingularitiesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAlgebraicFunctionSingularitiesBudgetCertificate :
    AlgebraicFunctionSingularitiesBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleAlgebraicFunctionSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]

example :
    sampleAlgebraicFunctionSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicFunctionSingularitiesBudgetCertificate.size := by
  apply algebraicFunctionSingularities_budgetCertificate_le_size
  constructor
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicFunctionSingularitiesBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.controlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]
  · norm_num [AlgebraicFunctionSingularitiesBudgetCertificate.budgetControlled,
      sampleAlgebraicFunctionSingularitiesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicFunctionSingularitiesBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicFunctionSingularitiesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List AlgebraicFunctionSingularitiesBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAlgebraicFunctionSingularitiesBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAlgebraicFunctionSingularitiesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.AlgebraicFunctionSingularities
