import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace UniversalityExponents

/-!
  Chapter VII finite checks: universality of critical exponents.

  Combinatorial families whose generating functions satisfy algebraic
  equations of the same structural type share identical critical
  exponents.  The *tree universality class* (square-root singularities
  from quadratic functional equations) yields coefficient growth
  `~ C · ρ⁻ⁿ · n⁻³ᐟ²`.  The *map universality class* (from
  cubic-type equations on surfaces) yields `~ C · ρ⁻ⁿ · n⁻⁵ᐟ²`.
  These universal exponents parallel critical exponents in statistical
  physics, where scaling relations constrain the exponent values.

  Reference: Flajolet & Sedgewick, *Analytic Combinatorics* (2009), §VII.
-/

-- ============================================================
/-! ## 1. Universality class exponent tables -/
-- ============================================================

/-- Coefficient decay exponent numerator (denominator always 2):
  0 = tree-like (3/2), 1 = map-like (5/2), 2 = higher algebraic (7/2). -/
def coeffExpNum : Fin 3 → ℕ := ![3, 5, 7]

/-- Singular exponent numerator (denominator 2):
  tree: 1/2, map: 3/2, higher: 5/2. -/
def singExpNum : Fin 3 → ℕ := ![1, 3, 5]

theorem singExp_plus_two_eq_coeffExp :
    ∀ i : Fin 3, coeffExpNum i = singExpNum i + 2 := by
  native_decide

theorem tree_coeffExp : coeffExpNum 0 = 3 := by native_decide
theorem map_coeffExp : coeffExpNum 1 = 5 := by native_decide
theorem higher_coeffExp : coeffExpNum 2 = 7 := by native_decide

theorem exponent_strict_ordering :
    coeffExpNum 0 < coeffExpNum 1 ∧ coeffExpNum 1 < coeffExpNum 2 := by
  native_decide

theorem coeffExp_all_odd :
    ∀ i : Fin 3, coeffExpNum i % 2 = 1 := by native_decide

-- ============================================================
/-! ## 2. Vanishing order determines exponent -/
-- ============================================================

/-- Vanishing order of the y-partial derivative at the dominant
  singularity in the defining equation P(z,y) = 0. -/
def vanishingOrder : Fin 3 → ℕ := ![1, 2, 3]

theorem singExp_from_vanishing :
    ∀ i : Fin 3, singExpNum i = 2 * vanishingOrder i - 1 := by
  native_decide

theorem coeffExp_from_vanishing :
    ∀ i : Fin 3, coeffExpNum i = 2 * vanishingOrder i + 1 := by
  native_decide

-- ============================================================
/-! ## 3. Tree universality class (α = 3/2) -/
-- ============================================================

def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

def catalanTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

theorem catalan_matches :
    ∀ n : Fin 12, catalan n.val = catalanTable n := by native_decide

def motzkinTable : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798]

def schroederTable : Fin 10 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586, 206098]

def ternaryTree (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

def ternaryTreeTable : Fin 10 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428, 7752, 43263, 246675]

theorem ternaryTree_matches :
    ∀ n : Fin 10, ternaryTree n.val = ternaryTreeTable n := by native_decide

/-- Catalan recurrence: C(n+1)·(n+2) = C(n)·2·(2n+1). -/
theorem catalan_recurrence_spot :
    catalanTable 1 * (0 + 2) = catalanTable 0 * 2 * (2 * 0 + 1) ∧
    catalanTable 2 * (1 + 2) = catalanTable 1 * 2 * (2 * 1 + 1) ∧
    catalanTable 3 * (2 + 2) = catalanTable 2 * 2 * (2 * 2 + 1) ∧
    catalanTable 4 * (3 + 2) = catalanTable 3 * 2 * (2 * 3 + 1) ∧
    catalanTable 5 * (4 + 2) = catalanTable 4 * 2 * (2 * 4 + 1) := by
  native_decide

theorem catalan_le_four_pow :
    ∀ n : Fin 12, catalanTable n ≤ 4 ^ n.val := by native_decide

theorem motzkin_le_three_pow :
    ∀ n : Fin 12, motzkinTable n ≤ 3 ^ n.val := by native_decide

theorem schroeder_le_six_pow :
    ∀ n : Fin 10, schroederTable n ≤ 6 ^ n.val := by native_decide

theorem ternaryTree_le_seven_pow :
    ∀ n : Fin 10, ternaryTreeTable n ≤ 7 ^ n.val := by native_decide

/-- Motzkin numbers are dominated by Catalan numbers. -/
theorem motzkin_le_catalan :
    ∀ n : Fin 12, motzkinTable n ≤ catalanTable n := by native_decide

example : catalan 5 = 42 := by native_decide
example : catalan 10 = 16796 := by native_decide
example : motzkinTable 6 = 51 := by native_decide

-- ============================================================
/-! ## 4. Map universality class (α = 5/2) -/
-- ============================================================

def rootedMapCount (n : ℕ) : ℕ :=
  2 * Nat.factorial (2 * n) * 3 ^ n /
    (Nat.factorial n * Nat.factorial (n + 2))

def rootedMapTable : Fin 10 → ℕ :=
  ![1, 2, 9, 54, 378, 2916, 24057, 208494, 1876446, 17399772]

theorem rootedMap_matches :
    ∀ n : Fin 10, rootedMapCount n.val = rootedMapTable n := by native_decide

/-- Map recurrence: m(n+1)·(n+3) = m(n)·6·(2n+1). -/
theorem map_recurrence_spot :
    rootedMapTable 1 * (0 + 3) = rootedMapTable 0 * 6 * (2 * 0 + 1) ∧
    rootedMapTable 2 * (1 + 3) = rootedMapTable 1 * 6 * (2 * 1 + 1) ∧
    rootedMapTable 3 * (2 + 3) = rootedMapTable 2 * 6 * (2 * 2 + 1) ∧
    rootedMapTable 4 * (3 + 3) = rootedMapTable 3 * 6 * (2 * 3 + 1) ∧
    rootedMapTable 5 * (4 + 3) = rootedMapTable 4 * 6 * (2 * 4 + 1) := by
  native_decide

theorem rootedMap_le_twelve_pow :
    ∀ n : Fin 10, rootedMapTable n ≤ 12 ^ n.val := by native_decide

example : rootedMapCount 3 = 54 := by native_decide
example : rootedMapCount 5 = 2916 := by native_decide

-- ============================================================
/-! ## 5. Cross-class comparison -/
-- ============================================================

theorem maps_dominate_catalan :
    ∀ n : Fin 10, catalan n.val ≤ rootedMapCount n.val := by native_decide

/-- The map-to-tree ratio is strictly increasing. -/
theorem map_catalan_ratio_grows :
    rootedMapCount 1 * catalan 0 > rootedMapCount 0 * catalan 1 ∧
    rootedMapCount 2 * catalan 1 > rootedMapCount 1 * catalan 2 ∧
    rootedMapCount 3 * catalan 2 > rootedMapCount 2 * catalan 3 ∧
    rootedMapCount 4 * catalan 3 > rootedMapCount 3 * catalan 4 ∧
    rootedMapCount 5 * catalan 4 > rootedMapCount 4 * catalan 5 := by
  native_decide

-- ============================================================
/-! ## 6. Statistical physics scaling relations -/
-- ============================================================

/-- 2D Ising model critical exponents [α, β, γ, δ, ν, η]
  scaled to a common denominator of 8. -/
def ising2D_x8 : Fin 6 → ℕ := ![0, 1, 14, 120, 8, 2]

/-- Mean-field critical exponents scaled to denominator 2. -/
def meanField_x2 : Fin 6 → ℕ := ![0, 1, 2, 6, 1, 0]

/-- Rushbrooke: α + 2β + γ = 2 (2D Ising, ×8). -/
theorem ising_rushbrooke :
    ising2D_x8 0 + 2 * ising2D_x8 1 + ising2D_x8 2 = 2 * 8 := by
  native_decide

/-- Widom: γ = β(δ−1) (2D Ising, ×8). -/
theorem ising_widom :
    ising2D_x8 2 * 8 = ising2D_x8 1 * (ising2D_x8 3 - 8) := by
  native_decide

/-- Fisher: γ = (2−η)ν (2D Ising, ×8). -/
theorem ising_fisher :
    ising2D_x8 2 * 8 = (2 * 8 - ising2D_x8 5) * ising2D_x8 4 := by
  native_decide

/-- Josephson hyperscaling d = 2: dν = 2 − α (2D Ising, ×8). -/
theorem ising_josephson :
    2 * ising2D_x8 4 = 2 * 8 - ising2D_x8 0 := by native_decide

theorem meanfield_rushbrooke :
    meanField_x2 0 + 2 * meanField_x2 1 + meanField_x2 2 = 2 * 2 := by
  native_decide

theorem meanfield_widom :
    meanField_x2 2 * 2 = meanField_x2 1 * (meanField_x2 3 - 2) := by
  native_decide

/-- Josephson at upper critical dimension d = 4 (mean-field, ×2). -/
theorem meanfield_josephson_d4 :
    4 * meanField_x2 4 = 2 * 2 - meanField_x2 0 := by native_decide

-- ============================================================
/-! ## 7. Analytic universality (noncomputable) -/
-- ============================================================

noncomputable def treeExponent : ℝ := 3 / 2
noncomputable def mapExponent : ℝ := 5 / 2
noncomputable def higherExponent : ℝ := 7 / 2

theorem exponent_gap_map_tree : mapExponent - treeExponent = 1 := by sorry
theorem exponent_gap_higher_map : higherExponent - mapExponent = 1 := by sorry
theorem map_gt_tree : mapExponent > treeExponent := by sorry
theorem higher_gt_map : higherExponent > mapExponent := by sorry

/-- Each algebraic universality class raises the exponent by exactly 1. -/
theorem universal_exponent_step :
    mapExponent - treeExponent = higherExponent - mapExponent := by sorry

end UniversalityExponents
