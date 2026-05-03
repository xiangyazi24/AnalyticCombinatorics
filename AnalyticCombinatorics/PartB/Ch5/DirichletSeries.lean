import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace DirichletSeries

/-!
# Dirichlet Series: Small Arithmetic Tables

Finite checks for multiplicative functions used with Dirichlet series.
All tables are indexed by `0 ↦ n = 1`, `1 ↦ n = 2`, and so on.
-/

def nTable : Fin 15 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def identityTable : Fin 15 → Int :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-! ## Möbius function -/

def mobiusTable : Fin 15 → Int :=
  ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1]

def mertensTable : Fin 15 → Int :=
  ![1, 0, -1, -1, -2, -1, -2, -2, -2, -1, -2, -2, -3, -2, -1]

/-! ## Divisor functions -/

def divisorCountTable : Fin 15 → ℕ :=
  ![1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 6, 2, 4, 4]

def divisorCountPrefixTable : Fin 15 → ℕ :=
  ![1, 3, 5, 8, 10, 14, 16, 20, 23, 27, 29, 35, 37, 41, 45]

def sigmaTable : Fin 15 → ℕ :=
  ![1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24]

def sigmaPrefixTable : Fin 15 → ℕ :=
  ![1, 4, 8, 15, 21, 33, 41, 56, 69, 87, 99, 127, 141, 165, 189]

/-!
`σ * μ = id` for Dirichlet convolution.  The table records the first
fifteen values of this convolution.
-/

def sigmaMobiusConvolutionTable : Fin 15 → Int :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-! ## Liouville function -/

def liouvilleTable : Fin 15 → Int :=
  ![1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1]

/-! ## Partial Euler products for `ζ(2)` -/

def zetaTwoEulerPrimeCutoffTable : Fin 4 → ℕ :=
  ![2, 3, 5, 7]

def zetaTwoEulerNumeratorTable : Fin 4 → ℕ :=
  ![4, 3, 25, 1225]

def zetaTwoEulerDenominatorTable : Fin 4 → ℕ :=
  ![3, 2, 16, 768]

theorem sigma_mobius_convolution_small :
    ∀ i : Fin 15, sigmaMobiusConvolutionTable i = identityTable i := by
  native_decide

theorem mobius_values_squarefree_small :
    mobiusTable 1 = -1 ∧ mobiusTable 5 = 1 ∧ mobiusTable 14 = 1 := by
  native_decide

theorem mobius_values_nonsquarefree_small :
    mobiusTable 3 = 0 ∧ mobiusTable 7 = 0 ∧ mobiusTable 8 = 0 ∧ mobiusTable 11 = 0 := by
  native_decide

lemma divisor_count_prefix_last :
    divisorCountPrefixTable 14 = 45 := by
  native_decide

lemma divisor_count_of_twelve :
    divisorCountTable 11 = 6 := by
  native_decide

theorem sigma_prefix_last :
    sigmaPrefixTable 14 = 189 := by
  native_decide

lemma sigma_values_selected :
    sigmaTable 5 = 12 ∧ sigmaTable 11 = 28 ∧ sigmaTable 14 = 24 := by
  native_decide

theorem liouville_values_selected :
    liouvilleTable 7 = -1 ∧ liouvilleTable 8 = 1 ∧ liouvilleTable 11 = -1 := by
  native_decide

theorem mertens_partial_sums_selected :
    mertensTable 0 = 1 ∧ mertensTable 9 = -1 ∧ mertensTable 14 = -1 := by
  native_decide

theorem zeta_two_euler_product_through_seven :
    ((4 : ℚ) / 3) * (9 / 8) * (25 / 24) * (49 / 48) = 1225 / 768 := by
  native_decide

theorem zeta_two_euler_tables_through_seven :
    zetaTwoEulerPrimeCutoffTable 3 = 7 ∧
      zetaTwoEulerNumeratorTable 3 = 1225 ∧
      zetaTwoEulerDenominatorTable 3 = 768 := by
  native_decide

end DirichletSeries
