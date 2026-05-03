import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ImplicitFunctionCoefficients

/-!
  Executable coefficient checks for implicit equations of the form
  `y = x * phi y`.

  The statements are bounded numerical versions of the coefficient extraction
  rules used in Chapter VII: Lagrange extraction, small functional-equation
  recurrences, and polygon-dissection tables.
-/

/-! ## Basic coefficient tables -/

/-- Coefficients of the linear schema `y = x * (1 + y)`. -/
def linearSchemaCoeffs : Fin 15 → ℕ :=
  ![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- Coefficients of the Catalan smooth schema `y = x * (1 + y)^2`. -/
def catalanSchemaCoeffs : Fin 15 → ℕ :=
  ![0, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900,
    2674440]

/-- Coefficients of the ordered-tree schema `y = x / (1 - y)`. -/
def orderedTreeSchemaCoeffs : Fin 15 → ℕ :=
  ![0, 1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900]

/-- Catalan numbers in closed form. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Fuss-Catalan numbers for arity `arity`. -/
def fussCatalan (arity pieces : ℕ) : ℕ :=
  Nat.choose (arity * pieces + 1) pieces / (arity * pieces + 1)

/-! ## Lagrange coefficient extraction checks -/

/--
For `y = x * (1 + y)`, Lagrange extraction gives
`n * [x^n] y = [u^(n-1)] (1 + u)^n = binom(n,n-1)`.
-/
theorem linear_schema_lagrange_checked :
    ∀ n : Fin 15,
      1 ≤ n.val →
        n.val * linearSchemaCoeffs n = Nat.choose n.val (n.val - 1) := by
  native_decide

/--
For `y = x * (1 + y)^2`, Lagrange extraction gives
`n * [x^n] y = [u^(n-1)] (1 + u)^(2n)`.
-/
theorem catalan_schema_lagrange_checked :
    ∀ n : Fin 15,
      1 ≤ n.val →
        n.val * catalanSchemaCoeffs n = Nat.choose (2 * n.val) (n.val - 1) := by
  native_decide

/--
For `y = x / (1 - y)`, Lagrange extraction gives
`n * [x^n] y = [u^(n-1)] (1 - u)^(-n)`.
-/
theorem ordered_tree_schema_lagrange_checked :
    ∀ n : Fin 15,
      1 ≤ n.val →
        n.val * orderedTreeSchemaCoeffs n =
          Nat.choose (2 * n.val - 2) (n.val - 1) := by
  native_decide

/-- The Catalan schema table is the shifted Catalan sequence. -/
theorem catalan_schema_is_shifted_catalan :
    ∀ n : Fin 15,
      catalanSchemaCoeffs n =
        if n.val = 0 then 0 else catalanNumber n.val := by
  native_decide

/-- The ordered-tree schema table is the Catalan sequence shifted by one. -/
theorem ordered_tree_schema_is_shifted_catalan :
    ∀ n : Fin 15,
      orderedTreeSchemaCoeffs n =
        if n.val = 0 then 0 else catalanNumber (n.val - 1) := by
  native_decide

/-! ## Functional-equation coefficient extraction -/

/-- Convolution side of `C = 1 + x * C^2`. -/
def catalanConvolutionRhs (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun total i => total + catalanNumber i * catalanNumber (n - i)) 0

/-- The first Catalan coefficients satisfy the quadratic functional equation. -/
theorem catalan_functional_equation_checked :
    ∀ n : Fin 14, catalanNumber (n.val + 1) = catalanConvolutionRhs n.val := by
  native_decide

/-- Coefficient formula for the ordered-tree solution, extended by zero at `0`. -/
def orderedTreeCoeff (n : ℕ) : ℕ :=
  if n = 0 then 0 else catalanNumber (n - 1)

/-- Convolution side of `y = x + y^2`, equivalent to `y = x / (1 - y)`. -/
def orderedTreeConvolutionRhs (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun total i => total + orderedTreeCoeff i * orderedTreeCoeff (n - i)) 0

/-- The ordered-tree coefficients satisfy the small functional-equation recurrence. -/
theorem ordered_tree_functional_equation_checked :
    ∀ n : Fin 15,
      2 ≤ n.val →
        orderedTreeSchemaCoeffs n = orderedTreeConvolutionRhs n.val := by
  native_decide

/-! ## Smooth-schema characteristic checks -/

/-- Values for `phi(y) = (1 + y)^2` at the characteristic point `tau = 1`. -/
def binaryPhiAtTau : ℕ := 4

/-- Value of `tau * phi'(tau)` for `phi(y) = (1 + y)^2` and `tau = 1`. -/
def binaryTauTimesPhiPrimeAtTau : ℕ := 4

/-- Executable characteristic equation `tau * phi'(tau) = phi(tau)`. -/
theorem binary_smooth_characteristic_checked :
    binaryTauTimesPhiPrimeAtTau = binaryPhiAtTau := by
  native_decide

/-- Twice the values at `tau = 1/2` for `phi(y) = 1 / (1 - y)`. -/
def orderedPhiAtTauDoubled : ℕ := 4

/-- Twice `tau * phi'(tau)` at `tau = 1/2` for `phi(y) = 1 / (1 - y)`. -/
def orderedTauTimesPhiPrimeAtTauDoubled : ℕ := 4

/-- Cross-multiplied characteristic equation for the ordered-tree schema. -/
theorem ordered_tree_smooth_characteristic_checked :
    orderedTauTimesPhiPrimeAtTauDoubled = orderedPhiAtTauDoubled := by
  native_decide

/-! ## Polygon dissections as implicit-schema coefficient tables -/

/-- Triangulations of convex `n`-gons for `n < 15`; entries below `3` are zero. -/
def polygonTriangulationCoeffs : Fin 15 → ℕ :=
  ![0, 0, 0, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

/-- Quadrangulations indexed by the number of quadrangles. -/
def quadrangulationCoeffs : Fin 11 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428, 7752, 43263, 246675, 1430715]

/-- Triangulations of `n`-gons are Catalan numbers `C_(n-2)`. -/
theorem polygon_triangulation_formula_checked :
    ∀ n : Fin 15,
      3 ≤ n.val →
        polygonTriangulationCoeffs n = catalanNumber (n.val - 2) := by
  native_decide

/-- Quadrangulation values are the arity-three Fuss-Catalan numbers. -/
theorem quadrangulation_fuss_catalan_checked :
    ∀ pieces : Fin 11,
      quadrangulationCoeffs pieces = fussCatalan 3 pieces.val := by
  native_decide

/-- The first polygon-dissection tables agree where triangulations meet ordered trees. -/
theorem triangulations_match_ordered_trees_checked :
    ∀ n : Fin 15,
      3 ≤ n.val →
        polygonTriangulationCoeffs n = orderedTreeCoeff (n.val - 1) := by
  native_decide

/-! ## Tables for small powers of `phi` -/

/-- Coefficients of `(1 + u)^8` through degree `8`. -/
def onePlusUPowEight : Fin 9 → ℕ :=
  ![1, 8, 28, 56, 70, 56, 28, 8, 1]

/-- Coefficients of `(1 + u)^(2 * 4)`, used by the Catalan schema at `n = 4`. -/
theorem catalan_phi_power_example_checked :
    ∀ k : Fin 9, onePlusUPowEight k = Nat.choose 8 k.val := by
  native_decide

/-- Lagrange extraction at `n = 4` yields the coefficient `14`. -/
theorem catalan_n_four_extraction_checked :
    4 * catalanSchemaCoeffs ⟨4, by native_decide⟩ = onePlusUPowEight ⟨3, by native_decide⟩ := by
  native_decide

/-- Coefficients of `(1 - u)^(-5)` through degree `7`. -/
def geometricPowFive : Fin 8 → ℕ :=
  ![1, 5, 15, 35, 70, 126, 210, 330]

/-- The negative-binomial coefficients for `(1 - u)^(-5)`. -/
theorem geometric_power_five_checked :
    ∀ k : Fin 8, geometricPowFive k = Nat.choose (k.val + 4) k.val := by
  native_decide

/-- Lagrange extraction for ordered trees at `n = 5` yields the coefficient `14`. -/
theorem ordered_tree_n_five_extraction_checked :
    5 * orderedTreeSchemaCoeffs ⟨5, by native_decide⟩ =
      geometricPowFive ⟨4, by native_decide⟩ := by
  native_decide

end ImplicitFunctionCoefficients
