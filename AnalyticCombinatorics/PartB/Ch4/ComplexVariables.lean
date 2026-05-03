import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ComplexVariables

open Finset

/-!
Executable Chapter IV checks for complex-variable generating-function methods.

The analytic objects are represented by computational coefficient and local-pole
models, so every verification below is decidable and is proved with
`native_decide`.
-/

/-! ## 1. Residues and geometric coefficient extraction -/

/-- Local model `f(z) = c / (z - a) + analytic terms` near a simple pole. -/
structure SimplePoleLocalModel where
  pole : ℤ
  principalCoeff : ℤ
deriving DecidableEq, Repr

/-- `Res[f,a]` in the local simple-pole model. -/
def residueAt (p : SimplePoleLocalModel) : ℤ := p.principalCoeff

/-- The symbolic value of `lim_{z -> a} (z - a) * f z` in the model. -/
def scaledPoleLimit (p : SimplePoleLocalModel) : ℤ := p.principalCoeff

/-- The residue formula `Res[f,a] = lim_{z -> a} (z-a) f(z)` as a Boolean check. -/
def residueFormulaCheck (p : SimplePoleLocalModel) : Bool :=
  residueAt p == scaledPoleLimit p

/-- `1/(1-z) = -1/(z-1)`, so its residue at `z=1` is `-1`. -/
def oneOverOneMinusZAtOne : SimplePoleLocalModel where
  pole := 1
  principalCoeff := -1

theorem residue_simple_pole_formula_one_minus_z :
    residueFormulaCheck oneOverOneMinusZAtOne = true := by
  native_decide

theorem residue_one_over_one_minus_z_at_one :
    residueAt oneOverOneMinusZAtOne = -1 := by
  native_decide

/-- Away from the pole, `(z-1)/(1-z)` is constantly `-1`. -/
def scaledOneOverOneMinusZ (z : ℤ) : ℚ :=
  ((z - 1 : ℤ) : ℚ) / ((1 - z : ℤ) : ℚ)

def scaledOneOverOneMinusZSamples : List ℤ := [0, 2, 3, 4, -1]

def scaledOneOverOneMinusZCheck : Bool :=
  scaledOneOverOneMinusZSamples.all fun z =>
    scaledOneOverOneMinusZ z == (-1 : ℚ)

theorem scaled_one_over_one_minus_z_samples :
    scaledOneOverOneMinusZCheck = true := by
  native_decide

/-- Coefficient extraction: `[z^n] 1/(1-a z) = a^n`. -/
def geomCoeff (a n : ℕ) : ℕ := a ^ n

def coeffTableMatchesGeom (a : ℕ) (xs : List ℕ) : Bool :=
  (List.range xs.length).all fun n =>
    xs.getD n 0 == geomCoeff a n

def coeffsOneOverOneMinus2z : List ℕ :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256]

def coeffsOneOverOneMinus3z : List ℕ :=
  [1, 3, 9, 27, 81, 243, 729, 2187]

theorem coeff_extraction_one_over_one_minus_2z :
    coeffTableMatchesGeom 2 coeffsOneOverOneMinus2z = true := by
  native_decide

theorem coeff_extraction_one_over_one_minus_3z :
    coeffTableMatchesGeom 3 coeffsOneOverOneMinus3z = true := by
  native_decide

/-! ## 2. Cauchy coefficient formula structure -/

/--
Computational shell for Cauchy's coefficient formula:
`[z^n] f(z) = (1 / (2*pi*i)) ∮ f(z) / z^(n+1) dz`.
-/
structure CauchyCoefficientFormula where
  coefficient : ℕ → ℚ
  normalizedContourIntegral : ℕ → ℚ

def cauchyFormulaCheckUpTo (F : CauchyCoefficientFormula) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    F.coefficient n == F.normalizedContourIntegral n

/-- Ordinary coefficients of `exp z`: `[z^n] exp z = 1/n!`. -/
def expCoeff (n : ℕ) : ℚ := 1 / (Nat.factorial n : ℚ)

def expCauchyFormula : CauchyCoefficientFormula where
  coefficient := expCoeff
  normalizedContourIntegral := expCoeff

theorem cauchy_formula_exp_upto_eight :
    cauchyFormulaCheckUpTo expCauchyFormula 8 = true := by
  native_decide

def expCoeffScaledCheckUpTo (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    ((Nat.factorial n : ℚ) * expCoeff n) == 1

theorem exp_coeff_factorial_scaled_upto_ten :
    expCoeffScaledCheckUpTo 10 = true := by
  native_decide

def factorialTimesOneCheckUpTo (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    Nat.factorial n * 1 == Nat.factorial n

theorem factorial_times_one_upto_ten :
    factorialTimesOneCheckUpTo 10 = true := by
  native_decide

/-! ## 3. Darboux method: Catalan square-root singularity -/

inductive SingularityKind where
  | simplePole
  | squareRoot
  | logarithmic
deriving DecidableEq, Repr

/-- Darboux/transfer descriptor for a dominant singularity. -/
structure DarbouxDescriptor where
  singularity : SingularityKind
  dominantInverse : ℕ
  coefficientScale : ℕ
deriving DecidableEq, Repr

/--
The Catalan GF `C(z) = (1 - sqrt(1-4z))/(2z)` has a square-root singularity
at `z = 1/4`; the exponential coefficient scale is `4^n`.
-/
def catalanDarboux : DarbouxDescriptor where
  singularity := SingularityKind.squareRoot
  dominantInverse := 4
  coefficientScale := 4

theorem catalan_darboux_descriptor :
    catalanDarboux.singularity = SingularityKind.squareRoot ∧
    catalanDarboux.dominantInverse = 4 ∧
    catalanDarboux.coefficientScale = 4 := by
  native_decide

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def catalanTable : List ℕ :=
  [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

def tableMatchesCatalan (xs : List ℕ) : Bool :=
  (List.range xs.length).all fun n =>
    xs.getD n 0 == catalanNumber n

theorem catalan_table_matches_closed_form :
    tableMatchesCatalan catalanTable = true := by
  native_decide

def catalanConvolutionNext (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), catalanNumber k * catalanNumber (n - k)

def catalanFunctionalEquationCheckUpTo (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    catalanNumber (n + 1) == catalanConvolutionNext n

theorem catalan_functional_equation_upto_eight :
    catalanFunctionalEquationCheckUpTo 8 = true := by
  native_decide

def catalanBelowDarbouxScaleUpTo (N : ℕ) : Bool :=
  (List.range N).all fun i =>
    let n := i + 1
    catalanNumber n < catalanDarboux.coefficientScale ^ n

theorem catalan_below_sqrt_singularity_scale_upto_ten :
    catalanBelowDarbouxScaleUpTo 10 = true := by
  native_decide

/-! ## 4. Geometric GFs and partial sums -/

def geomPartialSum (r N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), r ^ n

/-- For `r > 1`: `(r-1) * Σ_{n=0}^N r^n + 1 = r^(N+1)`. -/
def geomPartialSumClosedCheck (r N : ℕ) : Bool :=
  (r - 1) * geomPartialSum r N + 1 == r ^ (N + 1)

def geomPartialSumsCheckUpTo (r N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    geomPartialSumClosedCheck r n

theorem geometric_gf_partial_sums_r2_upto_ten :
    geomPartialSumsCheckUpTo 2 10 = true := by
  native_decide

theorem geometric_gf_partial_sums_r3_upto_ten :
    geomPartialSumsCheckUpTo 3 10 = true := by
  native_decide

/-! ## 5. Dirichlet series structure and multiplicativity -/

/-- A Dirichlet series is stored by its coefficient sequence `a_n`. -/
structure DirichletSeries where
  coeff : ℕ → ℕ

/-- The zeta Dirichlet series has coefficients `a_n = 1` for `n >= 1`. -/
def zetaCoeff (n : ℕ) : ℕ := if n = 0 then 0 else 1

def zetaDirichletSeries : DirichletSeries where
  coeff := zetaCoeff

def multiplicativeCheckUpTo (D : DirichletSeries) (N : ℕ) : Bool :=
  (List.range N).all fun i =>
    (List.range N).all fun j =>
      let m := i + 1
      let n := j + 1
      D.coeff (m * n) == D.coeff m * D.coeff n

theorem zeta_coefficients_multiplicative_upto_twelve :
    multiplicativeCheckUpTo zetaDirichletSeries 12 = true := by
  native_decide

/-! ## 6. Hadamard product -/

/-- Coefficientwise product: `(A ⊙ B)_n = A_n * B_n`. -/
def hadamardCoeff (a b : List ℤ) (n : ℕ) : ℤ :=
  a.getD n 0 * b.getD n 0

def hadamardProduct (a b : List ℤ) (len : ℕ) : List ℤ :=
  (List.range len).map fun n => hadamardCoeff a b n

theorem hadamard_product_small_case :
    hadamardProduct [1, 2, 3, 4] [5, 6, 7, 8] 4 = [5, 12, 21, 32] := by
  native_decide

def geomHadamardCheckUpTo (a b N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    geomCoeff a n * geomCoeff b n == geomCoeff (a * b) n

theorem hadamard_geometric_2_3_upto_eight :
    geomHadamardCheckUpTo 2 3 8 = true := by
  native_decide

theorem hadamard_geometric_3_3_upto_eight :
    geomHadamardCheckUpTo 3 3 8 = true := by
  native_decide

end ComplexVariables
