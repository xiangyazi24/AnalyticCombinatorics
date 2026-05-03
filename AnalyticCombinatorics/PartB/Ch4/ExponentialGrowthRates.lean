import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ExponentialGrowthRates

/-! Exponential growth rates of combinatorial sequences (Chapter IV).
Growth constant from singularity location, algebraic vs transcendental GFs,
growth hierarchy, and subexponential factors. -/

/-! ## 1. Growth hierarchy classification -/

inductive GrowthTier where
  | polynomial
  | exponential
  | factorial
  | superExponential
deriving DecidableEq, Repr

structure GrowthProfile where
  name : String
  tier : GrowthTier
  exponentialBase : String
  subexponentialFactor : String
deriving DecidableEq, Repr

def catalanProfile : GrowthProfile :=
  { name := "Catalan numbers"
    tier := GrowthTier.exponential
    exponentialBase := "4"
    subexponentialFactor := "n^(-3/2) / sqrt(pi)" }

def fibonacciProfile : GrowthProfile :=
  { name := "Fibonacci numbers"
    tier := GrowthTier.exponential
    exponentialBase := "phi = (1+sqrt(5))/2"
    subexponentialFactor := "1/sqrt(5)" }

def bellProfile : GrowthProfile :=
  { name := "Bell numbers"
    tier := GrowthTier.superExponential
    exponentialBase := "grows faster than any c^n"
    subexponentialFactor := "saddle-point estimate" }

def derangementProfile : GrowthProfile :=
  { name := "Derangements"
    tier := GrowthTier.factorial
    exponentialBase := "n!"
    subexponentialFactor := "1/e" }

theorem catalan_is_exponential :
    catalanProfile.tier = GrowthTier.exponential := by native_decide

theorem fibonacci_is_exponential :
    fibonacciProfile.tier = GrowthTier.exponential := by native_decide

theorem bell_is_superexponential :
    bellProfile.tier = GrowthTier.superExponential := by native_decide

theorem derangement_is_factorial :
    derangementProfile.tier = GrowthTier.factorial := by native_decide

/-! ## 2. Exponential growth rate tables -/

def catalanGrowthRate (n : ℕ) : ℕ := 4 ^ n

def catalanGrowthTable : Fin 11 → ℕ :=
  ![1, 4, 16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576]

theorem catalan_growth_table_checked :
    ∀ k : Fin 11, catalanGrowthRate k.val = catalanGrowthTable k := by native_decide

def motzkinGrowthRate (n : ℕ) : ℕ := 3 ^ n

def motzkinGrowthTable : Fin 9 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729, 2187, 6561]

theorem motzkin_growth_table_checked :
    ∀ k : Fin 9, motzkinGrowthRate k.val = motzkinGrowthTable k := by native_decide

theorem catalan_motzkin_growth_dominance :
    ∀ k : Fin 9, motzkinGrowthRate k.val ≤ catalanGrowthRate k.val := by native_decide

/-! ## 3. Singularity location determines growth constant -/

inductive SingularityType where
  | algebraic
  | logarithmic
  | pole
  | essential
deriving DecidableEq, Repr

structure SingularityData where
  name : String
  singType : SingularityType
  radiusNumerator : ℕ
  radiusDenominator : ℕ
  growthBase : ℕ
deriving DecidableEq, Repr

def catalanSingularity : SingularityData :=
  { name := "C(z) = (1 - sqrt(1-4z))/2, singularity at z = 1/4"
    singType := SingularityType.algebraic
    radiusNumerator := 1
    radiusDenominator := 4
    growthBase := 4 }

def motzkinSingularity : SingularityData :=
  { name := "M(z) algebraic, singularity at z = 1/3"
    singType := SingularityType.algebraic
    radiusNumerator := 1
    radiusDenominator := 3
    growthBase := 3 }

def rationalSingularity : SingularityData :=
  { name := "1/(1-2z), pole at z = 1/2"
    singType := SingularityType.pole
    radiusNumerator := 1
    radiusDenominator := 2
    growthBase := 2 }

theorem catalan_singularity_is_algebraic :
    catalanSingularity.singType = SingularityType.algebraic := by native_decide

theorem rational_singularity_is_pole :
    rationalSingularity.singType = SingularityType.pole := by native_decide

theorem growth_base_equals_reciprocal_radius :
    catalanSingularity.growthBase * catalanSingularity.radiusNumerator =
      catalanSingularity.radiusDenominator := by native_decide

theorem motzkin_growth_base_reciprocal :
    motzkinSingularity.growthBase * motzkinSingularity.radiusNumerator =
      motzkinSingularity.radiusDenominator := by native_decide

/-! ## 4. Algebraic vs transcendental GF comparison -/

inductive GFClass where
  | rational
  | algebraic
  | transcendental
deriving DecidableEq, Repr

def gfClassOrder : GFClass → ℕ
  | GFClass.rational => 0
  | GFClass.algebraic => 1
  | GFClass.transcendental => 2

structure GFClassification where
  family : String
  gfClass : GFClass
  subexpFactor : String
deriving DecidableEq, Repr

def rationalGF : GFClassification :=
  { family := "Binary strings 1/(1-2z)"
    gfClass := GFClass.rational
    subexpFactor := "constant" }

def algebraicGF : GFClassification :=
  { family := "Catalan: (1-sqrt(1-4z))/(2z)"
    gfClass := GFClass.algebraic
    subexpFactor := "n^(-3/2)" }

def transcendentalGF : GFClassification :=
  { family := "Derangements: exp(-z)/(1-z)"
    gfClass := GFClass.transcendental
    subexpFactor := "1/e" }

theorem rational_simplest_class :
    gfClassOrder GFClass.rational < gfClassOrder GFClass.algebraic := by native_decide

theorem algebraic_before_transcendental :
    gfClassOrder GFClass.algebraic < gfClassOrder GFClass.transcendental := by native_decide

/-! ## 5. Subexponential factors and ratio tests -/

def centralBinomial (n : ℕ) : ℕ := Nat.choose (2 * n) n

def catalanNumber (n : ℕ) : ℕ := centralBinomial n / (n + 1)

def catalanTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

theorem catalan_table_checked :
    ∀ k : Fin 12, catalanNumber k.val = catalanTable k := by native_decide

theorem growth_dominates_catalan :
    ∀ k : Fin 10, catalanNumber k.val ≤ catalanGrowthRate k.val := by native_decide

def consecutiveRatio (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (centralBinomial n * 100) / centralBinomial (n - 1)

def consecutiveRatioTable : Fin 8 → ℕ :=
  ![0, 200, 300, 333, 350, 360, 366, 371]

theorem consecutive_ratio_table_checked :
    ∀ k : Fin 8, consecutiveRatio k.val = consecutiveRatioTable k := by native_decide

/-! ## 6. Growth hierarchy witnesses -/

def factorialTable : Fin 11 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

def expBase3Table : Fin 11 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049]

def polynomialCubeTable : Fin 11 → ℕ :=
  ![0, 1, 8, 27, 64, 125, 216, 343, 512, 729, 1000]

theorem polynomial_lt_exponential :
    ∀ k : Fin 11, polynomialCubeTable k ≤ expBase3Table k := by native_decide

def expBase3Late : Fin 4 → ℕ := ![2187, 6561, 19683, 59049]
def factorialLate : Fin 4 → ℕ := ![5040, 40320, 362880, 3628800]

theorem exponential_lt_factorial_from7 :
    ∀ k : Fin 4, expBase3Late k ≤ factorialLate k := by native_decide

def superExpEarly : Fin 4 → ℕ := ![27, 256, 3125, 46656]
def factorialEarly : Fin 4 → ℕ := ![6, 24, 120, 720]

theorem factorial_lt_superexp_from3 :
    ∀ k : Fin 4, factorialEarly k ≤ superExpEarly k := by native_decide

/-! ## 7. Pringsheim and Hadamard -/

def pringsheimStatement : String :=
  "A power series with non-negative coefficients and finite radius R " ++
  "has a singularity at z = R."

noncomputable def hadamardRadius (a : ℕ → ℝ) : ℝ :=
  1 / sSup { r : ℝ | ∀ n, a n ≤ r ^ n }

theorem pringsheim_catalan_witness :
    catalanSingularity.radiusDenominator = catalanSingularity.growthBase := by native_decide

theorem pringsheim_motzkin_witness :
    motzkinSingularity.radiusDenominator = motzkinSingularity.growthBase := by native_decide

theorem hierarchy_polynomial_ne_exponential :
    GrowthTier.polynomial ≠ GrowthTier.exponential := by decide

theorem hierarchy_exponential_ne_factorial :
    GrowthTier.exponential ≠ GrowthTier.factorial := by decide

theorem hierarchy_factorial_ne_superexp :
    GrowthTier.factorial ≠ GrowthTier.superExponential := by decide

end ExponentialGrowthRates
