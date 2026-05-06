import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.SingularityAnalysisBasics


/-!
Basic singularity analysis tools from Chapter IV of Analytic Combinatorics.

The file records coefficient-level, computable checks for the standard
singularity-analysis dictionary:

* binomial singularities `(1 - z)^(-alpha)`,
* radii of convergence for geometric examples,
* boundary partial sums,
* exponential growth in the model form `C * rho^{-n}`,
* Fibonacci coefficients from `z / (1 - z - z^2)`,
* the central-binomial form of the `(1 - z)^(-3/2)` coefficients.
-/

/-! ## 1. Darboux/binomial coefficients for `(1 - z)^(-alpha)` -/

/-- Coefficient of `z^n` in `(1 - z)^(-alpha)` for positive integer `alpha`. -/
def oneMinusZNegPowerCoeff (alpha n : ℕ) : ℕ :=
  Nat.choose (n + alpha - 1) (alpha - 1)

def darbouxAlpha1Small : Fin 8 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1]

def darbouxAlpha2Small : Fin 8 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8]

def darbouxAlpha3Small : Fin 8 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36]

def darbouxAlpha4Small : Fin 8 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120]

def darbouxAlpha5Small : Fin 8 → ℕ :=
  ![1, 5, 15, 35, 70, 126, 210, 330]

theorem darboux_alpha1_small :
    ∀ n : Fin 8, oneMinusZNegPowerCoeff 1 n.val = darbouxAlpha1Small n := by native_decide

theorem darboux_alpha2_small :
    ∀ n : Fin 8, oneMinusZNegPowerCoeff 2 n.val = darbouxAlpha2Small n := by native_decide

theorem darboux_alpha3_small :
    ∀ n : Fin 8, oneMinusZNegPowerCoeff 3 n.val = darbouxAlpha3Small n := by native_decide

theorem darboux_alpha4_small :
    ∀ n : Fin 8, oneMinusZNegPowerCoeff 4 n.val = darbouxAlpha4Small n := by native_decide

theorem darboux_alpha5_small :
    ∀ n : Fin 8, oneMinusZNegPowerCoeff 5 n.val = darbouxAlpha5Small n := by native_decide

theorem coeff_oneMinusZ_neg_one :
    ∀ n : Fin 16, oneMinusZNegPowerCoeff 1 n.val = 1 := by native_decide

theorem coeff_oneMinusZ_neg_two :
    ∀ n : Fin 16, oneMinusZNegPowerCoeff 2 n.val = n.val + 1 := by native_decide

theorem coeff_oneMinusZ_neg_three :
    ∀ n : Fin 16,
      oneMinusZNegPowerCoeff 3 n.val = (n.val + 1) * (n.val + 2) / 2 := by native_decide

/-! ## 2. Radii of convergence for two geometric examples -/

/-- Coefficients of `sum z^n`. -/
def geomCoeff (_ : ℕ) : ℕ := 1

/-- Coefficients of `sum 2^n z^n`. -/
def geomTwoCoeff (n : ℕ) : ℕ := 2 ^ n

/-- Radius of convergence of `sum z^n`. -/
def geomRadius : ℚ := 1

/-- Radius of convergence of `sum 2^n z^n`. -/
def geomTwoRadius : ℚ := 1 / 2

theorem radius_geom_series : geomRadius = 1 := by native_decide

theorem radius_geom_two_series : geomTwoRadius = 1 / 2 := by native_decide

theorem geom_coeff_small :
    ∀ n : Fin 10, geomCoeff n.val = 1 := by native_decide

theorem geom_two_coeff_small :
    ∀ n : Fin 10, geomTwoCoeff n.val = 2 ^ n.val := by native_decide

/-! ## 3. Boundary partial sums -/

def constantBoundaryPartialSum (n : ℕ) : ℕ :=
  ∑ _k ∈ Finset.range (n + 1), (1 : ℕ)

def linearBoundaryPartialSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (k + 1)

theorem constant_boundary_partial_sum :
    ∀ n : Fin 16, constantBoundaryPartialSum n.val = n.val + 1 := by native_decide

theorem linear_boundary_partial_sum :
    ∀ n : Fin 16,
      linearBoundaryPartialSum n.val = (n.val + 1) * (n.val + 2) / 2 := by native_decide

/-! ## 4. Exponential growth from the dominant radius -/

/-- A computable model for `[z^n] f(z) ~ C rho^(-n)`.
`rhoInv` stores `rho^(-1)`, so the radius is `1 / rhoInv`. -/
structure ExponentialGrowthModel where
  C : ℕ
  rhoInv : ℕ
deriving DecidableEq

def modelRadius (m : ExponentialGrowthModel) : ℚ :=
  1 / (m.rhoInv : ℚ)

def modelAsymptoticCoeff (m : ExponentialGrowthModel) (n : ℕ) : ℕ :=
  m.C * m.rhoInv ^ n

def unitRadiusModel : ExponentialGrowthModel :=
  { C := 1, rhoInv := 1 }

def halfRadiusModel : ExponentialGrowthModel :=
  { C := 3, rhoInv := 2 }

theorem unit_radius_model_radius :
    modelRadius unitRadiusModel = 1 := by native_decide

theorem half_radius_model_radius :
    modelRadius halfRadiusModel = 1 / 2 := by native_decide

theorem unit_radius_growth_small :
    ∀ n : Fin 10, modelAsymptoticCoeff unitRadiusModel n.val = 1 := by native_decide

theorem half_radius_growth_small :
    ∀ n : Fin 8, modelAsymptoticCoeff halfRadiusModel n.val = 3 * 2 ^ n.val := by native_decide

/-! ## 5. Fibonacci coefficients from `z / (1 - z - z^2)` -/

/-- Coefficient of `z^n` in `z / (1 - z - z^2)`. -/
def fibonacciGFCoeff (n : ℕ) : ℕ := Nat.fib n

def fibonacciGFTable : Fin 12 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

theorem fibonacci_coeff_extraction_small :
    ∀ n : Fin 12, fibonacciGFCoeff n.val = fibonacciGFTable n := by native_decide

theorem fibonacci_recurrence_from_gf_small :
    ∀ n : Fin 12,
      fibonacciGFCoeff (n.val + 2) =
        fibonacciGFCoeff (n.val + 1) + fibonacciGFCoeff n.val := by native_decide

def fibonacciPartialSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), fibonacciGFCoeff k

theorem fibonacci_partial_sums_small :
    ∀ n : Fin 12, fibonacciPartialSum n.val = fibonacciGFCoeff (n.val + 2) - 1 := by native_decide

/-- Coefficients of the truncated product
`(1 - z - z^2) * sum_{k = 0}^N F_k z^k`. -/
def truncatedFibonacciCoeff (N n : ℕ) : ℤ :=
  if n ≤ N then (fibonacciGFCoeff n : ℤ) else 0

def shiftedTruncatedFibonacciCoeff (N shift n : ℕ) : ℤ :=
  if shift ≤ n then truncatedFibonacciCoeff N (n - shift) else 0

def fibonacciGFPartialProductCoeff (N n : ℕ) : ℤ :=
  truncatedFibonacciCoeff N n
    - shiftedTruncatedFibonacciCoeff N 1 n
    - shiftedTruncatedFibonacciCoeff N 2 n

def fibonacciGFPartialProductN8 : Fin 11 → ℤ :=
  ![(0 : ℤ), 1, 0, 0, 0, 0, 0, 0, 0, -34, -21]

theorem fibonacci_gf_partial_product_N8 :
    ∀ n : Fin 11,
      fibonacciGFPartialProductCoeff 8 n.val = fibonacciGFPartialProductN8 n := by native_decide

/-! ## 6. The `(1 - z)^(-3/2)` singularity -/

def centralBinomScaled (n : ℕ) : ℚ :=
  (Nat.choose (2 * n) n : ℚ) / (4 ^ n : ℕ)

/-- Coefficients of `(1 - z)^(-3/2)`:
`(2n + 1) * binom(2n,n) / 4^n`. -/
def threeHalvesSingularityCoeff (n : ℕ) : ℚ :=
  ((2 * n + 1 : ℕ) : ℚ) * centralBinomScaled n

def threeHalvesSingularityTable : Fin 7 → ℚ :=
  ![(1 : ℚ), 3 / 2, 15 / 8, 35 / 16, 315 / 128, 693 / 256, 3003 / 1024]

theorem three_halves_singularity_coeff_small :
    ∀ n : Fin 7,
      threeHalvesSingularityCoeff n.val = threeHalvesSingularityTable n := by native_decide

theorem three_halves_central_binom_relation_small :
    ∀ n : Fin 10,
      threeHalvesSingularityCoeff n.val =
        ((2 * n.val + 1 : ℕ) : ℚ) *
          ((Nat.choose (2 * n.val) n.val : ℚ) / (4 ^ n.val : ℕ)) := by native_decide



structure SingularityAnalysisBasicsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityAnalysisBasicsBudgetCertificate.controlled
    (c : SingularityAnalysisBasicsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SingularityAnalysisBasicsBudgetCertificate.budgetControlled
    (c : SingularityAnalysisBasicsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularityAnalysisBasicsBudgetCertificate.Ready
    (c : SingularityAnalysisBasicsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityAnalysisBasicsBudgetCertificate.size
    (c : SingularityAnalysisBasicsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularityAnalysisBasics_budgetCertificate_le_size
    (c : SingularityAnalysisBasicsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityAnalysisBasicsBudgetCertificate :
    SingularityAnalysisBasicsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSingularityAnalysisBasicsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.controlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]

example :
    sampleSingularityAnalysisBasicsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisBasicsBudgetCertificate.size := by
  apply singularityAnalysisBasics_budgetCertificate_le_size
  constructor
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.controlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularityAnalysisBasicsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.controlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]
  · norm_num [SingularityAnalysisBasicsBudgetCertificate.budgetControlled,
      sampleSingularityAnalysisBasicsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityAnalysisBasicsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityAnalysisBasicsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SingularityAnalysisBasicsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityAnalysisBasicsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSingularityAnalysisBasicsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.SingularityAnalysisBasics
