import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.GeneratingFunctionAnalyticity


/-!
# Analytic properties of generating functions

Small computable checks from Chapter V of analytic combinatorics:
central binomial coefficients, convolution/product/composition of ordinary
generating functions, Catalan coefficients, and elementary growth comparisons.
-/

/-- Central binomial coefficient `C(2n,n)`. -/
def centralBinom (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

/-- The first ten central binomial coefficients `C(2n,n)`, `n = 0..9`. -/
def centralBinomTable : Fin 10 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620]

theorem centralBinom_table_correct :
    ∀ n : Fin 10, centralBinomTable n = centralBinom n := by native_decide

/-- Recurrence checked as an integer division identity. -/
theorem centralBinom_recurrence_division :
    ∀ n : Fin 12,
      centralBinom ((n : ℕ) + 1) =
        (centralBinom n * (2 * (2 * (n : ℕ) + 1))) / ((n : ℕ) + 1) := by
  native_decide

/-- The same recurrence checked without division by cross-multiplication. -/
theorem centralBinom_recurrence_integer :
    ∀ n : Fin 12,
      centralBinom ((n : ℕ) + 1) * ((n : ℕ) + 1) =
        centralBinom n * (2 * (2 * (n : ℕ) + 1)) := by
  native_decide

/-- Convolution coefficient of two all-one sequences. -/
def onesConvolutionCoeff (n : ℕ) : ℕ :=
  ∑ _ : Fin (n + 1), (1 : ℕ)

/-- The product `1/(1-z) * 1/(1-z)` has coefficients `1,2,3,...`. -/
def onesConvolutionTable : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem ones_convolution_table_correct :
    ∀ n : Fin 10, onesConvolutionTable n = onesConvolutionCoeff n := by
  native_decide

theorem sum_ones_eq_succ :
    ∀ n : Fin 16, onesConvolutionCoeff n = (n : ℕ) + 1 := by native_decide

/-- Catalan coefficient `C_n = binom(2n,n)/(n+1)`. -/
def catalanCoeff (n : ℕ) : ℕ :=
  centralBinom n / (n + 1)

/-- Catalan numbers `C_0..C_10`. -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

theorem catalan_table_correct :
    ∀ n : Fin 11, catalanTable n = catalanCoeff n := by native_decide

/-- Product of Catalan GF with the geometric GF: partial sums of Catalan numbers. -/
def catalanTimesGeomCoeff (n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), catalanCoeff k

/-- Coefficients of `C(z)/(1-z)` for `n = 0..9`. -/
def catalanTimesGeomTable : Fin 10 → ℕ :=
  ![1, 2, 4, 9, 23, 65, 197, 626, 2056, 6918]

theorem catalan_times_geometric_small_cases :
    ∀ n : Fin 10, catalanTimesGeomTable n = catalanTimesGeomCoeff n := by
  native_decide

theorem catalan_times_geometric_specific_values :
    catalanTimesGeomTable 0 = 1 ∧
    catalanTimesGeomTable 1 = 2 ∧
    catalanTimesGeomTable 2 = 4 ∧
    catalanTimesGeomTable 3 = 9 ∧
    catalanTimesGeomTable 4 = 23 ∧
    catalanTimesGeomTable 5 = 65 ∧
    catalanTimesGeomTable 6 = 197 ∧
    catalanTimesGeomTable 7 = 626 ∧
    catalanTimesGeomTable 8 = 2056 ∧
    catalanTimesGeomTable 9 = 6918 := by
  native_decide

/-- Coefficient of `z * C(z)^2` at index `n`. -/
def catalanFunctionalRhsCoeff (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    ∑ k : Fin n, catalanCoeff k * catalanCoeff (n - 1 - k)

/-- Coefficient recurrence `C_n = sum_{k=0}^{n-1} C_k C_{n-1-k}`. -/
def catalanConvolutionCoeff (n : ℕ) : ℕ :=
  ∑ k : Fin n, catalanCoeff k * catalanCoeff (n - 1 - k)

theorem catalan_functional_equation_small :
    ∀ n : Fin 11, catalanCoeff n = catalanFunctionalRhsCoeff n := by
  native_decide

theorem catalan_convolution_equals_closed_form :
    ∀ n : Fin 10,
      catalanConvolutionCoeff ((n : ℕ) + 1) =
        centralBinom ((n : ℕ) + 1) / ((n : ℕ) + 2) := by
  native_decide

theorem catalan_convolution_equals_next_catalan :
    ∀ n : Fin 10,
      catalanCoeff ((n : ℕ) + 1) =
        ∑ k : Fin ((n : ℕ) + 1),
          catalanCoeff k * catalanCoeff ((n : ℕ) - k) := by
  native_decide

/-- `n! > 2^n` for `n = 4..12`. -/
theorem factorial_grows_faster_than_two_pow :
    ∀ i : Fin 9,
      2 ^ ((i : ℕ) + 4) < Nat.factorial ((i : ℕ) + 4) := by
  native_decide

/-- `n! < n^n` for `n = 2..8`. -/
theorem factorial_lt_self_power_small :
    ∀ i : Fin 7,
      Nat.factorial ((i : ℕ) + 2) < ((i : ℕ) + 2) ^ ((i : ℕ) + 2) := by
  native_decide

/-- Lower integer approximations to `1000 * e^n` for `n = 2..8`. -/
def expPowLower1000 : Fin 7 → ℕ :=
  ![7389, 20085, 54598, 148413, 403428, 1096633, 2980957]

/-- Upper integer approximations to `1000 * e^n` for `n = 2..8`. -/
def expPowUpper1000 : Fin 7 → ℕ :=
  ![7390, 20086, 54599, 148414, 403429, 1096634, 2980958]

/--
Integer Stirling-style comparison for `(n/e)^n`:
using scaled bounds for `e^n`, the ratio `n! e^n / n^n`
is between `3` and `8` for `n = 2..8`.
-/
theorem stirling_scaled_ratio_bounds :
    ∀ i : Fin 7,
      let n := (i : ℕ) + 2
      3 * 1000 * n ^ n ≤ Nat.factorial n * expPowLower1000 i ∧
        Nat.factorial n * expPowUpper1000 i ≤ 8 * 1000 * n ^ n := by
  native_decide

/-- In particular, `n!` is larger than the scaled lower comparison `(n/e)^n`. -/
theorem factorial_gt_scaled_n_over_e_pow :
    ∀ i : Fin 7,
      let n := (i : ℕ) + 2
      1000 * n ^ n < Nat.factorial n * expPowLower1000 i := by
  native_decide

/-- Crossover check: `2^n < n!` exactly from `n = 4` onward, for `n = 0..12`. -/
theorem two_pow_factorial_crossover :
    ∀ n : Fin 13, (2 ^ (n : ℕ) < Nat.factorial (n : ℕ)) = (4 ≤ (n : ℕ)) := by
  native_decide

/-- The false side of the crossover: `2^n < n!` fails for `n = 0,1,2,3`. -/
theorem two_pow_not_below_factorial_before_four :
    ∀ n : Fin 4, ¬ 2 ^ (n : ℕ) < Nat.factorial (n : ℕ) := by
  native_decide

/-- The true side of the crossover: `2^n < n!` for `n = 4..12`. -/
theorem two_pow_below_factorial_from_four_to_twelve :
    ∀ i : Fin 9, 2 ^ ((i : ℕ) + 4) < Nat.factorial ((i : ℕ) + 4) := by
  native_decide



structure GeneratingFunctionAnalyticityBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneratingFunctionAnalyticityBudgetCertificate.controlled
    (c : GeneratingFunctionAnalyticityBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GeneratingFunctionAnalyticityBudgetCertificate.budgetControlled
    (c : GeneratingFunctionAnalyticityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GeneratingFunctionAnalyticityBudgetCertificate.Ready
    (c : GeneratingFunctionAnalyticityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneratingFunctionAnalyticityBudgetCertificate.size
    (c : GeneratingFunctionAnalyticityBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem generatingFunctionAnalyticity_budgetCertificate_le_size
    (c : GeneratingFunctionAnalyticityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGeneratingFunctionAnalyticityBudgetCertificate :
    GeneratingFunctionAnalyticityBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleGeneratingFunctionAnalyticityBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.controlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]

example :
    sampleGeneratingFunctionAnalyticityBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionAnalyticityBudgetCertificate.size := by
  apply generatingFunctionAnalyticity_budgetCertificate_le_size
  constructor
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.controlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGeneratingFunctionAnalyticityBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.controlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]
  · norm_num [GeneratingFunctionAnalyticityBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionAnalyticityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneratingFunctionAnalyticityBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionAnalyticityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List GeneratingFunctionAnalyticityBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneratingFunctionAnalyticityBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGeneratingFunctionAnalyticityBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.GeneratingFunctionAnalyticity
