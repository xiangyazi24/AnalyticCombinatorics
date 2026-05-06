import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.GFConvergence


open Finset

/-!
# Generating Function Convergence: finite certificates

The analytic theorems in Chapter V of Flajolet and Sedgewick are represented
here only by numerical certificates that Lean can decide directly.  In
particular, "radius" statements below are encoded by finite ratio-test data,
singularity equations, and small coefficient checks, not by real-analysis
limits.
-/

-- ============================================================
-- Section 1: Geometric series, radius 1
-- ============================================================

def geometricCoeffNat (n : Nat) : Nat := n - n + 1

def geometricCoeffQ (n : Nat) : Rat := (n : Rat) - (n : Rat) + 1

def geometricRatioStep (n : Nat) : Bool :=
  geometricCoeffQ (n + 1) == geometricCoeffQ n

def geometricRadius : Rat := 1

def geometricDenominator (z : Rat) : Rat := 1 - z

def geometricPartialAtHalf (N : Nat) : Rat :=
  ∑ n ∈ range N, (1 / 2 : Rat) ^ n

theorem geometric_ratio_test_prefix :
    (∀ n : Fin 12, geometricRatioStep n.val = true) ∧
      geometricRadius = 1 ∧
      geometricDenominator geometricRadius = 0 := by
  native_decide

theorem geometric_inside_unit_partial_sums :
    geometricPartialAtHalf 1 = 1 ∧
      geometricPartialAtHalf 2 = 3 / 2 ∧
      geometricPartialAtHalf 4 = 15 / 8 ∧
      geometricPartialAtHalf 8 = 255 / 128 := by
  native_decide

-- ============================================================
-- Section 2: Exponential EGF, infinite radius by factorial growth
-- ============================================================

def expCoeffQ (n : Nat) : Rat := (1 : Rat) / Nat.factorial n

def expRatioStep (n : Nat) : Bool :=
  expCoeffQ (n + 1) * ((n + 1 : Nat) : Rat) == expCoeffQ n

def expTermAtNatRadius (r n : Nat) : Rat :=
  ((r : Rat) ^ n) / Nat.factorial n

theorem exponential_ratio_prefix :
    ∀ n : Fin 12, expRatioStep n.val = true := by
  native_decide

theorem factorial_beats_selected_powers :
    Nat.factorial 8 > 2 ^ 8 ∧
      Nat.factorial 10 > 3 ^ 10 ∧
      Nat.factorial 12 > 4 ^ 12 ∧
      Nat.factorial 12 > 5 ^ 12 ∧
      Nat.factorial 18 > 7 ^ 18 ∧
      Nat.factorial 30 > 10 ^ 30 := by
  native_decide

theorem exponential_terms_get_small_at_sample_radii :
    expTermAtNatRadius 2 8 < 1 ∧
      expTermAtNatRadius 3 10 < 1 ∧
      expTermAtNatRadius 4 12 < 1 ∧
      expTermAtNatRadius 5 12 < 1 ∧
      expTermAtNatRadius 10 30 < 1 := by
  native_decide

-- ============================================================
-- Section 3: Catalan GF, radius 1/4
-- ============================================================

def catalan (n : Nat) : Nat := Nat.choose (2 * n) n / (n + 1)

def catalanRadius : Rat := 1 / 4

def catalanRatioStep (n : Nat) : Bool :=
  catalan (n + 1) * (n + 2) == catalan n * (4 * n + 2)

def catalanKernel (z y : Rat) : Rat := z * y ^ 2 - y + 1

def catalanDiscriminant (z : Rat) : Rat := 1 - 4 * z

theorem catalan_initial_values :
    catalan 0 = 1 ∧
      catalan 1 = 1 ∧
      catalan 2 = 2 ∧
      catalan 3 = 5 ∧
      catalan 4 = 14 ∧
      catalan 5 = 42 ∧
      catalan 6 = 132 ∧
      catalan 7 = 429 := by
  native_decide

theorem catalan_ratio_test_prefix :
    ∀ n : Fin 10, catalanRatioStep n.val = true := by
  native_decide

theorem catalan_radius_singularity_certificate :
    catalanRadius = 1 / 4 ∧
      0 < catalanRadius ∧
      catalanDiscriminant catalanRadius = 0 ∧
      catalanKernel catalanRadius 2 = 0 := by
  native_decide

-- ============================================================
-- Section 4: Fibonacci GF, radius 1/phi
-- ============================================================

def fibonacciCoeff (n : Nat) : Nat := Nat.fib n

def fibonacciDenominator (z : Rat) : Rat := 1 - z - z ^ 2

def goldenPolynomial (x : Rat) : Rat := x ^ 2 - x - 1

def reciprocalPhiPolynomial (rho : Rat) : Rat := rho ^ 2 + rho - 1

def phiLowerApprox : Rat := 144 / 89

def phiUpperApprox : Rat := 233 / 144

def fibRadiusLowerApprox : Rat := 55 / 89

def fibRadiusUpperApprox : Rat := 89 / 144

theorem fibonacci_initial_values :
    fibonacciCoeff 0 = 0 ∧
      fibonacciCoeff 1 = 1 ∧
      fibonacciCoeff 2 = 1 ∧
      fibonacciCoeff 3 = 2 ∧
      fibonacciCoeff 4 = 3 ∧
      fibonacciCoeff 5 = 5 ∧
      fibonacciCoeff 6 = 8 ∧
      fibonacciCoeff 7 = 13 ∧
      fibonacciCoeff 8 = 21 ∧
      fibonacciCoeff 9 = 34 ∧
      fibonacciCoeff 10 = 55 := by
  native_decide

theorem fibonacci_recurrence_prefix :
    ∀ n : Fin 10,
      fibonacciCoeff (n.val + 2) = fibonacciCoeff (n.val + 1) + fibonacciCoeff n.val := by
  native_decide

theorem golden_ratio_bracket_certificate :
    0 < phiLowerApprox ∧
      phiLowerApprox < phiUpperApprox ∧
      goldenPolynomial phiLowerApprox < 0 ∧
      0 < goldenPolynomial phiUpperApprox := by
  native_decide

theorem fibonacci_radius_reciprocal_phi_certificate :
    0 < fibRadiusLowerApprox ∧
      fibRadiusLowerApprox < fibRadiusUpperApprox ∧
      reciprocalPhiPolynomial fibRadiusLowerApprox < 0 ∧
      0 < reciprocalPhiPolynomial fibRadiusUpperApprox ∧
      fibonacciDenominator fibRadiusLowerApprox > 0 ∧
      fibonacciDenominator fibRadiusUpperApprox < 0 ∧
      fibRadiusUpperApprox = 1 / phiLowerApprox := by
  native_decide

-- ============================================================
-- Section 5: Hadamard theorem, radius product checks
-- ============================================================

def powCoeff (k n : Nat) : Nat := k ^ n

def hadamardCoeff (a b : Nat -> Nat) (n : Nat) : Nat := a n * b n

def powCoeffRadius (k : Nat) : Rat := 1 / (k : Rat)

def hadamardCatalanPowTwo (n : Nat) : Nat := catalan n * 2 ^ n

theorem hadamard_geometric_2_3_coefficients :
    ∀ n : Fin 9,
      hadamardCoeff (powCoeff 2) (powCoeff 3) n.val = powCoeff 6 n.val := by
  native_decide

theorem hadamard_geometric_2_3_radius_product :
    powCoeffRadius 2 * powCoeffRadius 3 = powCoeffRadius 6 := by
  native_decide

theorem hadamard_geometric_2_3_radius_bound :
    powCoeffRadius 2 * powCoeffRadius 3 <= powCoeffRadius 6 := by
  native_decide

theorem hadamard_unit_geometric_5_coefficients :
    ∀ n : Fin 9,
      hadamardCoeff geometricCoeffNat (powCoeff 5) n.val = powCoeff 5 n.val := by
  native_decide

theorem hadamard_unit_geometric_5_radius_product :
    geometricRadius * powCoeffRadius 5 = powCoeffRadius 5 := by
  native_decide

theorem hadamard_unit_geometric_5_radius_bound :
    geometricRadius * powCoeffRadius 5 <= powCoeffRadius 5 := by
  native_decide

theorem hadamard_catalan_geometric_values :
    hadamardCatalanPowTwo 0 = 1 ∧
      hadamardCatalanPowTwo 1 = 2 ∧
      hadamardCatalanPowTwo 2 = 8 ∧
      hadamardCatalanPowTwo 3 = 40 ∧
      hadamardCatalanPowTwo 4 = 224 ∧
      hadamardCatalanPowTwo 5 = 1344 := by
  native_decide

theorem hadamard_catalan_geometric_radius_product :
    catalanRadius * powCoeffRadius 2 = 1 / 8 := by
  native_decide

theorem hadamard_catalan_geometric_radius_bound :
    catalanRadius * powCoeffRadius 2 <= (1 / 8 : Rat) := by
  native_decide

-- ============================================================
-- Section 6: Pringsheim consequence, positive-axis singularities
-- ============================================================

def positivePrefix (a : Nat -> Nat) (N : Nat) : Bool :=
  (List.range N).all fun n => a n != 0

def positivePrefixFrom (a : Nat -> Nat) (start N : Nat) : Bool :=
  (List.range N).all fun n => a (start + n) != 0

def doubleGeometricCoeff (n : Nat) : Nat := 2 ^ n

def doubleGeometricDenominator (z : Rat) : Rat := 1 - 2 * z

theorem pringsheim_geometric_certificate :
    positivePrefix geometricCoeffNat 12 = true ∧
      0 < (1 : Rat) ∧
      geometricDenominator 1 = 0 := by
  native_decide

theorem pringsheim_double_geometric_certificate :
    positivePrefix doubleGeometricCoeff 12 = true ∧
      0 < (1 / 2 : Rat) ∧
      doubleGeometricDenominator (1 / 2) = 0 := by
  native_decide

theorem pringsheim_catalan_certificate :
    positivePrefix catalan 12 = true ∧
      0 < catalanRadius ∧
      catalanDiscriminant catalanRadius = 0 := by
  native_decide

theorem pringsheim_fibonacci_certificate :
    positivePrefixFrom fibonacciCoeff 1 12 = true ∧
      0 < fibRadiusLowerApprox ∧
      fibRadiusLowerApprox < fibRadiusUpperApprox ∧
      fibonacciDenominator fibRadiusLowerApprox > 0 ∧
      fibonacciDenominator fibRadiusUpperApprox < 0 := by
  native_decide



structure GFConvergenceBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GFConvergenceBudgetCertificate.controlled
    (c : GFConvergenceBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GFConvergenceBudgetCertificate.budgetControlled
    (c : GFConvergenceBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GFConvergenceBudgetCertificate.Ready
    (c : GFConvergenceBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GFConvergenceBudgetCertificate.size
    (c : GFConvergenceBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem gFConvergence_budgetCertificate_le_size
    (c : GFConvergenceBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGFConvergenceBudgetCertificate :
    GFConvergenceBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleGFConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [GFConvergenceBudgetCertificate.controlled,
      sampleGFConvergenceBudgetCertificate]
  · norm_num [GFConvergenceBudgetCertificate.budgetControlled,
      sampleGFConvergenceBudgetCertificate]

example :
    sampleGFConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleGFConvergenceBudgetCertificate.size := by
  apply gFConvergence_budgetCertificate_le_size
  constructor
  · norm_num [GFConvergenceBudgetCertificate.controlled,
      sampleGFConvergenceBudgetCertificate]
  · norm_num [GFConvergenceBudgetCertificate.budgetControlled,
      sampleGFConvergenceBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleGFConvergenceBudgetCertificate.Ready := by
  constructor
  · norm_num [GFConvergenceBudgetCertificate.controlled,
      sampleGFConvergenceBudgetCertificate]
  · norm_num [GFConvergenceBudgetCertificate.budgetControlled,
      sampleGFConvergenceBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGFConvergenceBudgetCertificate.certificateBudgetWindow ≤
      sampleGFConvergenceBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List GFConvergenceBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGFConvergenceBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGFConvergenceBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.GFConvergence
