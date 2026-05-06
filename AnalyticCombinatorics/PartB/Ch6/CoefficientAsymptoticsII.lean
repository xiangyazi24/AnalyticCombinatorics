import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.CoefficientAsymptoticsII


/-!
  Finite coefficient tables inspired by the advanced coefficient asymptotics
  of Chapter VI of Flajolet and Sedgewick.

  The entries below record bounded checks for stretched-exponential labelled
  classes, saddle-point scales, large powers, Gaussian central windows, and
  central binomial residues.
-/

def tableAt {m : ℕ} (t : Fin m → ℕ) (n : ℕ) : ℕ :=
  if h : n < m then t ⟨n, h⟩ else 0

-- ============================================================
-- Stretched-exponential labelled classes
-- ============================================================

/-- Number of involutions on `n` labelled atoms. -/
def involutionNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionNumber (n + 1) + (n + 1) * involutionNumber n

/--
Scaled coefficients of `exp(z + z^2 / 2)`.

This is the finite coefficient formula
`n! [z^n] exp(z + z^2/2)`.
-/
def expLinearQuadraticCoeffScaled (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum
    (fun j =>
      Nat.factorial n /
        (Nat.factorial (n - 2 * j) * Nat.factorial j * 2 ^ j))

/-- Involution values for `n = 0, ..., 11`. -/
def involutionTable : Fin 12 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232, 764, 2620, 9496, 35696]

/-- The recurrence table for involutions agrees with the displayed values. -/
theorem involution_values_0_11 :
    ∀ n : Fin 12, involutionNumber n = involutionTable n := by native_decide

/-- The coefficient formula for `exp(z + z^2 / 2)` gives the same table. -/
theorem exp_linear_quadratic_values_0_11 :
    ∀ n : Fin 12, expLinearQuadraticCoeffScaled n = involutionTable n := by native_decide

/-- The finite involution recurrence is checked on `n = 2, ..., 11`. -/
theorem involution_recurrence_2_11 :
    ∀ n : Fin 10,
      tableAt involutionTable ((n : ℕ) + 2) =
        tableAt involutionTable ((n : ℕ) + 1) +
          ((n : ℕ) + 1) * tableAt involutionTable n := by native_decide

/-- Bell numbers for set partitions, `B_0, ..., B_10`. -/
def bellTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147, 115975]

/-- The Bell recurrence `B_{n+1} = sum_k binom(n,k) B_k` holds for this table. -/
theorem bell_recurrence_0_9 :
    ∀ n : Fin 10,
      tableAt bellTable ((n : ℕ) + 1) =
        (Finset.range ((n : ℕ) + 1)).sum
          (fun k => Nat.choose n k * tableAt bellTable k) := by native_decide

/-- A small ratio check reflecting the fast stretched-exponential growth. -/
theorem bell_growth_spot_checks :
    tableAt bellTable 8 > 4 * tableAt bellTable 7 ∧
    tableAt bellTable 9 > 5 * tableAt bellTable 8 ∧
    tableAt bellTable 10 > 5 * tableAt bellTable 9 := by native_decide

-- ============================================================
-- Hayman saddle-point scales
-- ============================================================

/--
For `f(z) = exp(z/(1-z))`, the Hayman scale
`a(r) = r / (1-r)^2`, sampled at `r = t/(t+1)`.
-/
def expSequenceHaymanA (t : ℕ) : ℕ :=
  t * (t + 1)

/--
For `f(z) = exp(z/(1-z))`, the Hayman scale
`b(r) = r(1+r) / (1-r)^3`, sampled at `r = t/(t+1)`.
-/
def expSequenceHaymanB (t : ℕ) : ℕ :=
  t * (t + 1) * (2 * t + 1)

/-- Values of `a(t/(t+1))` for `t = 0, ..., 7`. -/
def haymanATable : Fin 8 → ℕ :=
  ![0, 2, 6, 12, 20, 30, 42, 56]

/-- Values of `b(t/(t+1))` for `t = 0, ..., 7`. -/
def haymanBTable : Fin 8 → ℕ :=
  ![0, 6, 30, 84, 180, 330, 546, 840]

/-- The finite Hayman `a` table agrees with the sampled closed form. -/
theorem hayman_a_values_0_7 :
    ∀ t : Fin 8, expSequenceHaymanA t = haymanATable t := by native_decide

/-- The finite Hayman `b` table agrees with the sampled closed form. -/
theorem hayman_b_values_0_7 :
    ∀ t : Fin 8, expSequenceHaymanB t = haymanBTable t := by native_decide

/-- In this sample, the variance scale dominates the mean scale after `t = 1`. -/
theorem hayman_b_dominates_a_2_7 :
    ∀ t : Fin 6,
      tableAt haymanBTable ((t : ℕ) + 2) >
        tableAt haymanATable ((t : ℕ) + 2) := by native_decide

-- ============================================================
-- Large powers of generating functions
-- ============================================================

/-- Coefficient of `z^n` in `(1 + z + z^2)^k`. -/
def ternaryPowerCoeff (k n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum
    (fun j => Nat.choose k j * Nat.choose (k - j) (n - 2 * j))

/-- Coefficients of `(1 + z + z^2)^5`, from degree `0` to degree `10`. -/
def ternaryPowerFiveTable : Fin 11 → ℕ :=
  ![1, 5, 15, 30, 45, 51, 45, 30, 15, 5, 1]

/-- The coefficient formula gives the fifth large-power row. -/
theorem ternary_power_five_values :
    ∀ n : Fin 11, ternaryPowerCoeff 5 n = ternaryPowerFiveTable n := by native_decide

/-- The row is palindromic, as expected from the reciprocal polynomial. -/
theorem ternary_power_five_symmetry :
    ∀ n : Fin 11,
      tableAt ternaryPowerFiveTable n =
        tableAt ternaryPowerFiveTable (10 - (n : ℕ)) := by native_decide

/-- The central coefficient is the maximum in this bounded row. -/
theorem ternary_power_five_center_dominates :
    ∀ n : Fin 11,
      tableAt ternaryPowerFiveTable n ≤ tableAt ternaryPowerFiveTable 5 := by
  native_decide

-- ============================================================
-- Gaussian central windows
-- ============================================================

/-- The central binomial row `binom(10,k)`, `k = 0, ..., 10`. -/
def binomialRowTenTable : Fin 11 → ℕ :=
  ![1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1]

/-- The displayed row agrees with `Nat.choose 10 k`. -/
theorem binomial_row_ten_values :
    ∀ k : Fin 11, Nat.choose 10 k = binomialRowTenTable k := by native_decide

def squareDistanceFromFive (k : ℕ) : ℕ :=
  if k ≤ 5 then (5 - k) ^ 2 else (k - 5) ^ 2

/-- A finite variance identity for the Gaussian central window of the row. -/
theorem binomial_row_ten_centered_second_moment :
    (Finset.range 11).sum
      (fun k => squareDistanceFromFive k * tableAt binomialRowTenTable k) = 2560 := by native_decide

/-- The center is the maximum of the row. -/
theorem binomial_row_ten_center_dominates :
    ∀ k : Fin 11, tableAt binomialRowTenTable k ≤ tableAt binomialRowTenTable 5 := by native_decide

-- ============================================================
-- Middle binomial coefficients modulo primes
-- ============================================================

def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

/-- Small primes used for the bounded residue table. -/
def smallPrimeTable : Fin 5 → ℕ :=
  ![2, 3, 5, 7, 11]

/-- Middle binomial coefficients `binom(2p,p)` for the small primes above. -/
def centralBinomialPrimeTable : Fin 5 → ℕ :=
  ![6, 20, 252, 3432, 705432]

/-- The central binomial formula agrees with the displayed prime-indexed table. -/
theorem central_binomial_prime_values :
    ∀ i : Fin 5,
      centralBinomial (smallPrimeTable i) = centralBinomialPrimeTable i := by native_decide

/-- The elementary prime residue `binom(2p,p) ≡ 2 mod p` in this bounded range. -/
theorem central_binomial_mod_small_primes :
    ∀ i : Fin 5,
      centralBinomial (smallPrimeTable i) % smallPrimeTable i =
        2 % smallPrimeTable i := by native_decide



structure CoefficientAsymptoticsIIBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CoefficientAsymptoticsIIBudgetCertificate.controlled
    (c : CoefficientAsymptoticsIIBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CoefficientAsymptoticsIIBudgetCertificate.budgetControlled
    (c : CoefficientAsymptoticsIIBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CoefficientAsymptoticsIIBudgetCertificate.Ready
    (c : CoefficientAsymptoticsIIBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CoefficientAsymptoticsIIBudgetCertificate.size
    (c : CoefficientAsymptoticsIIBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem coefficientAsymptoticsII_budgetCertificate_le_size
    (c : CoefficientAsymptoticsIIBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCoefficientAsymptoticsIIBudgetCertificate :
    CoefficientAsymptoticsIIBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCoefficientAsymptoticsIIBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.controlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.budgetControlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]

example :
    sampleCoefficientAsymptoticsIIBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientAsymptoticsIIBudgetCertificate.size := by
  apply coefficientAsymptoticsII_budgetCertificate_le_size
  constructor
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.controlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.budgetControlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCoefficientAsymptoticsIIBudgetCertificate.Ready := by
  constructor
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.controlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]
  · norm_num [CoefficientAsymptoticsIIBudgetCertificate.budgetControlled,
      sampleCoefficientAsymptoticsIIBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCoefficientAsymptoticsIIBudgetCertificate.certificateBudgetWindow ≤
      sampleCoefficientAsymptoticsIIBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CoefficientAsymptoticsIIBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCoefficientAsymptoticsIIBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCoefficientAsymptoticsIIBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.CoefficientAsymptoticsII
