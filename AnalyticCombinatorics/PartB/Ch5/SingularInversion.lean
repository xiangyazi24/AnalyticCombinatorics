import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.SingularInversion


/-!
# Singular Inversion and Implicit Function Asymptotics

Finite arithmetic checks for the singular-inversion viewpoint in Chapter V
of *Analytic Combinatorics*.  The file records rational checks for Catalan
singular inversion, Motzkin coefficient evidence, large Schroder growth-rate
evidence, Catalan ratio convergence, and convergent power sums.
-/

/-- Lookup in a finite natural-number table, extended by zero. -/
def coeffNat {N : ℕ} (a : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-! ## Catalan: `y = 1 + z*y^2` -/

/-- Catalan implicit equation residual over rationals. -/
def catalanResidual (z y : ℚ) : ℚ :=
  y - (1 + z * y ^ 2)

/-- At `z = 1/4`, `y = 2` satisfies `y = 1 + z*y^2`. -/
theorem catalan_singular_point_equation :
    catalanResidual (1 / 4) 2 = 0 := by
  native_decide

/-- The critical derivative condition `1 = 2*z*y` also holds at `(1/4, 2)`. -/
theorem catalan_singular_point_derivative :
    (2 : ℚ) * (1 / 4) * 2 = 1 := by
  native_decide

/-- The requested rational arithmetic check: `2 = 1 + (1/4)*4`. -/
theorem catalan_rational_check :
    (2 : ℚ) = 1 + (1 / 4) * 4 := by
  native_decide

/-! ## Motzkin: coefficient table and recurrence evidence

The standard Motzkin OGF is `M(z) = 1 + z*M(z) + z^2*M(z)^2`, whose
dominant singularity gives growth rate `3`.  The tempting point
`(z, y) = (1/3, 3/2)` for the different equation `y = 1 + z*y + z*y^2`
fails by direct rational arithmetic.
-/

/-- Residual for the nonstandard equation `y = 1 + z*y + z*y^2`. -/
def motzkinWrongResidual (z y : ℚ) : ℚ :=
  y - (1 + z * y + z * y ^ 2)

/-- The proposed `(1/3, 3/2)` check fails: the residual is `-3/4`. -/
theorem motzkin_wrong_point_residual :
    motzkinWrongResidual (1 / 3) (3 / 2) = -3 / 4 := by
  native_decide

/-- Residual for the standard Motzkin equation `y = 1 + z*y + z^2*y^2`. -/
def motzkinResidual (z y : ℚ) : ℚ :=
  y - (1 + z * y + z ^ 2 * y ^ 2)

/-- The standard Motzkin singular pair is `(z0, y0) = (1/3, 3)`. -/
theorem motzkin_standard_singular_equation :
    motzkinResidual (1 / 3) 3 = 0 := by
  native_decide

/-- Critical condition `1 = z + 2*z^2*y` at the standard Motzkin point. -/
theorem motzkin_standard_singular_derivative :
    (1 / 3 : ℚ) + 2 * (1 / 3 : ℚ) ^ 2 * 3 = 1 := by
  native_decide

/-- Motzkin numbers `M_0..M_10`. -/
def motzkinNumbers : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

/-- Addition form of the Motzkin recurrence for `n >= 2`. -/
def motzkinRecurrenceCheck (n : ℕ) : Bool :=
  (n + 2) * coeffNat motzkinNumbers n ==
    (2 * n + 1) * coeffNat motzkinNumbers (n - 1) +
      3 * (n - 1) * coeffNat motzkinNumbers (n - 2)

/-- Verify `(n+2)M_n = (2n+1)M_{n-1} + 3(n-1)M_{n-2}` for `n = 2..10`. -/
theorem motzkin_recurrence_n2_to_n10 :
    ∀ i : Fin 9, motzkinRecurrenceCheck (i.val + 2) = true := by
  native_decide

/-- Motzkin ratios as rational numbers, extended by zero at `n = 0`. -/
def motzkinRatio (n : ℕ) : ℚ :=
  if coeffNat motzkinNumbers (n - 1) = 0 then
    0
  else
    (coeffNat motzkinNumbers n : ℚ) / coeffNat motzkinNumbers (n - 1)

/-- Finite ratio evidence toward the Motzkin growth rate `3`, after the initial plateau. -/
theorem motzkin_ratio_increases_below_three :
    ∀ i : Fin 7, motzkinRatio (i.val + 3) < motzkinRatio (i.val + 4) ∧
      motzkinRatio (i.val + 4) < 3 := by
  native_decide

/-! ## Large Schroder singular point analysis

For `S(z) = 1 + z*S(z) + z*S(z)^2`, the dominant singularity is
`rho = 3 - 2*sqrt(2)`, so the growth rate is
`1/rho = 3 + 2*sqrt(2) = 5.828...`.
-/

/-- Large Schroder numbers `S_0..S_8`. -/
def largeSchroderNumbers : Fin 9 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558, 41586]

/-- Large Schroder ratio `S_n/S_{n-1}`, extended by zero at `n = 0`. -/
def schroderRatio (n : ℕ) : ℚ :=
  if coeffNat largeSchroderNumbers (n - 1) = 0 then
    0
  else
    (coeffNat largeSchroderNumbers n : ℚ) /
      coeffNat largeSchroderNumbers (n - 1)

/-- The large Schroder growth rate `3 + 2*sqrt(2)` is between `5.828` and `5.829`. -/
theorem schroder_growth_rate_decimal_bracket :
    ((5828 : ℚ) / 1000) ^ 2 - 6 * ((5828 : ℚ) / 1000) + 1 < 0 ∧
      0 < ((5829 : ℚ) / 1000) ^ 2 - 6 * ((5829 : ℚ) / 1000) + 1 := by
  native_decide

/-- Ratio evidence for `n = 3..7`: increasing and still below `5.829`. -/
theorem schroder_ratio_approaches_growth_rate_n3_to_n7 :
    ∀ i : Fin 4, schroderRatio (i.val + 3) < schroderRatio (i.val + 4) ∧
      schroderRatio (i.val + 3) < (5829 : ℚ) / 1000 ∧
      schroderRatio 7 < (5829 : ℚ) / 1000 := by
  native_decide

/-! ## Catalan ratio convergence to `4` -/

/-- The `n`-th Catalan number. -/
def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

/-- Catalan ratio `C_{n+1}/C_n`. -/
def catalanRatio (n : ℕ) : ℚ :=
  if catalanNumber n = 0 then
    0
  else
    (catalanNumber (n + 1) : ℚ) / catalanNumber n

/-- Closed form ratio `C_{n+1}/C_n = 2*(2*n+1)/(n+2)` for `n = 1..12`. -/
theorem catalan_ratio_formula_n1_to_n12 :
    ∀ i : Fin 12,
      let n := i.val + 1
      catalanRatio n = (2 * (2 * n + 1) : ℚ) / (n + 2) ∧
        catalanRatio n < 4 := by
  native_decide

/-- The displayed Catalan ratios increase on `n = 1..12`, giving finite evidence toward `4`. -/
theorem catalan_ratio_increases_n1_to_n12 :
    ∀ i : Fin 11, catalanRatio (i.val + 1) < catalanRatio (i.val + 2) := by
  native_decide

/-! ## Power-sum convergence checks -/

/-- Partial sum `sum_{k=1}^n 1/k^s` over rationals. -/
def powerSumPartial (s n : ℕ) : ℚ :=
  (Finset.range n).sum (fun k => (1 : ℚ) / (k + 1) ^ s)

/-- Partial sums for `s = 2` increase and stay below `2` on the displayed range. -/
theorem power_sum_s2_checks :
    powerSumPartial 2 1 < powerSumPartial 2 2 ∧
      powerSumPartial 2 2 < powerSumPartial 2 4 ∧
      powerSumPartial 2 4 < powerSumPartial 2 8 ∧
      powerSumPartial 2 12 < 2 := by
  native_decide

/-- Partial sums for `s = 3` increase and stay below `5/4` on the displayed range. -/
theorem power_sum_s3_checks :
    powerSumPartial 3 1 < powerSumPartial 3 2 ∧
      powerSumPartial 3 2 < powerSumPartial 3 4 ∧
      powerSumPartial 3 4 < powerSumPartial 3 8 ∧
      powerSumPartial 3 12 < (5 : ℚ) / 4 := by
  native_decide

/-- Partial sums for `s = 4` increase and stay below `11/10` on the displayed range. -/
theorem power_sum_s4_checks :
    powerSumPartial 4 1 < powerSumPartial 4 2 ∧
      powerSumPartial 4 2 < powerSumPartial 4 4 ∧
      powerSumPartial 4 4 < powerSumPartial 4 8 ∧
      powerSumPartial 4 12 < (11 : ℚ) / 10 := by
  native_decide



structure SingularInversionBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularInversionBudgetCertificate.controlled
    (c : SingularInversionBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SingularInversionBudgetCertificate.budgetControlled
    (c : SingularInversionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularInversionBudgetCertificate.Ready
    (c : SingularInversionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularInversionBudgetCertificate.size
    (c : SingularInversionBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularInversion_budgetCertificate_le_size
    (c : SingularInversionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularInversionBudgetCertificate :
    SingularInversionBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSingularInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularInversionBudgetCertificate.controlled,
      sampleSingularInversionBudgetCertificate]
  · norm_num [SingularInversionBudgetCertificate.budgetControlled,
      sampleSingularInversionBudgetCertificate]

example :
    sampleSingularInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularInversionBudgetCertificate.size := by
  apply singularInversion_budgetCertificate_le_size
  constructor
  · norm_num [SingularInversionBudgetCertificate.controlled,
      sampleSingularInversionBudgetCertificate]
  · norm_num [SingularInversionBudgetCertificate.budgetControlled,
      sampleSingularInversionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularInversionBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularInversionBudgetCertificate.controlled,
      sampleSingularInversionBudgetCertificate]
  · norm_num [SingularInversionBudgetCertificate.budgetControlled,
      sampleSingularInversionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularInversionBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularInversionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SingularInversionBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularInversionBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSingularInversionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.SingularInversion
