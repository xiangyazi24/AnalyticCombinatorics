import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.PeriodicCoefficients


/-!
  Chapter IV theme: bounded executable tables for periodic fluctuations in
  coefficient sequences.  The examples are intentionally finite windows.
-/

/-! ## Coefficients of `1 / (1 - z^k)` -/

/-- Coefficients of `1 / (1 - z^2)` through degree `11`. -/
def geomPeriodTwoCoeffs : Fin 12 → ℕ :=
  ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Coefficients of `1 / (1 - z^3)` through degree `11`. -/
def geomPeriodThreeCoeffs : Fin 12 → ℕ :=
  ![1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]

/-- Coefficients of `1 / (1 - z^4)` through degree `11`. -/
def geomPeriodFourCoeffs : Fin 12 → ℕ :=
  ![1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]

def oneOverOneMinusZPowCoeff (k n : ℕ) : ℕ :=
  if n % k = 0 then 1 else 0

theorem geom_period_two_coeffs :
    ∀ i : Fin 12, geomPeriodTwoCoeffs i = oneOverOneMinusZPowCoeff 2 i := by
  native_decide

theorem geom_period_three_coeffs :
    ∀ i : Fin 12, geomPeriodThreeCoeffs i = oneOverOneMinusZPowCoeff 3 i := by
  native_decide

theorem geom_period_four_coeffs :
    ∀ i : Fin 12, geomPeriodFourCoeffs i = oneOverOneMinusZPowCoeff 4 i := by
  native_decide

/-! ## A small rational product with congruence fluctuations -/

/-- Coefficients of `1 / ((1 - z^2) (1 - z^3))` through degree `14`. -/
def coinTwoThreeCoeffs : Fin 15 → ℕ :=
  ![1, 0, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3]

def coinTwoThreeCoeffNat (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl
    (fun acc a =>
      if 2 * a ≤ n ∧ (n - 2 * a) % 3 = 0 then acc + 1 else acc)
    0

theorem coin_two_three_coeffs :
    ∀ i : Fin 15, coinTwoThreeCoeffs i = coinTwoThreeCoeffNat i := by
  native_decide

/-! ## Binary partitions -/

/-- Number of partitions of `n` into powers of two for `0 ≤ n ≤ 14`. -/
def binaryPartitionTable : Fin 15 → ℕ :=
  ![1, 1, 2, 2, 4, 4, 6, 6, 10, 10, 14, 14, 20, 20, 26]

def binaryPartitionSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 6
  | 7 => 6
  | 8 => 10
  | 9 => 10
  | 10 => 14
  | 11 => 14
  | 12 => 20
  | 13 => 20
  | 14 => 26
  | _ => 0

theorem binary_partition_table :
    ∀ i : Fin 15, binaryPartitionTable i = binaryPartitionSmall i := by
  native_decide

theorem binary_partition_odd_repeats_previous :
    ∀ i : Fin 7,
      binaryPartitionSmall (2 * (i : ℕ) + 1) =
        binaryPartitionSmall (2 * (i : ℕ)) := by
  native_decide

/-! ## Compositions into bounded parts -/

/-- Compositions of `n` into parts of size at most `2`, for `0 ≤ n ≤ 14`. -/
def compositionsLETwo : Fin 15 → ℕ :=
  ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]

def compositionsLETwoSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 8
  | 6 => 13
  | 7 => 21
  | 8 => 34
  | 9 => 55
  | 10 => 89
  | 11 => 144
  | 12 => 233
  | 13 => 377
  | 14 => 610
  | _ => 0

/-- Compositions of `n` into parts of size at most `3`, for `0 ≤ n ≤ 14`. -/
def compositionsLEThree : Fin 15 → ℕ :=
  ![1, 1, 2, 4, 7, 13, 24, 44, 81, 149, 274, 504, 927, 1705, 3136]

def compositionsLEThreeSmall : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 13
  | 6 => 24
  | 7 => 44
  | 8 => 81
  | 9 => 149
  | 10 => 274
  | 11 => 504
  | 12 => 927
  | 13 => 1705
  | 14 => 3136
  | _ => 0

theorem compositions_le_two_table :
    ∀ i : Fin 15, compositionsLETwo i = compositionsLETwoSmall i := by
  native_decide

theorem compositions_le_two_fibonacci_window :
    ∀ i : Fin 13,
      compositionsLETwoSmall ((i : ℕ) + 2) =
        compositionsLETwoSmall ((i : ℕ) + 1) + compositionsLETwoSmall i := by
  native_decide

theorem compositions_le_three_table :
    ∀ i : Fin 15, compositionsLEThree i = compositionsLEThreeSmall i := by
  native_decide

theorem compositions_le_three_tribonacci_window :
    ∀ i : Fin 12,
      compositionsLEThreeSmall ((i : ℕ) + 3) =
        compositionsLEThreeSmall ((i : ℕ) + 2) +
          compositionsLEThreeSmall ((i : ℕ) + 1) +
            compositionsLEThreeSmall i := by
  native_decide

/-! ## Oscillating and digital tables -/

/-- A shifted period-four oscillation, modelling a bounded Rademacher-type term. -/
def shiftedRademacherOscillation : Fin 12 → ℕ :=
  ![2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1]

def shiftedRademacherOscillationSmall (n : ℕ) : ℕ :=
  match n % 4 with
  | 0 => 2
  | 1 => 3
  | 2 => 2
  | _ => 1

theorem shifted_rademacher_oscillation_table :
    ∀ i : Fin 12,
      shiftedRademacherOscillation i = shiftedRademacherOscillationSmall i := by
  native_decide

/-- A digital periodic solution with period three. -/
def digitalPeriodThree : Fin 12 → ℕ :=
  ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

def digitalPeriodThreeSmall (n : ℕ) : ℕ :=
  n % 3

theorem digital_period_three_table :
    ∀ i : Fin 12, digitalPeriodThree i = digitalPeriodThreeSmall i := by
  native_decide

theorem digital_period_three_repeats :
    ∀ i : Fin 12,
      digitalPeriodThreeSmall ((i : ℕ) + 3) = digitalPeriodThreeSmall i := by
  native_decide

/-! ## Ruler sequence -/

/-- The ruler sequence `v₂(n)` for `1 ≤ n ≤ 15`. -/
def rulerSequence : Fin 15 → ℕ :=
  ![0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

def rulerSmall : ℕ → ℕ
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 3
  | 9 => 0
  | 10 => 1
  | 11 => 0
  | 12 => 2
  | 13 => 0
  | 14 => 1
  | 15 => 0
  | _ => 0

theorem ruler_sequence_table :
    ∀ i : Fin 15, rulerSequence i = rulerSmall ((i : ℕ) + 1) := by
  native_decide

theorem ruler_sequence_odd_entries_zero :
    ∀ i : Fin 8, rulerSmall (2 * (i : ℕ) + 1) = 0 := by
  native_decide



structure PeriodicCoefficientsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PeriodicCoefficientsBudgetCertificate.controlled
    (c : PeriodicCoefficientsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def PeriodicCoefficientsBudgetCertificate.budgetControlled
    (c : PeriodicCoefficientsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def PeriodicCoefficientsBudgetCertificate.Ready
    (c : PeriodicCoefficientsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PeriodicCoefficientsBudgetCertificate.size
    (c : PeriodicCoefficientsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem periodicCoefficients_budgetCertificate_le_size
    (c : PeriodicCoefficientsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def samplePeriodicCoefficientsBudgetCertificate :
    PeriodicCoefficientsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : samplePeriodicCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicCoefficientsBudgetCertificate.controlled,
      samplePeriodicCoefficientsBudgetCertificate]
  · norm_num [PeriodicCoefficientsBudgetCertificate.budgetControlled,
      samplePeriodicCoefficientsBudgetCertificate]

example :
    samplePeriodicCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicCoefficientsBudgetCertificate.size := by
  apply periodicCoefficients_budgetCertificate_le_size
  constructor
  · norm_num [PeriodicCoefficientsBudgetCertificate.controlled,
      samplePeriodicCoefficientsBudgetCertificate]
  · norm_num [PeriodicCoefficientsBudgetCertificate.budgetControlled,
      samplePeriodicCoefficientsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    samplePeriodicCoefficientsBudgetCertificate.Ready := by
  constructor
  · norm_num [PeriodicCoefficientsBudgetCertificate.controlled,
      samplePeriodicCoefficientsBudgetCertificate]
  · norm_num [PeriodicCoefficientsBudgetCertificate.budgetControlled,
      samplePeriodicCoefficientsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePeriodicCoefficientsBudgetCertificate.certificateBudgetWindow ≤
      samplePeriodicCoefficientsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List PeriodicCoefficientsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePeriodicCoefficientsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady samplePeriodicCoefficientsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.PeriodicCoefficients
