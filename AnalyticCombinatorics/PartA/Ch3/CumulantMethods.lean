import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-! # Ch III — Cumulant methods

Bounded, computational checks for moment-cumulant conversion, Bell-polynomial
coefficients, and small cumulant tables.
-/

namespace CumulantMethods

/-! ## Moment-cumulant conversion through order six -/

/-- First cumulant from raw moments. -/
def cumulant1 (m1 : ℚ) : ℚ :=
  m1

/-- Second cumulant from raw moments. -/
def cumulant2 (m1 m2 : ℚ) : ℚ :=
  m2 - m1 ^ 2

/-- Third cumulant from raw moments. -/
def cumulant3 (m1 m2 m3 : ℚ) : ℚ :=
  m3 - 3 * m2 * m1 + 2 * m1 ^ 3

/-- Fourth cumulant from raw moments. -/
def cumulant4 (m1 m2 m3 m4 : ℚ) : ℚ :=
  m4 - 4 * m3 * m1 - 3 * m2 ^ 2 + 12 * m2 * m1 ^ 2 - 6 * m1 ^ 4

/-- Fifth cumulant from raw moments. -/
def cumulant5 (m1 m2 m3 m4 m5 : ℚ) : ℚ :=
  m5 - 5 * m4 * m1 - 10 * m3 * m2 + 20 * m3 * m1 ^ 2 +
    30 * m2 ^ 2 * m1 - 60 * m2 * m1 ^ 3 + 24 * m1 ^ 5

/-- Sixth cumulant from raw moments. -/
def cumulant6 (m1 m2 m3 m4 m5 m6 : ℚ) : ℚ :=
  m6 - 6 * m5 * m1 - 15 * m4 * m2 - 10 * m3 ^ 2 +
    30 * m4 * m1 ^ 2 + 120 * m3 * m2 * m1 - 120 * m3 * m1 ^ 3 +
    30 * m2 ^ 3 - 270 * m2 ^ 2 * m1 ^ 2 + 360 * m2 * m1 ^ 4 -
    120 * m1 ^ 6

/-- Cumulants `κ₁..κ₆` computed from raw moments `m₁..m₆`. -/
def cumulantsFromMoments6 (m : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![cumulant1 (m 0),
    cumulant2 (m 0) (m 1),
    cumulant3 (m 0) (m 1) (m 2),
    cumulant4 (m 0) (m 1) (m 2) (m 3),
    cumulant5 (m 0) (m 1) (m 2) (m 3) (m 4),
    cumulant6 (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)]

/-- Raw moments `m₁..m₆` computed from cumulants `κ₁..κ₆`. -/
def momentsFromCumulants6 (k : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![k 0,
    k 1 + (k 0) ^ 2,
    k 2 + 3 * (k 1) * (k 0) + (k 0) ^ 3,
    k 3 + 4 * (k 2) * (k 0) + 3 * (k 1) ^ 2 +
      6 * (k 1) * (k 0) ^ 2 + (k 0) ^ 4,
    k 4 + 5 * (k 3) * (k 0) + 10 * (k 2) * (k 1) +
      10 * (k 2) * (k 0) ^ 2 + 15 * (k 1) ^ 2 * (k 0) +
      10 * (k 1) * (k 0) ^ 3 + (k 0) ^ 5,
    k 5 + 6 * (k 4) * (k 0) + 15 * (k 3) * (k 1) +
      15 * (k 3) * (k 0) ^ 2 + 10 * (k 2) ^ 2 +
      60 * (k 2) * (k 1) * (k 0) + 20 * (k 2) * (k 0) ^ 3 +
      15 * (k 1) ^ 3 + 45 * (k 1) ^ 2 * (k 0) ^ 2 +
      15 * (k 1) * (k 0) ^ 4 + (k 0) ^ 6]

/-! ## Bell and Faà di Bruno coefficient tables -/

/-- Numbers of set partitions, `B₁..B₆`. -/
def bellNumberTable : Fin 6 → ℕ :=
  ![1, 2, 5, 15, 52, 203]

/-- Coefficients in the complete Bell polynomial `B₅`. -/
def faaDiBrunoB5Coefficients : Fin 7 → ℕ :=
  ![1, 5, 10, 10, 15, 10, 1]

/-- Coefficients in the complete Bell polynomial `B₆`. -/
def faaDiBrunoB6Coefficients : Fin 11 → ℕ :=
  ![1, 6, 15, 15, 10, 60, 20, 15, 45, 15, 1]

/-- Faà di Bruno coefficients for `B₅` add up to the Bell number `B₅ = 52`. -/
theorem faaDiBrunoB5_coefficients_sum :
    (∑ i : Fin 7, faaDiBrunoB5Coefficients i) = bellNumberTable 4 := by
  native_decide

/-- Faà di Bruno coefficients for `B₆` add up to the Bell number `B₆ = 203`. -/
theorem faaDiBrunoB6_coefficients_sum :
    (∑ i : Fin 11, faaDiBrunoB6Coefficients i) = bellNumberTable 5 := by
  native_decide

/-! ## Distribution tables -/

/-- Raw moments `m₁..m₆` of a Poisson law with parameter `2`. -/
def poisson2MomentTable : Fin 6 → ℕ :=
  ![2, 6, 22, 94, 454, 2430]

/-- Cumulants `κ₁..κ₆` of a Poisson law with parameter `2`. -/
def poisson2CumulantTable : Fin 6 → ℕ :=
  ![2, 2, 2, 2, 2, 2]

/-- Rational view of the Poisson moment table. -/
def poisson2Moments : Fin 6 → ℚ :=
  fun i => poisson2MomentTable i

/-- Rational view of the Poisson cumulant table. -/
def poisson2Cumulants : Fin 6 → ℚ :=
  fun i => poisson2CumulantTable i

/-- Poisson cumulants are all equal to `λ`; here `λ = 2` through order six. -/
theorem poisson2_cumulants_from_moments :
    ∀ i : Fin 6, cumulantsFromMoments6 poisson2Moments i = poisson2Cumulants i := by
  native_decide

/-- Complete Bell polynomials recover the Poisson raw moments from the cumulants. -/
theorem poisson2_moments_from_cumulants :
    ∀ i : Fin 6, momentsFromCumulants6 poisson2Cumulants i = poisson2Moments i := by
  native_decide

/-- Raw moments `m₁..m₆` of `Bin(4, 1/2)`. -/
def binomial4HalfMomentTable : Fin 6 → ℚ :=
  ![(2 : ℚ), 5, 14, (85 : ℚ) / 2, 137, (925 : ℚ) / 2]

/-- Cumulants `κ₁..κ₆` of `Bin(4, 1/2)`. -/
def binomial4HalfCumulantTable : Fin 6 → ℚ :=
  ![(2 : ℚ), 1, 0, (-1 : ℚ) / 2, 0, 1]

/-- Moment-cumulant conversion for `Bin(4,1/2)` through order six. -/
theorem binomial4Half_cumulants_from_moments :
    ∀ i : Fin 6,
      cumulantsFromMoments6 binomial4HalfMomentTable i = binomial4HalfCumulantTable i := by
  native_decide

/-- Bell-polynomial conversion recovers `Bin(4,1/2)` moments from cumulants. -/
theorem binomial4Half_moments_from_cumulants :
    ∀ i : Fin 6,
      momentsFromCumulants6 binomial4HalfCumulantTable i = binomial4HalfMomentTable i := by
  native_decide

/-! ## Partition-based cumulant coefficients -/

/-- Coefficients in the partition formula for `κ₂`. -/
def cumulant2PartitionCoefficients : Fin 2 → ℤ :=
  ![1, -1]

/-- Coefficients in the partition formula for `κ₃`. -/
def cumulant3PartitionCoefficients : Fin 3 → ℤ :=
  ![1, -3, 2]

/-- Coefficients in the partition formula for `κ₄`. -/
def cumulant4PartitionCoefficients : Fin 5 → ℤ :=
  ![1, -4, -3, 12, -6]

/-- Coefficients in the partition formula for `κ₅`. -/
def cumulant5PartitionCoefficients : Fin 7 → ℤ :=
  ![1, -5, -10, 20, 30, -60, 24]

/-- Coefficients in the partition formula for `κ₆`. -/
def cumulant6PartitionCoefficients : Fin 11 → ℤ :=
  ![1, -6, -15, -10, 30, 120, -120, 30, -270, 360, -120]

/-- For a deterministic unit variable, all higher cumulants vanish. -/
theorem partition_cumulant_coefficients_sum_to_zero :
    (∑ i : Fin 2, cumulant2PartitionCoefficients i) = 0 ∧
      (∑ i : Fin 3, cumulant3PartitionCoefficients i) = 0 ∧
      (∑ i : Fin 5, cumulant4PartitionCoefficients i) = 0 ∧
      (∑ i : Fin 7, cumulant5PartitionCoefficients i) = 0 ∧
      (∑ i : Fin 11, cumulant6PartitionCoefficients i) = 0 := by
  native_decide

/-! ## Semi-invariants under translation -/

/-- Raw moments of `X + c` from raw moments of `X`, through order six. -/
def translatedMoments6 (m : Fin 6 → ℚ) (c : ℚ) : Fin 6 → ℚ :=
  ![m 0 + c,
    m 1 + 2 * c * (m 0) + c ^ 2,
    m 2 + 3 * c * (m 1) + 3 * c ^ 2 * (m 0) + c ^ 3,
    m 3 + 4 * c * (m 2) + 6 * c ^ 2 * (m 1) + 4 * c ^ 3 * (m 0) + c ^ 4,
    m 4 + 5 * c * (m 3) + 10 * c ^ 2 * (m 2) + 10 * c ^ 3 * (m 1) +
      5 * c ^ 4 * (m 0) + c ^ 5,
    m 5 + 6 * c * (m 4) + 15 * c ^ 2 * (m 3) + 20 * c ^ 3 * (m 2) +
      15 * c ^ 4 * (m 1) + 6 * c ^ 5 * (m 0) + c ^ 6]

/-- Cumulants of `X + 3` for Poisson `X` with parameter `2`. -/
def poisson2Shift3CumulantTable : Fin 6 → ℚ :=
  ![(5 : ℚ), 2, 2, 2, 2, 2]

/-- Cumulants are semi-invariants: translation changes only the first one. -/
theorem poisson2_translation_semiinvariants :
    ∀ i : Fin 6,
      cumulantsFromMoments6 (translatedMoments6 poisson2Moments 3) i =
        poisson2Shift3CumulantTable i := by
  native_decide

end CumulantMethods
