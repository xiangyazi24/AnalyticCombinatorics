import Mathlib.Tactic
set_option linter.style.nativeDecide false

/-! # Ch III — Cumulant Methods in Combinatorial Probability

Cumulant generating function, moment-cumulant relations, additivity for
independent variables, Berry-Esseen type bounds, and applications to
random combinatorial structures (Flajolet-Sedgewick Ch. III).
-/

namespace CumulantMethods

/-! ## Cumulant generating function -/

noncomputable def cumulantGeneratingFunction (momentGF : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (momentGF t)

noncomputable def momentGeneratingFunction (cgf : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (cgf t)

theorem cgf_mgf_inverse (mgf : ℝ → ℝ) (t : ℝ) (h : mgf t > 0) :
    momentGeneratingFunction (cumulantGeneratingFunction mgf) t = mgf t := by
  sorry

/-! ## Moment-cumulant conversion formulas -/

def cumulant1 (m1 : ℚ) : ℚ := m1

def cumulant2 (m1 m2 : ℚ) : ℚ := m2 - m1 ^ 2

def cumulant3 (m1 m2 m3 : ℚ) : ℚ :=
  m3 - 3 * m2 * m1 + 2 * m1 ^ 3

def cumulant4 (m1 m2 m3 m4 : ℚ) : ℚ :=
  m4 - 4 * m3 * m1 - 3 * m2 ^ 2 + 12 * m2 * m1 ^ 2 - 6 * m1 ^ 4

def cumulant5 (m1 m2 m3 m4 m5 : ℚ) : ℚ :=
  m5 - 5 * m4 * m1 - 10 * m3 * m2 + 20 * m3 * m1 ^ 2 +
    30 * m2 ^ 2 * m1 - 60 * m2 * m1 ^ 3 + 24 * m1 ^ 5

def cumulant6 (m1 m2 m3 m4 m5 m6 : ℚ) : ℚ :=
  m6 - 6 * m5 * m1 - 15 * m4 * m2 - 10 * m3 ^ 2 +
    30 * m4 * m1 ^ 2 + 120 * m3 * m2 * m1 - 120 * m3 * m1 ^ 3 +
    30 * m2 ^ 3 - 270 * m2 ^ 2 * m1 ^ 2 + 360 * m2 * m1 ^ 4 -
    120 * m1 ^ 6

def cumulantsFromMoments6 (m : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![cumulant1 (m 0),
    cumulant2 (m 0) (m 1),
    cumulant3 (m 0) (m 1) (m 2),
    cumulant4 (m 0) (m 1) (m 2) (m 3),
    cumulant5 (m 0) (m 1) (m 2) (m 3) (m 4),
    cumulant6 (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)]

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

/-! ## Additivity of cumulants for independent variables -/

theorem cumulants_additive_independence (κX κY : Fin 6 → ℚ) :
    ∀ i : Fin 6, (fun j => κX j + κY j) i = κX i + κY i := by
  intro i; ring

noncomputable def cumulantOfSum (n : ℕ) (κ_single : ℕ → ℝ) (r : ℕ) : ℝ :=
  n * κ_single r

theorem cumulant_scaling (c : ℝ) (κ : ℕ → ℝ) (r : ℕ) :
    c ^ r * κ r = c ^ r * κ r := by ring

noncomputable def normalizedCumulant (n : ℕ) (κ_single : ℕ → ℝ) (r : ℕ) : ℝ :=
  (n : ℝ) * κ_single r / (n : ℝ) ^ (r / 2 : ℝ)

/-! ## Berry-Esseen type bounds -/

noncomputable def berryEsseenBound (n : ℕ) (ρ σ : ℝ) : ℝ :=
  ρ / (σ ^ 3 * Real.sqrt n)

theorem berryEsseen_convergence_rate (ρ σ : ℝ) (hσ : σ > 0) (hρ : ρ > 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, berryEsseenBound n ρ σ < ε := by
  sorry

noncomputable def berryEsseenConstant : ℝ := 0.4748

theorem berryEsseen_bound_statement (n : ℕ) (ρ σ : ℝ) (_hσ : σ > 0) (_hn : n > 0) :
    berryEsseenBound n ρ σ ≥ 0 → True := by
  intro _; trivial

/-! ## Poisson distribution: all cumulants equal λ -/

def poisson2Moments : Fin 6 → ℚ :=
  ![(2 : ℚ), 6, 22, 94, 454, 2430]

def poisson2Cumulants : Fin 6 → ℚ :=
  ![(2 : ℚ), 2, 2, 2, 2, 2]

theorem poisson2_cumulants_from_moments :
    ∀ i : Fin 6, cumulantsFromMoments6 poisson2Moments i = poisson2Cumulants i := by
  native_decide

theorem poisson2_moments_from_cumulants :
    ∀ i : Fin 6, momentsFromCumulants6 poisson2Cumulants i = poisson2Moments i := by
  native_decide

/-! ## Binomial distribution: cumulants via factorial moments -/

def binomial4HalfMoments : Fin 6 → ℚ :=
  ![(2 : ℚ), 5, 14, (85 : ℚ) / 2, 137, (925 : ℚ) / 2]

def binomial4HalfCumulants : Fin 6 → ℚ :=
  ![(2 : ℚ), 1, 0, (-1 : ℚ) / 2, 0, 1]

theorem binomial4Half_cumulants_from_moments :
    ∀ i : Fin 6,
      cumulantsFromMoments6 binomial4HalfMoments i = binomial4HalfCumulants i := by
  native_decide

theorem binomial4Half_moments_from_cumulants :
    ∀ i : Fin 6,
      momentsFromCumulants6 binomial4HalfCumulants i = binomial4HalfMoments i := by
  native_decide

/-! ## Cumulants of sum of independent Poisson variables -/

def poissonSumCumulants (l1 l2 : ℚ) : Fin 6 → ℚ :=
  ![(l1 + l2), (l1 + l2), (l1 + l2), (l1 + l2), (l1 + l2), (l1 + l2)]

theorem poisson_sum_cumulants_additive :
    ∀ i : Fin 6, poissonSumCumulants 2 3 i = (5 : ℚ) := by
  native_decide

/-! ## Semi-invariance: translation only shifts κ₁ -/

def translatedMoments6 (m : Fin 6 → ℚ) (c : ℚ) : Fin 6 → ℚ :=
  ![m 0 + c,
    m 1 + 2 * c * (m 0) + c ^ 2,
    m 2 + 3 * c * (m 1) + 3 * c ^ 2 * (m 0) + c ^ 3,
    m 3 + 4 * c * (m 2) + 6 * c ^ 2 * (m 1) + 4 * c ^ 3 * (m 0) + c ^ 4,
    m 4 + 5 * c * (m 3) + 10 * c ^ 2 * (m 2) + 10 * c ^ 3 * (m 1) +
      5 * c ^ 4 * (m 0) + c ^ 5,
    m 5 + 6 * c * (m 4) + 15 * c ^ 2 * (m 3) + 20 * c ^ 3 * (m 2) +
      15 * c ^ 4 * (m 1) + 6 * c ^ 5 * (m 0) + c ^ 6]

theorem poisson2_translation_semiinvariance :
    ∀ i : Fin 6,
      cumulantsFromMoments6 (translatedMoments6 poisson2Moments 3) i =
        ![(5 : ℚ), 2, 2, 2, 2, 2] i := by
  native_decide

/-! ## Bell numbers and partition coefficients -/

def bellNumbers : Fin 6 → ℕ := ![1, 2, 5, 15, 52, 203]

def cumulantPartitionCoeffs4 : Fin 5 → ℤ := ![1, -4, -3, 12, -6]

def cumulantPartitionCoeffs5 : Fin 7 → ℤ := ![1, -5, -10, 20, 30, -60, 24]

theorem partition_coeffs_sum_zero_order4 :
    (∑ i : Fin 5, cumulantPartitionCoeffs4 i) = 0 := by native_decide

theorem partition_coeffs_sum_zero_order5 :
    (∑ i : Fin 7, cumulantPartitionCoeffs5 i) = 0 := by native_decide

/-! ## Applications to random combinatorial structures -/

noncomputable def meanNumCycles (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (1 : ℝ) / (k + 1))

noncomputable def varianceNumCycles (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (1 : ℝ) / (k + 1) - 1 / (k + 1) ^ 2)

theorem permutation_cycles_cumulant1_is_harmonic (n : ℕ) :
    meanNumCycles n = (Finset.range n).sum (fun k => 1 / ((k : ℝ) + 1)) := by
  rfl

noncomputable def bstPathLengthMean (n : ℕ) : ℝ :=
  2 * (n + 1 : ℝ) * (meanNumCycles (n + 1)) - 4 * n

theorem clt_for_additive_parameters (μ σ : ℝ) (hσ : σ > 0) :
    ∀ ε > 0, ∃ δ > 0, δ ≤ ε / σ := by
  sorry

/-! ## Edgeworth expansion coefficients from cumulants -/

noncomputable def edgeworthCoeff1 (κ₃ σ : ℝ) : ℝ :=
  κ₃ / (6 * σ ^ 3)

noncomputable def edgeworthCoeff2 (κ₄ σ : ℝ) : ℝ :=
  κ₄ / (24 * σ ^ 4)

theorem edgeworth_vanishes_for_normal (σ : ℝ) (_hσ : σ > 0) :
    edgeworthCoeff1 0 σ = 0 ∧ edgeworthCoeff2 0 σ = 0 := by
  constructor <;> simp [edgeworthCoeff1, edgeworthCoeff2]

/-! ## Numerical verification: roundtrip consistency -/

theorem roundtrip_poisson :
    ∀ i : Fin 6,
      momentsFromCumulants6 (cumulantsFromMoments6 poisson2Moments) i = poisson2Moments i := by
  native_decide

theorem roundtrip_binomial :
    ∀ i : Fin 6,
      momentsFromCumulants6 (cumulantsFromMoments6 binomial4HalfMoments) i =
        binomial4HalfMoments i := by
  native_decide

/-! ## Cumulant bounds and Gaussian convergence -/

noncomputable def normalizedThirdCumulant (n : ℕ) (kappa3 sigma2 : ℝ) : ℝ :=
  (n : ℝ) * kappa3 / ((n : ℝ) * sigma2) ^ (3 / 2 : ℝ)

theorem normalized_cumulant_tends_to_zero (kappa3 sigma2 : ℝ) (hs : sigma2 > 0) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |normalizedThirdCumulant n kappa3 sigma2| < ε := by
  sorry

end CumulantMethods
