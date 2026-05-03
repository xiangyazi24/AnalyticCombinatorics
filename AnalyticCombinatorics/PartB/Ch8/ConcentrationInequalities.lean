import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ConcentrationInequalities

open Finset Nat

/-!
  Chapter VIII concentration-inequality templates.

  Probabilities are represented by integer-scaled masses.  For the symmetric
  binomial law `Bin(n, 1/2)`, the common denominator is `2^n`; inequalities are
  cross-multiplied so that all certificates are exact finite arithmetic.
-/

/-! ## Finite probability tables -/

/-- Total scaled mass on `{0, ..., N}`. -/
def totalMass (N : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x

/-- Scaled tail mass for the event `X >= t`. -/
def tailMass (N t : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), if t ≤ x then w x else 0

/-- Scaled lower-tail mass for the event `X <= t`. -/
def lowerMass (N t : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), if x ≤ t then w x else 0

/-- Scaled mass of the point event `X = t`. -/
def pointMass (N t : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), if x = t then w x else 0

/-- Scaled first raw moment. -/
def firstMomentMass (N : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x * x

/-- Scaled second raw moment. -/
def secondMomentMass (N : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x * x ^ 2

/-- Distance from `x` to the center `centerTwice / 2`, scaled by `2`. -/
def twiceDistanceFrom (centerTwice x : ℕ) : ℕ :=
  if centerTwice ≤ 2 * x then 2 * x - centerTwice else centerTwice - 2 * x

/-- Scaled second centered moment for the variable `2X - centerTwice`. -/
def centeredSecondMomentTwice (N centerTwice : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1), w x * twiceDistanceFrom centerTwice x ^ 2

/-- Scaled mass of `|2X - centerTwice| >= thresholdTwice`. -/
def deviationMassTwice (N centerTwice thresholdTwice : ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (N + 1),
    if thresholdTwice ≤ twiceDistanceFrom centerTwice x then w x else 0

/-- Scaled mass table for `Bin(n, 1/2)`. -/
def binomialHalfMass (n : ℕ) : ℕ → ℕ :=
  fun k => if k ≤ n then Nat.choose n k else 0

/-- Scaled tail count for `Bin(n, 1/2)`: denominator `2^n`. -/
def binomialHalfTail (n k : ℕ) : ℕ :=
  tailMass n k (binomialHalfMass n)

/-- Scaled lower-tail count for `Bin(n, 1/2)`: denominator `2^n`. -/
def binomialHalfLower (n k : ℕ) : ℕ :=
  lowerMass n k (binomialHalfMass n)

/-- Scaled point count for `Bin(n, 1/2)`: denominator `2^n`. -/
def binomialHalfPoint (n k : ℕ) : ℕ :=
  pointMass n k (binomialHalfMass n)

/-! ## 1. Markov inequality -/

/--
Integer-scaled Markov form:
`P(X >= t) <= E[X] / t` becomes
`tailMass * t <= firstMomentMass`.
-/
abbrev markovKernel (N t : ℕ) (w : ℕ → ℕ) : Prop :=
  tailMass N t w * t ≤ firstMomentMass N w

structure MarkovCertificate where
  supportMax : ℕ
  threshold : ℕ
  weights : ℕ → ℕ
  markovBound : markovKernel supportMax threshold weights

def markovBinomialTenAtEight : MarkovCertificate where
  supportMax := 10
  threshold := 8
  weights := binomialHalfMass 10
  markovBound := by native_decide

/-- For `X = sum_{i=1}^n Bernoulli(1/2)`, `E[X] = n/2`, scaled by `2^n`. -/
theorem binomialHalf_mean_scaled :
    ∀ n : Fin 21,
      2 * firstMomentMass n.val (binomialHalfMass n.val) = n.val * 2 ^ n.val := by
  native_decide

theorem markov_binomial_tail_samples :
    markovKernel 10 8 (binomialHalfMass 10) ∧
      markovKernel 12 9 (binomialHalfMass 12) ∧
      markovKernel 16 12 (binomialHalfMass 16) := by
  native_decide

/-! ## 2. Chebyshev inequality -/

/--
Integer-scaled Chebyshev form for a doubled center:
`P(|X - mu| >= t) <= Var(X) / t^2`.

Here `centerTwice = 2 * mu` and `thresholdTwice = 2 * t`, so the checked
kernel is `P(|2X-centerTwice| >= thresholdTwice) <=
E[(2X-centerTwice)^2] / thresholdTwice^2`.
-/
abbrev chebyshevKernelTwice
    (N centerTwice thresholdTwice : ℕ) (w : ℕ → ℕ) : Prop :=
  deviationMassTwice N centerTwice thresholdTwice w * thresholdTwice ^ 2 ≤
    centeredSecondMomentTwice N centerTwice w

structure ChebyshevCertificate where
  supportMax : ℕ
  centerTwice : ℕ
  thresholdTwice : ℕ
  weights : ℕ → ℕ
  chebyshevBound : chebyshevKernelTwice supportMax centerTwice thresholdTwice weights

def chebyshevBinomialTenDistanceThree : ChebyshevCertificate where
  supportMax := 10
  centerTwice := 10
  thresholdTwice := 6
  weights := binomialHalfMass 10
  chebyshevBound := by native_decide

/-- For `X ~ Bin(n, 1/2)`, `E[(2X-n)^2] = n`; equivalently `4 * Var(X) = n`. -/
theorem binomialHalf_variance_scaled :
    ∀ n : Fin 21,
      centeredSecondMomentTwice n.val n.val (binomialHalfMass n.val) =
        n.val * 2 ^ n.val := by
  native_decide

theorem chebyshev_binomial_tail_samples :
    chebyshevKernelTwice 10 10 6 (binomialHalfMass 10) ∧
      chebyshevKernelTwice 12 12 8 (binomialHalfMass 12) ∧
      chebyshevKernelTwice 16 16 10 (binomialHalfMass 16) := by
  native_decide

/-! ## 3. Binomial coefficient tail numerics -/

/--
Boundary coefficient used in binomial tail estimates.  The point probability is
`C(n,k) / 2^n`; upper tails are separately represented by `binomialHalfTail`.
-/
structure BinomialCoefficientCertificate where
  n : ℕ
  k : ℕ
  numerator : ℕ
  denominator : ℕ
  coefficientValue : numerator = Nat.choose n k
  denominatorValue : denominator = 2 ^ n

def binomialCoefficientTenEight : BinomialCoefficientCertificate where
  n := 10
  k := 8
  numerator := 45
  denominator := 1024
  coefficientValue := by native_decide
  denominatorValue := by native_decide

theorem binomial_point_10_8_bound :
    Nat.choose 10 8 = 45 ∧
      2 ^ 10 = 1024 ∧
      45 * 20 < 1024 := by
  native_decide

/-- A monotone-tail count bound using the boundary coefficient and tail length. -/
abbrev binomialTailByBoundaryTerm (n k : ℕ) : Prop :=
  binomialHalfTail n k ≤ (n + 1 - k) * Nat.choose n k

theorem binomial_tail_boundary_term_samples :
    binomialTailByBoundaryTerm 10 8 ∧
      binomialTailByBoundaryTerm 12 9 ∧
      binomialTailByBoundaryTerm 16 12 := by
  native_decide

/-! ## 4. Hoeffding-type bounds -/

/--
Hoeffding shape for `n` coin flips:
`P(S_n >= n/2 + t) <= exp(-2t^2/n)`.

The exponential term is stored symbolically by the pair
`(exponentNumerator, exponentDenominator) = (2t^2, n)`.
-/
structure HoeffdingTypeCertificate where
  n : ℕ
  t : ℕ
  threshold : ℕ
  tailNumerator : ℕ
  denominator : ℕ
  exponentNumerator : ℕ
  exponentDenominator : ℕ
  thresholdValue : 2 * threshold = n + 2 * t
  tailValue : tailNumerator = binomialHalfTail n threshold
  denominatorValue : denominator = 2 ^ n
  exponentValue : exponentNumerator * exponentDenominator = 2 * t ^ 2 * n

def hoeffdingTenThree : HoeffdingTypeCertificate where
  n := 10
  t := 3
  threshold := 8
  tailNumerator := 56
  denominator := 1024
  exponentNumerator := 18
  exponentDenominator := 10
  thresholdValue := by native_decide
  tailValue := by native_decide
  denominatorValue := by native_decide
  exponentValue := by native_decide

theorem binomial_tail_10_8_exact :
    binomialHalfTail 10 8 =
      Nat.choose 10 8 + Nat.choose 10 9 + Nat.choose 10 10 ∧
      Nat.choose 10 8 + Nat.choose 10 9 + Nat.choose 10 10 = 56 := by
  native_decide

theorem hoeffding_integer_tail_10_8 :
    2 ^ 10 * binomialHalfTail 10 8 = 2 ^ 10 * 56 ∧
      binomialHalfTail 10 8 = 56 := by
  native_decide

/-! ## 5. Anti-concentration at the center -/

/-- Central binomial mass for `Bin(2k, 1/2)`: `C(2k,k) / 4^k`. -/
def centralBinomialMassNumerator (k : ℕ) : ℕ :=
  Nat.choose (2 * k) k

/-- Denominator for the central mass `P(Bin(2k,1/2)=k)`. -/
def centralBinomialMassDenominator (k : ℕ) : ℕ :=
  4 ^ k

structure AntiConcentrationCertificate where
  k : ℕ
  numerator : ℕ
  denominator : ℕ
  numeratorValue : numerator = centralBinomialMassNumerator k
  denominatorValue : denominator = centralBinomialMassDenominator k

def antiConcentrationKFive : AntiConcentrationCertificate where
  k := 5
  numerator := 252
  denominator := 1024
  numeratorValue := by native_decide
  denominatorValue := by native_decide

theorem central_binomial_mass_formula_samples :
    centralBinomialMassNumerator 1 = 2 ∧
      centralBinomialMassDenominator 1 = 4 ∧
      centralBinomialMassNumerator 5 = 252 ∧
      centralBinomialMassDenominator 5 = 1024 ∧
      centralBinomialMassNumerator 8 = 12870 ∧
      centralBinomialMassDenominator 8 = 65536 := by
  native_decide

/--
Finite square-window checks for the `1 / sqrt(n)` scale:
for `n = 2k`, the value `n * P(Bin(n,1/2)=n/2)^2` stays between `1/2` and `1`
in these samples.
-/
theorem central_binomial_mass_sqrt_scale_samples :
    ∀ k : Fin 9,
      1 ≤ k.val →
        let n := 2 * k.val
        let c := centralBinomialMassNumerator k.val
        let d := centralBinomialMassDenominator k.val
        d ^ 2 ≤ 2 * n * c ^ 2 ∧ n * c ^ 2 ≤ d ^ 2 := by
  native_decide

/-! ## 6. Median versus mean for symmetric distributions -/

/-- Symmetry on `{0, ..., N}` around the center `N/2`. -/
abbrev symmetricOnSupport (N : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ x : Fin (N + 1), w x.val = w (N - x.val)

/-- Integer-count median certificate: both closed half-lines have mass at least `1/2`. -/
abbrev medianByCounts (N median : ℕ) (w : ℕ → ℕ) : Prop :=
  2 * lowerMass N median w ≥ totalMass N w ∧
    2 * tailMass N median w ≥ totalMass N w

structure SymmetricMedianMeanCertificate where
  supportMax : ℕ
  center : ℕ
  weights : ℕ → ℕ
  symmetric : symmetricOnSupport supportMax weights
  median : medianByCounts supportMax center weights
  meanTwice : 2 * firstMomentMass supportMax weights =
    supportMax * totalMass supportMax weights

def symmetricBinomialTenMedianMean : SymmetricMedianMeanCertificate where
  supportMax := 10
  center := 5
  weights := binomialHalfMass 10
  symmetric := by native_decide
  median := by native_decide
  meanTwice := by native_decide

theorem binomialHalf_symmetric_small :
    ∀ n : Fin 21, symmetricOnSupport n.val (binomialHalfMass n.val) := by
  native_decide

theorem symmetric_binomial_even_median_equals_mean :
    ∀ k : Fin 11,
      let n := 2 * k.val
      medianByCounts n k.val (binomialHalfMass n) ∧
        2 * firstMomentMass n (binomialHalfMass n) =
          n * totalMass n (binomialHalfMass n) := by
  native_decide

end ConcentrationInequalities
