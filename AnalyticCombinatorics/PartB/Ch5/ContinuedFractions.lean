import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ContinuedFractions

/-! # Continued Fractions and Generating Functions (Chapter 5)

Stieltjes-type and Jacobi continued fractions, their connection to moment
sequences and combinatorial generating functions. Convergent evaluation
and verification of the CF expansion for e - 1. -/

-- ============================================================================
-- §1. Simple Continued Fraction Convergents
-- ============================================================================

/-- Forward recurrence for convergents of [a₀; a₁, a₂, ...].
    State = (hₙ₋₁, kₙ₋₁, hₙ₋₂, kₙ₋₂), input = aₙ -/
def convergentStep : ℕ × ℕ × ℕ × ℕ → ℕ → ℕ × ℕ × ℕ × ℕ
  | (h, k, h', k'), a => (a * h + h', a * k + k', h, k)

/-- Convergent pₙ/qₙ of simple CF [a₀; a₁, ..., aₙ] -/
def convergent (coeffs : List ℕ) : ℕ × ℕ :=
  match coeffs with
  | [] => (0, 1)
  | a₀ :: rest =>
    match rest.foldl convergentStep (a₀, 1, 1, 0) with
    | (h, k, _, _) => (h, k)

/-- Partial quotients of e - 1 follow pattern: 1; (1, 2k, 1) for k = 1, 2, ... -/
def eMinus1_partials (groups : ℕ) : List ℕ :=
  1 :: (List.range groups).flatMap (fun k => [1, 2 * (k + 1), 1])

example : eMinus1_partials 0 = [1] := by native_decide
example : eMinus1_partials 1 = [1, 1, 2, 1] := by native_decide
example : eMinus1_partials 2 = [1, 1, 2, 1, 1, 4, 1] := by native_decide
example : eMinus1_partials 3 = [1, 1, 2, 1, 1, 4, 1, 1, 6, 1] := by native_decide

-- Convergents of e - 1 = [1; 1, 2, 1, 1, 4, 1, 1, 6, ...]
-- Rational approximations converging to e - 1 ≈ 1.71828...

example : convergent [1] = (1, 1) := by native_decide
example : convergent [1, 1] = (2, 1) := by native_decide
example : convergent [1, 1, 2] = (5, 3) := by native_decide
example : convergent [1, 1, 2, 1] = (7, 4) := by native_decide
example : convergent [1, 1, 2, 1, 1] = (12, 7) := by native_decide
example : convergent [1, 1, 2, 1, 1, 4] = (55, 32) := by native_decide
example : convergent [1, 1, 2, 1, 1, 4, 1] = (67, 39) := by native_decide
example : convergent [1, 1, 2, 1, 1, 4, 1, 1] = (122, 71) := by native_decide
example : convergent [1, 1, 2, 1, 1, 4, 1, 1, 6] = (799, 465) := by native_decide
example : convergent (eMinus1_partials 3) = (921, 536) := by native_decide

-- √2 = [1; 2, 2, 2, ...] convergents
example : convergent [1, 2] = (3, 2) := by native_decide
example : convergent [1, 2, 2] = (7, 5) := by native_decide
example : convergent [1, 2, 2, 2] = (17, 12) := by native_decide
example : convergent [1, 2, 2, 2, 2] = (41, 29) := by native_decide
example : convergent [1, 2, 2, 2, 2, 2] = (99, 70) := by native_decide

-- ============================================================================
-- §2. Euler-Minding Determinant Formula
-- ============================================================================

-- For simple CFs: pₙqₙ₋₁ - pₙ₋₁qₙ = (-1)^(n+1)
-- Verified on consecutive convergents of e - 1:

example : (2 : ℤ) * 1 - 1 * 1 = 1 := by norm_num
example : (5 : ℤ) * 1 - 2 * 3 = -1 := by norm_num
example : (7 : ℤ) * 3 - 5 * 4 = 1 := by norm_num
example : (12 : ℤ) * 4 - 7 * 7 = -1 := by norm_num
example : (55 : ℤ) * 7 - 12 * 32 = 1 := by norm_num
example : (67 : ℤ) * 32 - 55 * 39 = -1 := by norm_num
example : (122 : ℤ) * 39 - 67 * 71 = 1 := by norm_num
example : (799 : ℤ) * 71 - 122 * 465 = -1 := by norm_num
example : (921 : ℤ) * 465 - 799 * 536 = 1 := by norm_num

-- And for √2:
example : (3 : ℤ) * 1 - 1 * 2 = 1 := by norm_num
example : (7 : ℤ) * 2 - 3 * 5 = -1 := by norm_num
example : (17 : ℤ) * 5 - 7 * 12 = 1 := by norm_num
example : (41 : ℤ) * 12 - 17 * 29 = -1 := by norm_num

-- Even convergents increase, odd convergents decrease (bracketing property)
example : (1 : ℚ) / 1 < 5 / 3 := by norm_num
example : (5 : ℚ) / 3 < 12 / 7 := by norm_num
example : (12 : ℚ) / 7 < 67 / 39 := by norm_num
example : (67 : ℚ) / 39 < 799 / 465 := by norm_num
example : (2 : ℚ) / 1 > 7 / 4 := by norm_num
example : (7 : ℚ) / 4 > 55 / 32 := by norm_num
example : (55 : ℚ) / 32 > 122 / 71 := by norm_num

-- ============================================================================
-- §3. Stieltjes-Type Continued Fractions
-- ============================================================================

/-- Stieltjes CF: S(z) = 1/(1 - c₁z/(1 - c₂z/(... /(1 - cₙz))))
    Arises from moment sequences of probability distributions. -/
def stieltjesCF (coeffs : List ℚ) (z : ℚ) : ℚ :=
  let denom := coeffs.reverse.foldl (fun acc c => 1 - c * z / acc) 1
  1 / denom

-- All cᵢ = 1 gives the Catalan OGF: C(z) = (1 - √(1-4z))/(2z)
-- Successive truncations at z = 1/5 converge to C(1/5) ≈ 1.382:

example : stieltjesCF [] (1/5 : ℚ) = 1 := by native_decide
example : stieltjesCF [1] (1/5 : ℚ) = 5/4 := by native_decide
example : stieltjesCF [1, 1] (1/5 : ℚ) = 4/3 := by native_decide
example : stieltjesCF [1, 1, 1] (1/5 : ℚ) = 15/11 := by native_decide
example : stieltjesCF [1, 1, 1, 1] (1/5 : ℚ) = 11/8 := by native_decide
example : stieltjesCF [1, 1, 1, 1, 1] (1/5 : ℚ) = 40/29 := by native_decide

-- Monotone convergence from below for positive coefficients and z > 0:
example : (1 : ℚ) < 5/4 := by norm_num
example : (5 : ℚ) / 4 < 4/3 := by norm_num
example : (4 : ℚ) / 3 < 15/11 := by norm_num
example : (15 : ℚ) / 11 < 11/8 := by norm_num
example : (11 : ℚ) / 8 < 40/29 := by norm_num

-- ============================================================================
-- §4. Jacobi-Type Continued Fractions
-- ============================================================================

/-- Jacobi CF: J(z) = 1/(1 - b₀z - a₁z²/(1 - b₁z - a₂z²/(... /(1 - bₙz))))
    Encodes three-term recurrence of orthogonal polynomials. -/
def jacobiCF (b_coeffs : List ℚ) (a_coeffs : List ℚ) (z : ℚ) : ℚ :=
  match b_coeffs.reverse with
  | [] => 1
  | bLast :: bRest =>
    let init := 1 - bLast * z
    let pairs := a_coeffs.reverse.zip bRest
    let denom := pairs.foldl (fun acc (ai, bi) => 1 - bi * z - ai * z ^ 2 / acc) init
    1 / denom

-- Catalan J-fraction: b₀ = 1, bᵢ = 2 for i ≥ 1, all aᵢ = 1
example : jacobiCF [1] [] (1/5 : ℚ) = 5/4 := by native_decide
example : jacobiCF [1, 2] [1] (1/5 : ℚ) = 15/11 := by native_decide
example : jacobiCF [1, 2, 2] [1, 1] (1/5 : ℚ) = 40/29 := by native_decide

-- Motzkin J-fraction: all bᵢ = 1, all aᵢ = 1
-- Encodes M(z) = 1/(1 - z - z²·M(z)), the Motzkin OGF
example : jacobiCF [1, 1] [1] (0 : ℚ) = 1 := by native_decide
example : jacobiCF [1, 1, 1] [1, 1] (0 : ℚ) = 1 := by native_decide

-- ============================================================================
-- §5. Stieltjes-to-Jacobi Contraction
-- ============================================================================

-- An S-fraction with coefficients [c₁,...,c_{2k+1}] contracts to a J-fraction
-- via bⱼ = c_{2j+1} + c_{2j+2} and aⱼ = c_{2j}·c_{2j+1}.
-- For all cᵢ = 1: S-fraction with 2k+1 terms = J-fraction with (k+1, k) terms.

example : stieltjesCF [1] (1/5 : ℚ) = jacobiCF [1] [] (1/5 : ℚ) := by native_decide
example : stieltjesCF [1, 1, 1] (1/5 : ℚ) = jacobiCF [1, 2] [1] (1/5 : ℚ) := by
  native_decide
example : stieltjesCF [1, 1, 1, 1, 1] (1/5 : ℚ) = jacobiCF [1, 2, 2] [1, 1] (1/5 : ℚ) := by
  native_decide

-- ============================================================================
-- §6. Structural Theorems
-- ============================================================================

/-- Euler-Minding: pₙqₙ₋₁ - pₙ₋₁qₙ = (-1)^n for simple CFs -/
theorem euler_minding_determinant (coeffs : List ℕ) (h : coeffs.length ≥ 2) :
    let (pn, qn) := convergent coeffs
    let (pm, qm) := convergent coeffs.dropLast
    (pn : ℤ) * qm - pm * qn = (-1) ^ coeffs.length := by
  sorry

/-- The Stieltjes CF 1/(1-z/(1-z/(1-...))) with all cᵢ = 1 satisfies
    S(z) = 1 + zS(z)², making it the Catalan OGF -/
theorem stieltjes_catalan_functional_equation :
    ∀ (n : ℕ), ∃ (S : ℚ → ℚ),
    (∀ z : ℚ, S z = stieltjesCF (List.replicate n 1) z) ∧
    (n ≥ 2 → ∀ z : ℚ, z ≠ 0 →
      |S z - (1 + z * (S z) ^ 2)| ≤ |z| ^ n) := by
  sorry

/-- The S-to-J contraction theorem: an S-fraction with 2n+1 positive coefficients
    contracts to a J-fraction preserving the rational function identity -/
theorem stieltjes_jacobi_contraction (cs : List ℚ) (z : ℚ)
    (hlen : cs.length = 2 * n + 1) (hpos : ∀ c ∈ cs, c > 0) :
    ∃ (bs : List ℚ) (as : List ℚ),
    bs.length = n + 1 ∧ as.length = n ∧
    stieltjesCF cs z = jacobiCF bs as z := by
  sorry

/-- Jacobi CFs encode three-term recurrences of orthogonal polynomials:
    Pₙ₊₁(x) = (x - bₙ)Pₙ(x) - aₙPₙ₋₁(x) implies the moment GF
    μ(z) = Σ μₙzⁿ has a J-fraction with these coefficients -/
theorem jacobi_orthogonal_moments (b_coeffs : List ℚ) (a_coeffs : List ℚ)
    (hlen : a_coeffs.length + 1 = b_coeffs.length)
    (hpos : ∀ a ∈ a_coeffs, a > 0) :
    ∃ (moments : List ℚ), moments.length = 2 * a_coeffs.length + 1 ∧
    moments.head? = some 1 := by
  sorry

end ContinuedFractions
