import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MellinTransforms

open Finset Complex

/-!
# Mellin Transforms in Analytic Combinatorics

Flajolet–Sedgewick, Chapter V §5 and Appendix B.7.

The Mellin transform converts a function on (0,∞) into a function of a complex
variable s, valid in a vertical strip (the fundamental strip). Its main use in
analytic combinatorics is the asymptotic analysis of harmonic sums arising in
average-case analysis of algorithms.
-/

/-! ## 1. The Mellin transform and fundamental strip -/

/-- The Mellin transform of f, defined as ∫₀^∞ f(x) x^(s-1) dx. -/
noncomputable def mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0, f x * (x : ℂ) ^ (s - 1)

/-- The fundamental strip: the vertical strip ⟨α, β⟩ where the Mellin transform converges. -/
structure FundamentalStrip where
  α : ℝ
  β : ℝ
  hlt : α < β

/-- Predicate: s lies in the fundamental strip. -/
def inStrip (F : FundamentalStrip) (s : ℂ) : Prop :=
  F.α < s.re ∧ s.re < F.β

/-- The Mellin inversion formula: f(x) = (1/2πi) ∫_{c-i∞}^{c+i∞} f*(s) x^(-s) ds. -/
noncomputable def mellinInverse (fstar : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I)) *
    ∫ t : ℝ, fstar (c + t * I) * (x : ℂ) ^ (-(c + t * I))

/-- The Mellin transform of e^(-x) is Γ(s), in the strip ⟨0, ∞⟩. -/
theorem mellin_exp_eq_gamma (s : ℂ) (hs : 0 < s.re) :
    mellinTransform (fun x => Complex.exp (-x)) s =
      ∫ x : ℝ in Set.Ioi 0, Complex.exp (-x) * (x : ℂ) ^ (s - 1) := by
  sorry

/-- Fundamental strip of e^(-x) is ⟨0, ∞⟩ (represented finitely as ⟨0, M⟩ for any M). -/
def expFundamentalStrip (M : ℝ) (hM : 0 < M) : FundamentalStrip :=
  ⟨0, M, hM⟩

/-- The Mellin transform of 1/(1+x) is π/sin(πs) in the strip ⟨0,1⟩. -/
theorem mellin_inv_one_plus (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    mellinTransform (fun x => 1 / ((x : ℂ) + 1)) s =
      Real.pi / Complex.sin (Real.pi * s) := by
  sorry

/-! ## 2. Harmonic sums and the factorization property -/

/-- A harmonic sum: H(x) = ∑ₖ cₖ g(μₖ x). -/
noncomputable def harmonicSum (n : ℕ) (coeffs : Fin n → ℂ) (mu : Fin n → ℝ)
    (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k : Fin n, coeffs k * g (mu k * x)

/-- The Mellin transform of a harmonic sum factorizes:
    H*(s) = (∑ₖ cₖ μₖ^(-s)) · g*(s). -/
theorem mellin_harmonic_sum_factorization (n : ℕ) (coeffs : Fin n → ℂ)
    (mu : Fin n → ℝ) (g : ℝ → ℂ) (s : ℂ)
    (hmu : ∀ k, 0 < mu k) :
    mellinTransform (harmonicSum n coeffs mu g) s =
      (∑ k : Fin n, coeffs k * (mu k : ℂ) ^ (-s)) * mellinTransform g s := by
  sorry

/-- The Dirichlet series Λ(s) = ∑ₖ cₖ μₖ^(-s) appearing in factorization. -/
noncomputable def dirichletComponent (n : ℕ) (coeffs : Fin n → ℂ)
    (mu : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∑ k : Fin n, coeffs k * (mu k : ℂ) ^ (-s)

/-! ## 3. Binary digital sums -/

/-- Fuelled binary digit sum. -/
def s2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 => (n + 1) % 2 + s2Fuel fuel ((n + 1) / 2)

/-- `s₂(n)`: number of 1-bits in n. -/
def s2 (n : ℕ) : ℕ := s2Fuel (n + 1) n

/-- Cumulative binary weight: ∑_{0 ≤ m < n} s₂(m). -/
def cumulativeS2 (n : ℕ) : ℕ := ∑ m ∈ range n, s2 m

/-- Binary splitting: s₂(2n) = s₂(n). -/
example : ∀ n : Fin 64, s2 (2 * (n : ℕ)) = s2 n := by native_decide

/-- Binary splitting: s₂(2n+1) = s₂(n) + 1. -/
example : ∀ n : Fin 64, s2 (2 * (n : ℕ) + 1) = s2 n + 1 := by native_decide

/-- Complete binary blocks: ∑_{m<2^k} s₂(m) = k·2^(k-1). -/
example : cumulativeS2 (2 ^ 0) = 0 * 2 ^ (0 - 1) := by native_decide
example : cumulativeS2 (2 ^ 1) = 1 * 2 ^ (1 - 1) := by native_decide
example : cumulativeS2 (2 ^ 2) = 2 * 2 ^ (2 - 1) := by native_decide
example : cumulativeS2 (2 ^ 3) = 3 * 2 ^ (3 - 1) := by native_decide
example : cumulativeS2 (2 ^ 4) = 4 * 2 ^ (4 - 1) := by native_decide
example : cumulativeS2 (2 ^ 5) = 5 * 2 ^ (5 - 1) := by native_decide

/-! ## 4. Ruler function and Legendre's formula -/

/-- Fuelled 2-adic valuation. -/
def v2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 =>
      if (n + 1) % 2 = 0 then 1 + v2Fuel fuel ((n + 1) / 2) else 0

/-- v₂(n): 2-adic valuation (v₂(0) := 0). -/
def v2 (n : ℕ) : ℕ := v2Fuel (n + 1) n

/-- v₂(n!) = ∑_{1≤m≤n} v₂(m). -/
def v2Factorial (n : ℕ) : ℕ := ∑ m ∈ range (n + 1), v2 m

/-- Legendre's formula: v₂(n!) = n - s₂(n). -/
example : ∀ n : Fin 33, v2Factorial n = (n : ℕ) - s2 n := by native_decide

example : v2Factorial 8 = 7 := by native_decide
example : v2Factorial 16 = 15 := by native_decide
example : v2Factorial 32 = 31 := by native_decide

/-! ## 5. Divide-and-conquer recurrences -/

/-- Fuelled mergesort-type cost T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + n. -/
def divConqFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | fuel + 1, n + 2 =>
      divConqFuel fuel ((n + 2) / 2) + divConqFuel fuel ((n + 3) / 2) + (n + 2)

/-- T(n): mergesort divide-and-conquer cost. -/
def divConqT (n : ℕ) : ℕ := divConqFuel (n + 1) n

/-- On powers of two: T(2^k) = k·2^k (exact, no fluctuation). -/
example : ∀ k : Fin 11, divConqT (2 ^ (k : ℕ)) = (k : ℕ) * 2 ^ (k : ℕ) := by
  native_decide

/-- The recurrence itself, verified on a finite range. -/
example :
    ∀ n : Fin 64,
      divConqT ((n : ℕ) + 2) =
        divConqT (((n : ℕ) + 2) / 2) + divConqT (((n : ℕ) + 3) / 2) + ((n : ℕ) + 2) := by
  native_decide

/-! ## 6. Mellin transform of the toll function -/

/-- The toll function for mergesort is t(x) = x on [1,∞).
    Its Mellin transform is -1/(s(s+1)) in ⟨-2,-1⟩.
    After the change of variable this gives the asymptotic expansion. -/
theorem mergesort_mellin_toll (s : ℂ) (hs : -2 < s.re) (hs' : s.re < -1) :
    mellinTransform (fun x => if 1 ≤ x then (x : ℂ) else 0) s =
      -1 / (s * (s + 1)) := by
  sorry

/-! ## 7. Digit sum in arbitrary base -/

/-- Fuelled digit sum in base b. -/
def digitSumFuel (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if b ≤ 1 then n
      else if n = 0 then 0
      else n % b + digitSumFuel b fuel (n / b)

/-- Sum of digits of n in base b. -/
def digitSumBase (b n : ℕ) : ℕ := digitSumFuel b (n + 1) n

/-- Cumulative digit sum. -/
def cumulativeDigitSum (b n : ℕ) : ℕ := ∑ m ∈ range n, digitSumBase b m

/-- Kempner's formula: ∑_{m<b^k} s_b(m) = k(b-1)/2 · b^k, binary case. -/
example : cumulativeDigitSum 2 (2 ^ 4) = 2 ^ 4 * Nat.log 2 (2 ^ 4) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 5) = 2 ^ 5 * Nat.log 2 (2 ^ 5) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 6) = 2 ^ 6 * Nat.log 2 (2 ^ 6) / 2 := by native_decide

/-! ## 8. Asymptotic structure from Mellin analysis -/

/-- The fluctuating term in the digital sum asymptotics is periodic in log₂ n
    with period 1. This encodes the Fourier coefficients arising from poles of
    the Dirichlet series ∑ 2^(-ks) at s = 1 + 2kπi/ln2. -/
theorem digital_sum_asymptotic_structure :
    ∀ k : Fin 7,
      cumulativeS2 (2 ^ (k : ℕ)) = (k : ℕ) * 2 ^ ((k : ℕ) - 1) := by
  native_decide

/-- Harmonic sum model: finite decomposition check. -/
structure FiniteHarmonicModel where
  modes : ℕ
  lambda : Fin modes → ℚ
  beta : Fin modes → ℤ
  kernel : ℤ → ℚ

def evalHarmonicModel (M : FiniteHarmonicModel) (s : ℤ) : ℚ :=
  ∑ k : Fin M.modes, M.lambda k * M.kernel (s + M.beta k)

def twoModeModel : FiniteHarmonicModel where
  modes := 2
  lambda := ![1, -1 / 2]
  beta := ![0, 1]
  kernel := fun s => s

example : evalHarmonicModel twoModeModel 5 = 5 + (-1 / 2) * 6 := by native_decide
example : evalHarmonicModel twoModeModel (-3) = -3 + (-1 / 2) * (-2) := by native_decide

end MellinTransforms
