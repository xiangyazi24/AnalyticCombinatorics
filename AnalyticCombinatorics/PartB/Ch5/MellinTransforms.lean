import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace MellinTransforms

open Finset

/-!
Executable checks for Mellin-transform style formulae in digital analysis
(Flajolet--Sedgewick, Chapter V).  The analytic equalities are represented by
finite, computable shadows: harmonic sums decompose into shifted Mellin kernels,
and the digital identities are checked on exact finite ranges.
-/

/-! ## 1. Harmonic-sum decomposition -/

/--
A finite Mellin harmonic-sum model:
`H(s) = sum_k lambda_k * fstar(s + beta_k)`.

The index `k` represents the frequencies/residue classes that arise after
Mellin inversion and residue collection.
-/
structure HarmonicSumModel where
  modes : ℕ
  lambda : Fin modes → ℚ
  beta : Fin modes → ℤ
  fstar : ℤ → ℚ

/-- The harmonic sum assembled from shifted Mellin kernels. -/
def H (M : HarmonicSumModel) (s : ℤ) : ℚ :=
  ∑ k : Fin M.modes, M.lambda k * M.fstar (s + M.beta k)

/-- A two-mode toy model used to check the decomposition shape. -/
def binaryToyModel : HarmonicSumModel where
  modes := 2
  lambda := ![1, -1 / 2]
  beta := ![0, 1]
  fstar := fun s => s

/-- Concrete check of `H(s) = sum_k lambda_k * fstar(s + beta_k)`. -/
example : H binaryToyModel 5 = 5 + (-1 / 2) * 6 := by native_decide

/-- The same finite decomposition at another argument. -/
example : H binaryToyModel (-3) = -3 + (-1 / 2) * (-2) := by native_decide

/-! ## 2. Binary digital sums -/

/-- Fuelled binary digit sum. -/
def s2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 => (n + 1) % 2 + s2Fuel fuel ((n + 1) / 2)

/-- `s_2(n)`: number of `1` bits in the binary expansion of `n`. -/
def s2 (n : ℕ) : ℕ :=
  s2Fuel (n + 1) n

/-- Cumulative binary weight: `sum_{0 <= m < n} s_2(m)`. -/
def cumulativeS2 (n : ℕ) : ℕ :=
  ∑ m ∈ range n, s2 m

/-- Binary splitting identity `s_2(2n) = s_2(n)`, checked for small `n`. -/
example : ∀ n : Fin 64, s2 (2 * (n : ℕ)) = s2 n := by native_decide

/-- Binary splitting identity `s_2(2n+1) = s_2(n)+1`, checked for small `n`. -/
example : ∀ n : Fin 64, s2 (2 * (n : ℕ) + 1) = s2 n + 1 := by native_decide

/-- Cumulative identity on complete binary blocks. -/
example : cumulativeS2 (2 ^ 0) = 0 * 2 ^ (0 - 1) := by native_decide
example : cumulativeS2 (2 ^ 1) = 1 * 2 ^ (1 - 1) := by native_decide
example : cumulativeS2 (2 ^ 2) = 2 * 2 ^ (2 - 1) := by native_decide
example : cumulativeS2 (2 ^ 3) = 3 * 2 ^ (3 - 1) := by native_decide
example : cumulativeS2 (2 ^ 4) = 4 * 2 ^ (4 - 1) := by native_decide
example : cumulativeS2 (2 ^ 5) = 5 * 2 ^ (5 - 1) := by native_decide
example : cumulativeS2 (2 ^ 6) = 6 * 2 ^ (6 - 1) := by native_decide

/-! ## 3. Ruler function and Legendre's formula -/

/-- Fuelled ruler function. -/
def v2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 =>
      if (n + 1) % 2 = 0 then
        1 + v2Fuel fuel ((n + 1) / 2)
      else
        0

/-- `v_2(n)`: the exponent of `2` in `n`; `v_2(0)` is set to `0` here. -/
def v2 (n : ℕ) : ℕ :=
  v2Fuel (n + 1) n

/-- `v_2(n!) = sum_{1 <= m <= n} v_2(m)`. -/
def v2Factorial (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), v2 m

/-- Legendre/ruler formula: `v_2(n!) = n - s_2(n)`, checked for small `n`. -/
example : ∀ n : Fin 33, v2Factorial n = (n : ℕ) - s2 n := by native_decide

example : v2Factorial 0 = 0 := by native_decide
example : v2Factorial 1 = 0 := by native_decide
example : v2Factorial 2 = 1 := by native_decide
example : v2Factorial 3 = 1 := by native_decide
example : v2Factorial 4 = 3 := by native_decide
example : v2Factorial 8 = 7 := by native_decide
example : v2Factorial 16 = 15 := by native_decide

/-! ## 4. Kempner digit-sum formula -/

/-- Fuelled digit sum in base `b`; bases `0` and `1` are treated trivially. -/
def digitSumFuel (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if b ≤ 1 then
        n
      else if n = 0 then
        0
      else
        n % b + digitSumFuel b fuel (n / b)

/-- Sum of digits of `n` in base `b`. -/
def digitSumBase (b n : ℕ) : ℕ :=
  digitSumFuel b (n + 1) n

/-- Cumulative sum of base-`b` digits over `0 <= m < n`. -/
def cumulativeDigitSum (b n : ℕ) : ℕ :=
  ∑ m ∈ range n, digitSumBase b m

/-- Kempner's exact complete-block formula, in binary. -/
example : cumulativeDigitSum 2 (2 ^ 1) = 2 ^ 1 * Nat.log 2 (2 ^ 1) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 2) = 2 ^ 2 * Nat.log 2 (2 ^ 2) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 3) = 2 ^ 3 * Nat.log 2 (2 ^ 3) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 4) = 2 ^ 4 * Nat.log 2 (2 ^ 4) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 5) = 2 ^ 5 * Nat.log 2 (2 ^ 5) / 2 := by native_decide
example : cumulativeDigitSum 2 (2 ^ 6) = 2 ^ 6 * Nat.log 2 (2 ^ 6) / 2 := by native_decide

/--
For base `b`, the complete-block average is
`k * (b - 1) / 2` over the `b^k` numbers with at most `k` digits.
This is the exact finite counterpart of the usual Kempner mean term.
-/
def completeBlockAverageDigitSum (b k : ℕ) : ℚ :=
  (k : ℚ) * (b - 1 : ℕ) / 2

example : completeBlockAverageDigitSum 2 6 = 3 := by native_decide
example : completeBlockAverageDigitSum 10 4 = 18 := by native_decide

/-! ## 5. Radix representation counts -/

/-- Number of positive integers with exactly `k` digits in base `b`. -/
def radixKDigitCount (b k : ℕ) : ℕ :=
  b ^ k - b ^ (k - 1)

example : radixKDigitCount 2 1 = 1 := by native_decide
example : radixKDigitCount 2 8 = 128 := by native_decide
example : radixKDigitCount 10 1 = 9 := by native_decide
example : radixKDigitCount 10 3 = 900 := by native_decide
example : radixKDigitCount 16 2 = 240 := by native_decide

/-- Bounded check of `b^k - b^(k-1) = (b-1)b^(k-1)`. -/
example :
    ∀ b : Fin 17, ∀ k : Fin 8,
      2 ≤ (b : ℕ) + 2 →
        radixKDigitCount ((b : ℕ) + 2) ((k : ℕ) + 1)
          = (((b : ℕ) + 2) - 1) * ((b : ℕ) + 2) ^ (k : ℕ) := by
  native_decide

/-! ## 6. Divide-and-conquer recurrence -/

/-- Fuelled divide-and-conquer cost. -/
def divideConquerTFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | fuel + 1, n + 2 =>
      divideConquerTFuel fuel ((n + 2) / 2)
        + divideConquerTFuel fuel ((n + 3) / 2)
        + (n + 2)

/--
Cost model for
`T(n) = T(floor(n/2)) + T(ceil(n/2)) + n`, with `T(0)=T(1)=0`.
-/
def divideConquerT (n : ℕ) : ℕ :=
  divideConquerTFuel (n + 1) n

/-- The recurrence itself, checked on a finite range. -/
example :
    ∀ n : Fin 64,
      divideConquerT ((n : ℕ) + 2)
        =
          divideConquerT (((n : ℕ) + 2) / 2)
            + divideConquerT (((n : ℕ) + 3) / 2)
            + ((n : ℕ) + 2) := by
  native_decide

/-- Powers of two satisfy the closed form `T(2^k) = k 2^k`. -/
example : ∀ k : Fin 11, divideConquerT (2 ^ (k : ℕ)) = (k : ℕ) * 2 ^ (k : ℕ) := by
  native_decide

example : divideConquerT 2 = 2 := by native_decide
example : divideConquerT 4 = 8 := by native_decide
example : divideConquerT 8 = 24 := by native_decide
example : divideConquerT 16 = 64 := by native_decide
example : divideConquerT 32 = 160 := by native_decide

end MellinTransforms
