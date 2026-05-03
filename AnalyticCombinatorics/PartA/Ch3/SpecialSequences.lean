import Mathlib.Tactic

set_option linter.style.nativeDecide false

open Finset Nat

namespace SpecialSequences

/-!
# Special integer sequences

Finite, computable tables for several classical integer sequences occurring
around the elementary functions of Chapter III of Flajolet and Sedgewick.
The identities below are deliberately stated over bounded tables, so that each
check is a concrete decidable verification.
-/

/-! ## Bernoulli numbers -/

/-- A rational number represented by an integer numerator and denominator. -/
abbrev IntPair := Int × Int

/-- Selected Bernoulli numbers as integer pairs `(num, den)`. -/
def bernoulliPair : Nat → IntPair
  | 0 => (1, 1)
  | 2 => (1, 6)
  | 4 => (-1, 30)
  | _ => (0, 1)

def bernoulliNum (n : Nat) : Int := (bernoulliPair n).1
def bernoulliDen (n : Nat) : Int := (bernoulliPair n).2
def bernoulliValue (n : Nat) : Rat := (bernoulliNum n : Rat) / (bernoulliDen n : Rat)

example : bernoulliPair 0 = (1, 1) := by native_decide
example : bernoulliNum 0 = 1 := by native_decide
example : bernoulliPair 2 = (1, 6) := by native_decide
example : bernoulliNum 2 = 1 := by native_decide
example : bernoulliDen 2 = 6 := by native_decide
example : bernoulliPair 4 = (-1, 30) := by native_decide
example : bernoulliNum 4 = -1 := by native_decide
example : bernoulliDen 4 = 30 := by native_decide

/-- Multiplying the stored rational value by its denominator recovers the numerator. -/
example : (bernoulliDen 0 : Rat) * bernoulliValue 0 = (bernoulliNum 0 : Rat) := by
  native_decide

example : (bernoulliDen 2 : Rat) * bernoulliValue 2 = (bernoulliNum 2 : Rat) := by
  native_decide

example : (bernoulliDen 4 : Rat) * bernoulliValue 4 = (bernoulliNum 4 : Rat) := by
  native_decide

example : 6 * bernoulliValue 2 = 1 := by native_decide
example : 30 * bernoulliValue 4 = -1 := by native_decide
example : bernoulliValue 2 * bernoulliValue 4 = ((-1 : Rat) / 180) := by
  native_decide

/-! ## Euler numbers and secant coefficients -/

/-- Signed even Euler numbers, indexed by the actual even subscript. -/
def eulerNumber : Nat → Int
  | 0 => 1
  | 2 => -1
  | 4 => 5
  | 6 => -61
  | 8 => 1385
  | _ => 0

/-- Absolute even Euler numbers `|E_{2n}|`, indexed by `n`. -/
def absEulerEven : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 5
  | 3 => 61
  | 4 => 1385
  | 5 => 50521
  | _ => 0

example : eulerNumber 0 = 1 := by native_decide
example : eulerNumber 2 = -1 := by native_decide
example : eulerNumber 4 = 5 := by native_decide
example : eulerNumber 6 = -61 := by native_decide
example : eulerNumber 8 = 1385 := by native_decide

example : absEulerEven 0 = 1 := by native_decide
example : absEulerEven 1 = 1 := by native_decide
example : absEulerEven 2 = 5 := by native_decide
example : absEulerEven 3 = 61 := by native_decide
example : absEulerEven 4 = 1385 := by native_decide
example : absEulerEven 5 = 50521 := by native_decide

example :
    ∀ n : Fin 5,
      eulerNumber (2 * (n : Nat)) =
        if (n : Nat) % 2 = 0 then (absEulerEven (n : Nat) : Int)
        else -((absEulerEven (n : Nat) : Int)) := by
  native_decide

/-! ## Tangent numbers -/

/-- Tangent numbers indexed by the actual odd subscript. -/
def tangentNumber : Nat → Nat
  | 1 => 1
  | 3 => 2
  | 5 => 16
  | 7 => 272
  | 9 => 7936
  | _ => 0

/-- Tangent coefficients indexed by `n`, so this is `T_{2n+1}`. -/
def tangentCoeff : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 16
  | 3 => 272
  | 4 => 7936
  | _ => 0

example : tangentNumber 1 = 1 := by native_decide
example : tangentNumber 3 = 2 := by native_decide
example : tangentNumber 5 = 16 := by native_decide
example : tangentNumber 7 = 272 := by native_decide
example : tangentNumber 9 = 7936 := by native_decide

example : ∀ n : Fin 5, tangentNumber (2 * (n : Nat) + 1) = tangentCoeff (n : Nat) := by
  native_decide

/-! ## Genocchi numbers -/

/-- Positive Genocchi numbers as listed by even subscript. -/
def genocchiNumber : Nat → Nat
  | 2 => 1
  | 4 => 1
  | 6 => 3
  | 8 => 17
  | 10 => 155
  | _ => 0

example : genocchiNumber 2 = 1 := by native_decide
example : genocchiNumber 4 = 1 := by native_decide
example : genocchiNumber 6 = 3 := by native_decide
example : genocchiNumber 8 = 17 := by native_decide
example : genocchiNumber 10 = 155 := by native_decide

/-! ## Poly-Bernoulli numbers -/

/-- Stirling numbers of the second kind, used for negative-index poly-Bernoulli numbers. -/
def stirlingSecond : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

/-- Negative-index poly-Bernoulli numbers `B_n^(-k)`. -/
def polyBernoulliNeg (n k : Nat) : Nat :=
  ∑ m ∈ range (min n k + 1),
    (factorial m) ^ 2 * stirlingSecond (n + 1) (m + 1) * stirlingSecond (k + 1) (m + 1)

/-- A small `B_n^(-k)` table, rows indexed by `n`, columns by `k`. -/
def polyBernoulliNegTable : List (List Nat) :=
  [[1, 1, 1, 1, 1],
   [1, 2, 4, 8, 16],
   [1, 4, 14, 46, 146],
   [1, 8, 46, 230, 1066],
   [1, 16, 146, 1066, 6902]]

example : polyBernoulliNeg 0 0 = 1 := by native_decide
example : polyBernoulliNeg 1 3 = 8 := by native_decide
example : polyBernoulliNeg 2 2 = 14 := by native_decide
example : polyBernoulliNeg 3 2 = 46 := by native_decide
example : polyBernoulliNeg 4 4 = 6902 := by native_decide

example :
    polyBernoulliNegTable =
      [[polyBernoulliNeg 0 0, polyBernoulliNeg 0 1, polyBernoulliNeg 0 2,
        polyBernoulliNeg 0 3, polyBernoulliNeg 0 4],
       [polyBernoulliNeg 1 0, polyBernoulliNeg 1 1, polyBernoulliNeg 1 2,
        polyBernoulliNeg 1 3, polyBernoulliNeg 1 4],
       [polyBernoulliNeg 2 0, polyBernoulliNeg 2 1, polyBernoulliNeg 2 2,
        polyBernoulliNeg 2 3, polyBernoulliNeg 2 4],
       [polyBernoulliNeg 3 0, polyBernoulliNeg 3 1, polyBernoulliNeg 3 2,
        polyBernoulliNeg 3 3, polyBernoulliNeg 3 4],
       [polyBernoulliNeg 4 0, polyBernoulliNeg 4 1, polyBernoulliNeg 4 2,
        polyBernoulliNeg 4 3, polyBernoulliNeg 4 4]] := by
  native_decide

/-! ## Secant-tangent convolution -/

/--
The coefficient identity from `d(sec x)/dx = sec x * tan x`, checked for
`n = 0, ..., 4`:

`|E_{2n+2}| = sum_j binom(2n+1,2j) |E_{2j}| T_{2(n-j)+1}`.
-/
theorem absEulerEven_secant_tangent_sum :
    ∀ n : Fin 5,
      absEulerEven ((n : Nat) + 1) =
        ∑ j ∈ range ((n : Nat) + 1),
          choose (2 * (n : Nat) + 1) (2 * j) *
            absEulerEven j * tangentCoeff ((n : Nat) - j) := by
  native_decide

example :
    absEulerEven 3 =
      choose 5 0 * absEulerEven 0 * tangentCoeff 2 +
      choose 5 2 * absEulerEven 1 * tangentCoeff 1 +
      choose 5 4 * absEulerEven 2 * tangentCoeff 0 := by
  native_decide

example :
    absEulerEven 5 =
      choose 9 0 * absEulerEven 0 * tangentCoeff 4 +
      choose 9 2 * absEulerEven 1 * tangentCoeff 3 +
      choose 9 4 * absEulerEven 2 * tangentCoeff 2 +
      choose 9 6 * absEulerEven 3 * tangentCoeff 1 +
      choose 9 8 * absEulerEven 4 * tangentCoeff 0 := by
  native_decide

end SpecialSequences
