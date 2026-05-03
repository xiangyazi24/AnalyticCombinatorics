import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace RationalFunctionDecomposition

/-!
Executable coefficient checks for rational-function decompositions from
Chapter IV.  The identities below record the usual coefficient-extraction
formulas in finite, decidable form.
-/

/-! ## 1. Partial fractions for `1 / ((1 - z) (1 - 2z))` -/

def oneTwoCrossMul (z : ℤ) : ℤ :=
  2 * (1 - z) - (1 - 2 * z)

theorem one_two_partial_fraction_cross_mul :
    ∀ z : Fin 16, oneTwoCrossMul (z.val : ℤ) = 1 := by
  native_decide

def oneTwoProductCoeff (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), 2 ^ (n - j)

def oneTwoPartialFractionCoeff (n : ℕ) : ℤ :=
  2 * (2 : ℤ) ^ n - 1

def oneTwoClosedCoeff (n : ℕ) : ℤ :=
  (2 : ℤ) ^ (n + 1) - 1

theorem one_two_coeff_from_convolution :
    ∀ n : Fin 14,
      (oneTwoProductCoeff n.val : ℤ) = oneTwoPartialFractionCoeff n.val := by
  native_decide

theorem one_two_coeff_closed_form :
    ∀ n : Fin 14,
      oneTwoPartialFractionCoeff n.val = oneTwoClosedCoeff n.val := by
  native_decide

def oneTwoCoeffTable : Fin 10 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511, 1023]

theorem one_two_coeff_table :
    ∀ n : Fin 10, oneTwoCoeffTable n = oneTwoProductCoeff n.val := by
  native_decide

/-! ## 2. Transfer matrices and characteristic roots -/

structure Matrix2 where
  a00 : ℤ
  a01 : ℤ
  a10 : ℤ
  a11 : ℤ
deriving DecidableEq, Repr

def matrixTrace (M : Matrix2) : ℤ :=
  M.a00 + M.a11

def matrixDet (M : Matrix2) : ℤ :=
  M.a00 * M.a11 - M.a01 * M.a10

def charPoly2 (M : Matrix2) (x : ℤ) : ℤ :=
  x ^ 2 - matrixTrace M * x + matrixDet M

def transferMatrix : Matrix2 :=
  { a00 := 1, a01 := 0, a10 := 0, a11 := 2 }

def transferTracePower (n : ℕ) : ℕ :=
  1 ^ n + 2 ^ n

theorem transfer_characteristic_roots :
    charPoly2 transferMatrix 1 = 0 ∧ charPoly2 transferMatrix 2 = 0 := by
  native_decide

theorem transfer_growth_from_largest_root :
    ∀ n : Fin 14, transferTracePower n.val ≤ 2 * 2 ^ n.val := by
  native_decide

/-! ## 3. Fibonacci via partial fractions / Binet form -/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

structure Quad5 where
  rat : ℚ
  sqrt5 : ℚ
deriving DecidableEq, Repr

def qzero : Quad5 :=
  ⟨0, 0⟩

def qone : Quad5 :=
  ⟨1, 0⟩

def qnat (n : ℕ) : Quad5 :=
  ⟨(n : ℚ), 0⟩

def qadd (x y : Quad5) : Quad5 :=
  ⟨x.rat + y.rat, x.sqrt5 + y.sqrt5⟩

def qneg (x : Quad5) : Quad5 :=
  ⟨-x.rat, -x.sqrt5⟩

def qsub (x y : Quad5) : Quad5 :=
  qadd x (qneg y)

def qmul (x y : Quad5) : Quad5 :=
  ⟨x.rat * y.rat + 5 * x.sqrt5 * y.sqrt5,
    x.rat * y.sqrt5 + x.sqrt5 * y.rat⟩

def qpow (x : Quad5) : ℕ → Quad5
  | 0 => qone
  | n + 1 => qmul x (qpow x n)

def sqrtFive : Quad5 :=
  ⟨0, 1⟩

def phi : Quad5 :=
  ⟨(1 : ℚ) / 2, (1 : ℚ) / 2⟩

def psi : Quad5 :=
  ⟨(1 : ℚ) / 2, (-1 : ℚ) / 2⟩

theorem fibonacci_binet_scaled :
    ∀ n : Fin 13,
      qmul sqrtFive (qnat (fib n.val)) =
        qsub (qpow phi n.val) (qpow psi n.val) := by
  native_decide

def fiveFibSqTable : Fin 13 → ℕ :=
  ![0, 5, 5, 20, 45, 125, 320, 845, 2205, 5780, 15125, 39605, 103680]

theorem five_fib_sq_values :
    ∀ n : Fin 13, fiveFibSqTable n = 5 * fib n.val ^ 2 := by
  native_decide

/-! ## 4. Linear-recurrence solution skeletons -/

structure TwoRootSolution where
  c1 : ℤ
  r1 : ℤ
  c2 : ℤ
  r2 : ℤ
deriving DecidableEq, Repr

def TwoRootSolution.eval (s : TwoRootSolution) (n : ℕ) : ℤ :=
  s.c1 * s.r1 ^ n + s.c2 * s.r2 ^ n

def oneTwoTwoRootSolution : TwoRootSolution :=
  { c1 := 2, r1 := 2, c2 := -1, r2 := 1 }

theorem one_two_two_root_solution :
    ∀ n : Fin 14,
      oneTwoTwoRootSolution.eval n.val = oneTwoPartialFractionCoeff n.val := by
  native_decide

def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

def tribonacciCharPoly (x : ℤ) : ℤ :=
  x ^ 3 - x ^ 2 - x - 1

theorem tribonacci_recurrence_values :
    ∀ n : Fin 12,
      tribonacci (n.val + 3) =
        tribonacci (n.val + 2) + tribonacci (n.val + 1) + tribonacci n.val := by
  native_decide

def tribonacciTable : Fin 12 → ℕ :=
  ![0, 0, 1, 1, 2, 4, 7, 13, 24, 44, 81, 149]

theorem tribonacci_table_values :
    ∀ n : Fin 12, tribonacciTable n = tribonacci n.val := by
  native_decide

theorem tribonacci_characteristic_sample :
    (List.map tribonacciCharPoly [-2, -1, 0, 1, 2]) = [-11, -2, -1, -2, 1] := by
  native_decide

/-! ## 5. Multiple poles -/

def multiplePoleCoeff (k n : ℕ) : ℕ :=
  Nat.choose (n + k - 1) (k - 1)

def pole2Table : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def pole3Table : Fin 10 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55]

def pole4Table : Fin 10 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120, 165, 220]

theorem multiple_pole_k2 :
    ∀ n : Fin 10, pole2Table n = multiplePoleCoeff 2 n.val := by
  native_decide

theorem multiple_pole_k3 :
    ∀ n : Fin 10, pole3Table n = multiplePoleCoeff 3 n.val := by
  native_decide

theorem multiple_pole_k4 :
    ∀ n : Fin 10, pole4Table n = multiplePoleCoeff 4 n.val := by
  native_decide

/-! ## 6. Exponential-polynomial coefficient forms -/

def poleCoeffAlpha (alpha m n : ℕ) : ℕ :=
  Nat.choose (n + m - 1) (m - 1) * alpha ^ n

def shiftedPoleCoeffAlpha (alpha m shift n : ℕ) : ℕ :=
  if shift ≤ n then
    Nat.choose (n - shift + m - 1) (m - 1) * alpha ^ (n - shift)
  else
    0

def polynomialNumeratorPoleCoeff (coeffs : List ℕ) (alpha m n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range coeffs.length,
    coeffs[j]! * shiftedPoleCoeffAlpha alpha m j n

def linearFactorM2Alpha3 (n : ℕ) : ℕ :=
  (n + 1) * 3 ^ n

def quadraticFactorM3Alpha2 (n : ℕ) : ℕ :=
  ((n + 1) * (n + 2) / 2) * 2 ^ n

theorem exp_poly_m2_alpha3 :
    ∀ n : Fin 9,
      poleCoeffAlpha 3 2 n.val = linearFactorM2Alpha3 n.val := by
  native_decide

theorem exp_poly_m3_alpha2 :
    ∀ n : Fin 9,
      poleCoeffAlpha 2 3 n.val = quadraticFactorM3Alpha2 n.val := by
  native_decide

def onePlusZOverCubicPoleTable : Fin 8 → ℕ :=
  ![1, 7, 30, 104, 320, 912, 2464, 6400]

theorem exp_poly_with_numerator_small :
    ∀ n : Fin 8,
      onePlusZOverCubicPoleTable n =
        polynomialNumeratorPoleCoeff [1, 1] 2 3 n.val := by
  native_decide

def twoPlusThreeZOverSimplePoleTable : Fin 8 → ℕ :=
  ![2, 11, 44, 176, 704, 2816, 11264, 45056]

theorem exp_poly_simple_pole_with_numerator :
    ∀ n : Fin 8,
      twoPlusThreeZOverSimplePoleTable n =
        polynomialNumeratorPoleCoeff [2, 3] 4 1 n.val := by
  native_decide

end RationalFunctionDecomposition
