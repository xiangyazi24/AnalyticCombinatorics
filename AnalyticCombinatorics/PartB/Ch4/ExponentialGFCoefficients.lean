import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace ExponentialGFCoefficients

/-!
Coefficient extraction from exponential generating functions, following the
Chapter IV convention

  `F(z) = sum_n a_n * z^n / n!`, so `[z^n/n!] F(z) = a_n`.

Ordinary coefficients are represented as rationals when the displayed formula
uses `[z^n] F(z) * n!`.
-/

/-- Lookup in a finite natural-number coefficient table, extended by zero. -/
def coeffNat {N : ℕ} (a : Fin N → ℕ) (n : ℕ) : ℕ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-- Lookup in a finite integer coefficient table, extended by zero. -/
def coeffInt {N : ℕ} (a : Fin N → ℤ) (n : ℕ) : ℤ :=
  if h : n < N then a ⟨n, h⟩ else 0

/-- The ordinary coefficient `[z^n] exp(z) = 1 / n!`. -/
def expOrdCoeff (n : ℕ) : ℚ :=
  (1 : ℚ) / (Nat.factorial n : ℚ)

/-- The EGF coefficient `[z^n/n!] exp(z)`. -/
def expEgfCoeff (_n : ℕ) : ℕ :=
  1

/-- Multiplying `[z^n] exp(z)` by `n!` extracts the EGF coefficient `1`. -/
def expOrdCoeffScaled (n : ℕ) : ℚ :=
  expOrdCoeff n * (Nat.factorial n : ℚ)

theorem exp_ordinary_coefficients_are_inverse_factorials_up_to_10 :
    ∀ n : Fin 11, expOrdCoeffScaled n = (expEgfCoeff n : ℚ) := by
  native_decide

/-- The ordinary coefficient `[z^n] exp(a*z) = a^n / n!`. -/
def expLinearOrdCoeff (a n : ℕ) : ℚ :=
  (a ^ n : ℚ) / (Nat.factorial n : ℚ)

/-- The EGF coefficient `[z^n/n!] exp(a*z) = a^n`. -/
def expLinearEgfCoeff (a n : ℕ) : ℕ :=
  a ^ n

/-- Multiplying `[z^n] exp(a*z)` by `n!` extracts `a^n`. -/
def expLinearOrdCoeffScaled (a n : ℕ) : ℚ :=
  expLinearOrdCoeff a n * (Nat.factorial n : ℚ)

def expTwoTable : Fin 8 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128]

theorem exp_two_coefficients :
    ∀ n : Fin 8, expTwoTable n = expLinearEgfCoeff 2 n := by
  native_decide

theorem exp_two_ordinary_scaled_coefficients :
    ∀ n : Fin 8, expLinearOrdCoeffScaled 2 n = (expTwoTable n : ℚ) := by
  native_decide

/-- Stirling numbers of the second kind. -/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirlingSecond n k + (k + 1) * stirlingSecond n (k + 1)

/-- Bell numbers from the EGF `exp(exp(z) - 1)`. -/
def bellNumber (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => stirlingSecond n k)

/-- Ordinary coefficient `[z^n] exp(exp(z)-1) = B(n) / n!`. -/
def bellOrdCoeff (n : ℕ) : ℚ :=
  (bellNumber n : ℚ) / (Nat.factorial n : ℚ)

/-- `B(n) = [z^n] exp(exp(z)-1) * n!`. -/
def bellFromEgf (n : ℕ) : ℚ :=
  bellOrdCoeff n * (Nat.factorial n : ℚ)

def bellTable : Fin 8 → ℕ :=
  ![1, 1, 2, 5, 15, 52, 203, 877]

theorem bell_numbers_from_exp_exp_minus_one :
    ∀ n : Fin 8, bellFromEgf n = (bellTable n : ℚ) := by
  native_decide

theorem bell_numbers_table :
    ∀ n : Fin 8, bellNumber n = bellTable n := by
  native_decide

/-- Sign coefficients of `exp(-z)` as an EGF. -/
def alternatingSign (n : ℕ) : ℤ :=
  if n % 2 = 0 then 1 else -1

/-- Coefficients of `1/(1-z)` when written as an EGF. -/
def geometricAsEgfCoeff (n : ℕ) : ℤ :=
  (Nat.factorial n : ℤ)

/-- EGF product coefficient for integer-valued EGF coefficient sequences. -/
def egfMulCoeffInt (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum
    (fun k => (Nat.choose n k : ℤ) * a k * b (n - k))

/-- Derangements from the EGF `exp(-z)/(1-z)`. -/
def derangementFromEgf (n : ℕ) : ℤ :=
  egfMulCoeffInt alternatingSign geometricAsEgfCoeff n

/-- Subfactorials. -/
def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

def derangementTable : Fin 7 → ℕ :=
  ![1, 0, 1, 2, 9, 44, 265]

theorem derangement_egf_coefficients :
    ∀ n : Fin 7, derangementFromEgf n = (derangementTable n : ℤ) := by
  native_decide

theorem subfactorial_values :
    ∀ n : Fin 7, subfactorial n = derangementTable n := by
  native_decide

/-- Involutions from `exp(z + z^2/2)`, grouped by the number of transpositions. -/
def involutionFromEgf (n : ℕ) : ℕ :=
  (Finset.range (n / 2 + 1)).sum
    (fun j =>
      Nat.factorial n /
        (Nat.factorial (n - 2 * j) * 2 ^ j * Nat.factorial j))

/-- Involution numbers. -/
def involutionNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionNumber (n + 1) + (n + 1) * involutionNumber n

def involutionTable : Fin 8 → ℕ :=
  ![1, 1, 2, 4, 10, 26, 76, 232]

theorem involution_egf_coefficients :
    ∀ n : Fin 8, involutionFromEgf n = involutionTable n := by
  native_decide

theorem involution_recurrence_values :
    ∀ n : Fin 8, involutionNumber n = involutionTable n := by
  native_decide

/-- Fixed-point-free involutions, the `x=0` part of the involution EGF. -/
def fixedPointFreeInvolutions (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    Nat.factorial n / (2 ^ (n / 2) * Nat.factorial (n / 2))
  else
    0

/--
Absolute values of the probabilists' Hermite values at zero:
`|He_n(0)|`.  These count fixed-point-free involutions.
-/
def hermiteZeroAbs (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    Nat.factorial n / (2 ^ (n / 2) * Nat.factorial (n / 2))
  else
    0

def hermiteZeroInvolutionTable : Fin 9 → ℕ :=
  ![1, 0, 1, 0, 3, 0, 15, 0, 105]

theorem hermite_zero_fixed_point_free_involutions :
    ∀ n : Fin 9,
      hermiteZeroAbs n = fixedPointFreeInvolutions n ∧
        fixedPointFreeInvolutions n = hermiteZeroInvolutionTable n := by
  native_decide

/-- Labelled graphs on `n` vertices: `2^(n choose 2)`. -/
def labelledGraphCount (n : ℕ) : ℕ :=
  2 ^ Nat.choose n 2

def labelledGraphTableOneToSeven : Fin 7 → ℕ :=
  ![1, 2, 8, 64, 1024, 32768, 2097152]

theorem labelled_graph_counts_one_to_seven :
    ∀ i : Fin 7, labelledGraphTableOneToSeven i = labelledGraphCount (i + 1) := by
  native_decide

/-- Connected labelled graph counts `c_0..c_4`. -/
def connectedGraphTable : Fin 5 → ℕ :=
  ![0, 1, 1, 4, 38]

/-- Exponential-formula coefficient for labelled graphs on three vertices. -/
def graphExpFormulaCoeff3 : ℕ :=
  coeffNat connectedGraphTable 3 +
    3 * coeffNat connectedGraphTable 2 * coeffNat connectedGraphTable 1 +
      coeffNat connectedGraphTable 1 ^ 3

/-- Exponential-formula coefficient for labelled graphs on four vertices. -/
def graphExpFormulaCoeff4 : ℕ :=
  coeffNat connectedGraphTable 4 +
    4 * coeffNat connectedGraphTable 3 * coeffNat connectedGraphTable 1 +
      3 * coeffNat connectedGraphTable 2 ^ 2 +
        6 * coeffNat connectedGraphTable 2 * coeffNat connectedGraphTable 1 ^ 2 +
          coeffNat connectedGraphTable 1 ^ 4

theorem graph_exponential_formula_n3 :
    graphExpFormulaCoeff3 = labelledGraphCount 3 := by
  native_decide

theorem graph_exponential_formula_n4 :
    graphExpFormulaCoeff4 = labelledGraphCount 4 := by
  native_decide

end ExponentialGFCoefficients
