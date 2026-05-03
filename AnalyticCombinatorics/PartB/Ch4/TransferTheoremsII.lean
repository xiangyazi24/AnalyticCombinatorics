import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace TransferTheoremsII

/-!
Transfer-theorem numerics for Chapter IV singularity analysis.

The statements below are finite, computable checks for standard model cases:
integer powers `(1 - z)^(-alpha)`, singularity-type tables, logarithmic
singularities, and small comparisons between polynomial and exponential growth.
-/

/-! ## Integer-power transfer coefficients -/

/-- Coefficient of `z^n` in `(1 - z)^(-alpha)` for positive integer `alpha`. -/
def transferPowerCoeff (alpha n : ℕ) : ℕ :=
  Nat.choose (n + alpha - 1) (alpha - 1)

def alphaOneTransferTable : Fin 10 → ℕ :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def alphaTwoTransferTable : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def alphaThreeTransferTable : Fin 10 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55]

def alphaFourTransferTable : Fin 10 → ℕ :=
  ![1, 4, 10, 20, 35, 56, 84, 120, 165, 220]

theorem alpha_one_transfer_table :
    ∀ n : Fin 10, transferPowerCoeff 1 n.val = alphaOneTransferTable n := by
  native_decide

theorem alpha_two_transfer_table :
    ∀ n : Fin 10, transferPowerCoeff 2 n.val = alphaTwoTransferTable n := by
  native_decide

theorem alpha_three_transfer_table :
    ∀ n : Fin 10, transferPowerCoeff 3 n.val = alphaThreeTransferTable n := by
  native_decide

theorem alpha_four_transfer_table :
    ∀ n : Fin 10, transferPowerCoeff 4 n.val = alphaFourTransferTable n := by
  native_decide

theorem alpha_two_polynomial_form :
    ∀ n : Fin 12, transferPowerCoeff 2 n.val = n.val + 1 := by
  native_decide

theorem alpha_three_polynomial_form :
    ∀ n : Fin 12,
      transferPowerCoeff 3 n.val = (n.val + 1) * (n.val + 2) / 2 := by
  native_decide

/-! ## O-transfer style finite majorants -/

def linearMajorant (n : ℕ) : ℕ :=
  2 * (n + 1)

def quadraticMajorant (n : ℕ) : ℕ :=
  (n + 1) ^ 2

def cubicMajorant (n : ℕ) : ℕ :=
  (n + 1) ^ 3

theorem alpha_two_bigO_check_small :
    ∀ n : Fin 12, transferPowerCoeff 2 n.val ≤ linearMajorant n.val := by
  native_decide

theorem alpha_three_bigO_check_small :
    ∀ n : Fin 12, transferPowerCoeff 3 n.val ≤ quadraticMajorant n.val := by
  native_decide

theorem alpha_four_bigO_check_small :
    ∀ n : Fin 12, transferPowerCoeff 4 n.val ≤ cubicMajorant n.val := by
  native_decide

/-! ## Singularity type classification tables -/

/-- Encoded singularity classes used in the finite tables below. -/
inductive SingularityKind where
  | removable
  | pole
  | algebraic
  | logarithmic
  | essential
deriving DecidableEq

def singularityKindCode : SingularityKind → ℕ
  | .removable => 0
  | .pole => 1
  | .algebraic => 2
  | .logarithmic => 3
  | .essential => 4

def chapterIVSingularityKinds : Fin 8 → SingularityKind :=
  ![.pole, .pole, .algebraic, .logarithmic,
    .algebraic, .removable, .pole, .essential]

def chapterIVSingularityKindCodes : Fin 8 → ℕ :=
  ![1, 1, 2, 3, 2, 0, 1, 4]

theorem singularity_kind_code_table :
    ∀ i : Fin 8,
      singularityKindCode (chapterIVSingularityKinds i) =
        chapterIVSingularityKindCodes i := by
  native_decide

def isTransferAdmissible : SingularityKind → Bool
  | .removable => false
  | .pole => true
  | .algebraic => true
  | .logarithmic => true
  | .essential => false

def transferAdmissibleTable : Fin 8 → Bool :=
  ![true, true, true, true, true, false, true, false]

theorem transfer_admissible_table :
    ∀ i : Fin 8,
      isTransferAdmissible (chapterIVSingularityKinds i) =
        transferAdmissibleTable i := by
  native_decide

/-! ## Flajolet-Odlyzko model coefficient examples -/

def foModelCoeff (rhoInv alpha n : ℕ) : ℕ :=
  rhoInv ^ n * transferPowerCoeff alpha n

def foSimplePoleRhoTwo : Fin 9 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256]

def foDoublePoleRhoTwo : Fin 9 → ℕ :=
  ![1, 4, 12, 32, 80, 192, 448, 1024, 2304]

def foTriplePoleRhoThree : Fin 7 → ℕ :=
  ![1, 9, 54, 270, 1215, 5103, 20412]

theorem fo_simple_pole_rho_two :
    ∀ n : Fin 9, foModelCoeff 2 1 n.val = foSimplePoleRhoTwo n := by
  native_decide

theorem fo_double_pole_rho_two :
    ∀ n : Fin 9, foModelCoeff 2 2 n.val = foDoublePoleRhoTwo n := by
  native_decide

theorem fo_triple_pole_rho_three :
    ∀ n : Fin 7, foModelCoeff 3 3 n.val = foTriplePoleRhoThree n := by
  native_decide

/-! ## Logarithmic singularity coefficients -/

/-- Denominator of the coefficient of `z^(n+1)` in `-log (1 - z)`. -/
def negLogCoeffDenominator (n : ℕ) : ℕ :=
  n + 1

def negLogDenominatorTable : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem neg_log_denominator_table :
    ∀ n : Fin 10, negLogCoeffDenominator n.val = negLogDenominatorTable n := by
  native_decide

/-- Coefficients of `z^(n+1)` in `z / (1 - z)` after multiplying by `n + 1`. -/
def scaledLogDerivativeCoeff (n : ℕ) : ℕ :=
  (n + 1) * 1

def scaledLogDerivativeTable : Fin 10 → ℕ :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem scaled_log_derivative_table :
    ∀ n : Fin 10, scaledLogDerivativeCoeff n.val = scaledLogDerivativeTable n := by
  native_decide

theorem log_derivative_recovers_unit_coefficients :
    ∀ n : Fin 10,
      scaledLogDerivativeCoeff n.val / negLogCoeffDenominator n.val = 1 := by
  native_decide

/-! ## Power-law versus exponential growth for small `n` -/

def squarePowerLaw (n : ℕ) : ℕ :=
  (n + 1) ^ 2

def cubePowerLaw (n : ℕ) : ℕ :=
  (n + 1) ^ 3

def binaryExponential (n : ℕ) : ℕ :=
  2 ^ n

def ternaryExponential (n : ℕ) : ℕ :=
  3 ^ n

def squareVsBinaryFromSix : Fin 7 → Bool :=
  ![true, true, true, true, true, true, true]

def cubeVsTernaryFromFive : Fin 8 → Bool :=
  ![true, true, true, true, true, true, true, true]

theorem square_power_below_binary_from_six :
    ∀ i : Fin 7,
      (squarePowerLaw (i.val + 6) < binaryExponential (i.val + 6)) =
        squareVsBinaryFromSix i := by
  native_decide

theorem cube_power_below_ternary_from_five :
    ∀ i : Fin 8,
      (cubePowerLaw (i.val + 5) < ternaryExponential (i.val + 5)) =
        cubeVsTernaryFromFive i := by
  native_decide

end TransferTheoremsII
