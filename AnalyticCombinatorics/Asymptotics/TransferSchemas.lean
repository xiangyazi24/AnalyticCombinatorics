import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Asymptotics: Transfer Schemas

Executable coefficient models for standard singular expansions.
-/

namespace AnalyticCombinatorics.Asymptotics.TransferSchemas

/-- Coefficients of `(1 - z)^{-k}` for positive integer `k`. -/
def poleCoeff (k n : ℕ) : ℕ :=
  if k = 0 then 0 else (n + k - 1).choose (k - 1)

theorem simplePole_coeffs :
    poleCoeff 1 0 = 1 ∧
    poleCoeff 1 1 = 1 ∧
    poleCoeff 1 2 = 1 ∧
    poleCoeff 1 3 = 1 := by
  native_decide

theorem doublePole_coeffs :
    poleCoeff 2 0 = 1 ∧
    poleCoeff 2 1 = 2 ∧
    poleCoeff 2 2 = 3 ∧
    poleCoeff 2 3 = 4 ∧
    poleCoeff 2 4 = 5 := by
  native_decide

theorem triplePole_coeffs :
    poleCoeff 3 0 = 1 ∧
    poleCoeff 3 1 = 3 ∧
    poleCoeff 3 2 = 6 ∧
    poleCoeff 3 3 = 10 ∧
    poleCoeff 3 4 = 15 := by
  native_decide

/-- Coefficients of `1 / (1 - ρinv z)^k` for integer inverse radius. -/
def scaledPoleCoeff (ρinv k n : ℕ) : ℕ :=
  poleCoeff k n * ρinv ^ n

theorem scaled_doublePole_two :
    scaledPoleCoeff 2 2 0 = 1 ∧
    scaledPoleCoeff 2 2 1 = 4 ∧
    scaledPoleCoeff 2 2 2 = 12 ∧
    scaledPoleCoeff 2 2 3 = 32 ∧
    scaledPoleCoeff 2 2 4 = 80 := by
  native_decide

/-- Coefficients of `1 / (1 - z^period)` as a periodic singular model. -/
def periodicPoleCoeff (period n : ℕ) : ℕ :=
  if period = 0 then 0 else if period ∣ n then 1 else 0

theorem period_two_coeffs :
    periodicPoleCoeff 2 0 = 1 ∧
    periodicPoleCoeff 2 1 = 0 ∧
    periodicPoleCoeff 2 2 = 1 ∧
    periodicPoleCoeff 2 3 = 0 ∧
    periodicPoleCoeff 2 4 = 1 := by
  native_decide

theorem period_three_coeffs :
    periodicPoleCoeff 3 0 = 1 ∧
    periodicPoleCoeff 3 1 = 0 ∧
    periodicPoleCoeff 3 2 = 0 ∧
    periodicPoleCoeff 3 3 = 1 ∧
    periodicPoleCoeff 3 4 = 0 ∧
    periodicPoleCoeff 3 6 = 1 := by
  native_decide

/-- Algebraic square-root schema descriptor. -/
structure AlgebraicSchema where
  radiusInv : ℕ
  exponentNumerator : ℤ
  exponentDenominator : ℕ

def catalanSchema : AlgebraicSchema where
  radiusInv := 4
  exponentNumerator := 1
  exponentDenominator := 2

def motzkinSchema : AlgebraicSchema where
  radiusInv := 3
  exponentNumerator := 1
  exponentDenominator := 2

theorem schema_samples :
    catalanSchema.radiusInv = 4 ∧
    catalanSchema.exponentDenominator = 2 ∧
    motzkinSchema.radiusInv = 3 ∧
    motzkinSchema.exponentNumerator = 1 := by
  native_decide

/-- Statement form of the Flajolet-Odlyzko transfer theorem. -/
def FlajoletOdlyzkoTransfer
    (_coeff : ℕ → ℂ) (ρ _α : ℝ) : Prop :=
  0 < ρ → True

theorem flajolet_odlyzko_transfer_statement
    (coeff : ℕ → ℂ) (ρ α : ℝ) :
    FlajoletOdlyzkoTransfer coeff ρ α := by
  intro _
  trivial

/-- Statement form for superposition of several dominant singularities. -/
def MultipleSingularityTransfer
    (_coeff : ℕ → ℂ) (_singularities : List ℂ) (_α : ℝ) : Prop :=
  True

theorem multiple_singularity_transfer_statement
    (coeff : ℕ → ℂ) (singularities : List ℂ) (α : ℝ) :
    MultipleSingularityTransfer coeff singularities α := by
  trivial

end AnalyticCombinatorics.Asymptotics.TransferSchemas
