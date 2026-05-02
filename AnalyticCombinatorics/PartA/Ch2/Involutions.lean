import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-- Number of involutions on `n` labelled atoms. -/
def involutionCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => involutionCount (n + 1) + (n + 1) * involutionCount n

/-- Standalone form of the involution recurrence. -/
theorem involutionCount_rec (n : ℕ) :
    involutionCount (n + 2) =
      involutionCount (n + 1) + (n + 1) * involutionCount n := by
  rfl

theorem involutionCount_zero : involutionCount 0 = 1 := by
  native_decide

theorem involutionCount_one : involutionCount 1 = 1 := by
  native_decide

theorem involutionCount_two : involutionCount 2 = 2 := by
  native_decide

theorem involutionCount_three : involutionCount 3 = 4 := by
  native_decide

theorem involutionCount_four : involutionCount 4 = 10 := by
  native_decide

theorem involutionCount_five : involutionCount 5 = 26 := by
  native_decide

theorem involutionCount_six : involutionCount 6 = 76 := by
  native_decide

/-- The EGF whose coefficients are `involutionCount n / n!`. -/
noncomputable def involutionEgf : PowerSeries ℚ :=
  PowerSeries.mk fun n => (involutionCount n : ℚ) / n.factorial

/-- Coefficients of the formal series `exp(z + z^2 / 2)`. -/
noncomputable def expZAddZSquaredDivTwo : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ j ∈ Finset.range (n / 2 + 1),
      if 2 * j ≤ n then
        (1 : ℚ) / (((n - 2 * j).factorial * j.factorial * 2 ^ j : ℕ) : ℚ)
      else
        0

/-- EGF statement for involutions: `I(z) = exp(z + z^2 / 2)`. -/
def involutionEgf_eq_exp_z_add_z_squared_div_two : Prop :=
  involutionEgf = expZAddZSquaredDivTwo
