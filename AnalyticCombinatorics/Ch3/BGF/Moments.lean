import AnalyticCombinatorics.Ch3.BGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sequence
import AnalyticCombinatorics.Ch1.OGF.Compositions
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Ch3 -- Moments of bivariate generating functions

The first factorial moment differentiates the parameter variable `u` and then
sets `u = 1`.  For a parameterized class this extracts the cumulative parameter
over each fixed-size fiber.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- Formal derivative in the parameter variable `u`, coefficientwise in size. -/
noncomputable def uDeriv (F : ℚ[X]⟦X⟧) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => Polynomial.derivative (PowerSeries.coeff n F)

/-- First factorial moment series: differentiate in `u`, then set `u = 1`. -/
noncomputable def factorialMoment1 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv F)

/-- The first factorial moment coefficient is the cumulative parameter value on
the size-`n` fiber. -/
theorem ParamClass.coeff_factorialMoment1 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (factorialMoment1 C.bgf) = ∑ x : C.Obj n, (C.param n x : ℚ) := by
  classical
  simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf, ParamClass.paramPoly,
    Polynomial.derivative_X_pow]

/-- Mean value of the parameter on the size-`n` fiber. -/
noncomputable def ParamClass.mean (C : ParamClass) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (factorialMoment1 C.bgf) / (C.toCombClass.counts n : ℚ)

/-- The mean is the cumulative parameter divided by the number of objects. -/
theorem ParamClass.mean_eq (C : ParamClass) (n : ℕ) :
    C.mean n = (∑ x : C.Obj n, (C.param n x : ℚ)) / (C.toCombClass.counts n : ℚ) := by
  rw [ParamClass.mean, ParamClass.coeff_factorialMoment1]

/-- Integer compositions parameterized by their number of parts. -/
def ParamClass.compositionsByParts : ParamClass where
  toCombClass := CombClass.compositions
  param _ c := c.length

/-- Setting `u = 1` forgets the number-of-parts parameter and recovers the OGF
for integer compositions. -/
theorem ParamClass.evalU1_compositionsByParts :
    evalU 1 ParamClass.compositionsByParts.bgf = CombClass.compositions.ogf := by
  simpa [ParamClass.compositionsByParts] using
    ParamClass.evalU1_bgf ParamClass.compositionsByParts

end AnalyticCombinatorics.Ch1
