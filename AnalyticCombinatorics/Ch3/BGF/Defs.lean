import AnalyticCombinatorics.Ch1.OGF.Product
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Ch3 -- Bivariate generating functions for parameters

This file opens Chapter III with parameterized combinatorial classes.  The BGF
representation is `PowerSeries (Polynomial ℚ)`: the outer power series variable
is size (`z`), while the inner polynomial variable records the parameter (`u`).
For each fixed size the parameter support is finite because the size fiber is
finite.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- A combinatorial class equipped with a natural-valued parameter on each
fixed-size fiber. -/
structure ParamClass extends CombClass where
  /-- The parameter value of an object of size `n`. -/
  param : ∀ n, Obj n → ℕ

/-- Bivariate counts: objects of size `n` whose parameter has value `k`. -/
noncomputable def ParamClass.bcounts (C : ParamClass) (n k : ℕ) : ℕ :=
  Fintype.card {x : C.Obj n // C.param n x = k}

/-- The fixed-size parameter polynomial `∑_x u^χ(x)`. -/
noncomputable def ParamClass.paramPoly (C : ParamClass) (n : ℕ) : ℚ[X] :=
  ∑ x : C.Obj n, (Polynomial.X : ℚ[X]) ^ C.param n x

/-- The bivariate generating function, represented as `ℚ[u]⟦z⟧`. -/
noncomputable def ParamClass.bgf (C : ParamClass) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => C.paramPoly n

/-- Coefficients of the BGF are exactly the bivariate counts. -/
@[simp] theorem ParamClass.coeff_bgf (C : ParamClass) (n k : ℕ) :
    (PowerSeries.coeff n C.bgf).coeff k = (C.bcounts n k : ℚ) := by
  classical
  rw [ParamClass.bgf, PowerSeries.coeff_mk, ParamClass.paramPoly, ParamClass.bcounts]
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole, Fintype.card_subtype]
  apply congrArg (fun s : Finset (C.Obj n) => (s.card : ℚ))
  ext x
  simpa using (eq_comm : k = C.param n x ↔ C.param n x = k)

/-- Disjoint sum of parameterized classes, preserving the side parameter. -/
def ParamClass.sum (A B : ParamClass) : ParamClass where
  Obj n := A.Obj n ⊕ B.Obj n
  finObj _ := inferInstance
  param n := Sum.elim (A.param n) (B.param n)

@[simp] lemma ParamClass.paramPoly_sum (A B : ParamClass) (n : ℕ) :
    (A.sum B).paramPoly n = A.paramPoly n + B.paramPoly n := by
  classical
  rw [ParamClass.paramPoly, ParamClass.paramPoly, ParamClass.paramPoly]
  change (∑ x : A.Obj n ⊕ B.Obj n,
      (Polynomial.X : ℚ[X]) ^ Sum.elim (A.param n) (B.param n) x) = _
  rw [Fintype.sum_sum_type]
  rfl

/-- BGF transfer theorem for disjoint sum. -/
theorem ParamClass.bgf_sum (A B : ParamClass) :
    (A.sum B).bgf = A.bgf + B.bgf := by
  apply PowerSeries.ext
  intro n
  simp [ParamClass.bgf]

/-- Cartesian product of parameterized classes, with additive size and
additive parameter. -/
def ParamClass.prod (A B : ParamClass) : ParamClass where
  Obj n := Σ i : Fin (n + 1), A.Obj i × B.Obj (n - i)
  finObj _ := inferInstance
  param n x := A.param x.1 x.2.1 + B.param (n - x.1) x.2.2

@[simp] lemma ParamClass.paramPoly_prod (A B : ParamClass) (n : ℕ) :
    (A.prod B).paramPoly n =
      ∑ i : Fin (n + 1), A.paramPoly i * B.paramPoly (n - i) := by
  classical
  rw [ParamClass.paramPoly]
  change (∑ x : Σ i : Fin (n + 1), A.Obj i × B.Obj (n - i),
      (Polynomial.X : ℚ[X]) ^
        (A.param x.1 x.2.1 + B.param (n - x.1) x.2.2)) = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ParamClass.paramPoly, ParamClass.paramPoly]
  rw [Fintype.sum_prod_type]
  change (∑ a : A.Obj i, ∑ b : B.Obj (n - i),
      (Polynomial.X : ℚ[X]) ^ (A.param i a + B.param (n - i) b)) =
    (∑ a : A.Obj i, (Polynomial.X : ℚ[X]) ^ A.param i a) *
      ∑ b : B.Obj (n - i), (Polynomial.X : ℚ[X]) ^ B.param (n - i) b
  rw [Fintype.sum_mul_sum]
  simp [pow_add]

/-- BGF transfer theorem for Cartesian product. -/
theorem ParamClass.bgf_prod (A B : ParamClass) :
    (A.prod B).bgf = A.bgf * B.bgf := by
  apply PowerSeries.ext
  intro n
  rw [ParamClass.bgf, PowerSeries.coeff_mk, ParamClass.paramPoly_prod]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Fin.sum_univ_eq_sum_range (fun k => A.paramPoly k * B.paramPoly (n - k)) (n + 1)]
  simp [ParamClass.bgf]

/-- Evaluate the parameter variable `u` while leaving the size variable formal. -/
noncomputable def evalU (a : ℚ) : ℚ[X]⟦X⟧ →+* ℚ⟦X⟧ :=
  PowerSeries.map (Polynomial.evalRingHom a)

/-- Evaluating a BGF at `u = 1` recovers the underlying OGF. -/
theorem ParamClass.evalU1_bgf (C : ParamClass) :
    evalU 1 C.bgf = C.toCombClass.ogf := by
  apply PowerSeries.ext
  intro n
  simp [evalU, ParamClass.bgf, ParamClass.paramPoly, CombClass.coeff_ogf,
    CombClass.counts]

end AnalyticCombinatorics.Ch1
