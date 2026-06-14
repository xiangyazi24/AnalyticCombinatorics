import Mathlib
import AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries
import AnalyticCombinatorics.Ch1.Lagrange.Residue
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeRecurrence
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryFussCatalan

/-!
# Ternary trees via Lagrange inversion

We close the ternary-tree Fuss–Catalan closed form
`ternaryCount n = C(3n, n) / (2n + 1) = ternaryTreeCount n`
through the banked Ch1 Lagrange inversion machinery, mirroring the Catalan
worked example `coeff_implicitSeries_one_add_X_sq` with a cube.

The generating function `B = ∑ ternaryCount n · zⁿ` satisfies `B = 1 + z·B³`, so
`T := B - 1` satisfies `T = z·(1 + T)³ = z·((1+X)³).subst T`. By
`implicitSeries_unique`, `T = implicitSeries ((1+X)³)`, whose `n`-th coefficient
(for `0 < n`) is `(1/n)·C(3n, n-1) = C(3n, n)/(2n+1)` by Lagrange inversion.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open PowerSeries
open AnalyticCombinatorics.Ch1.Lagrange
open scoped BigOperators

/-! ## Part B.1 — Lagrange coefficient of `implicitSeries ((1+X)³)` -/

/-- Public coefficient formula for `(1 + X)^m` over `ℚ⟦X⟧`. -/
lemma coeff_one_add_X_pow_rat (m k : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ m) = (((m.choose k : ℕ) : ℚ)) := by
  have hright : ((1 + X : ℚ⟦X⟧) ^ m) =
      ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- The exact `Nat` binomial identity behind the Fuss–Catalan reduction:
`n · C(3n, n) = (2n+1) · C(3n, n-1)`. -/
lemma nat_choose_three_pred_identity (n : ℕ) (hn : 0 < n) :
    n * Nat.choose (3 * n) n = (2 * n + 1) * Nat.choose (3 * n) (n - 1) := by
  have hchoose := Nat.choose_succ_right_eq (3 * n) (n - 1)
  -- hchoose : C(3n, n-1+1) * (n-1+1) = C(3n, n-1) * (3n - (n-1))
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
  rw [hsucc, hsub] at hchoose
  -- hchoose : C(3n, n) * n = C(3n, n-1) * (2n+1)
  rw [mul_comm n, mul_comm (2 * n + 1)]
  exact hchoose

/-- Rational form of the Lagrange coefficient as the Fuss–Catalan number. -/
lemma inv_natCast_mul_choose_three_pred_eq_choose_div (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * ((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)
      = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  have hnat := nat_choose_three_pred_identity n hn
  have hq : (n : ℚ) * ((Nat.choose (3 * n) n : ℕ) : ℚ)
      = ((2 * n + 1 : ℕ) : ℚ) * ((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hden : ((2 * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  linarith [hq]

/-- The implicit solution of `T = X · (1 + T)³` has Fuss–Catalan coefficients
`C(3n, n)/(2n+1)` for `0 < n`. Cube analogue of `coeff_implicitSeries_one_add_X_sq`. -/
theorem coeff_implicitSeries_one_add_X_cube (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧))
      = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  have hunit : IsUnit (constantCoeff (((1 + X) ^ 3 : ℚ⟦X⟧))) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (((1 + X) ^ 3 : ℚ⟦X⟧)) hunit n hn
  have hcoeff : coeff (n - 1) ((((1 + X) ^ 3 : ℚ⟦X⟧) ^ n))
      = (((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)) := by
    have hpow : ((((1 + X) ^ 3 : ℚ⟦X⟧) ^ n) = (1 + X : ℚ⟦X⟧) ^ (3 * n)) := by
      rw [← pow_mul]
    rw [hpow]
    exact coeff_one_add_X_pow_rat (3 * n) (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧))
        = (n : ℚ)⁻¹ * (((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)) := by
          simpa using hlag
    _ = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) :=
          inv_natCast_mul_choose_three_pred_eq_choose_div n hn

#print axioms coeff_implicitSeries_one_add_X_cube

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
