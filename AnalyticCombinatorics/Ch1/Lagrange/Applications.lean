import Mathlib
import AnalyticCombinatorics.Ch1.Lagrange.ImplicitSeries
import AnalyticCombinatorics.Ch1.Lagrange.Residue

/-!
# Applications of Lagrange inversion

This file records the Catalan and Cayley coefficient formulas obtained from
the formal Lagrange inversion theorem.
-/

noncomputable section

namespace Nat

export _root_ (catalan)

end Nat

namespace AnalyticCombinatorics.Ch1.Lagrange.Applications

open PowerSeries

private lemma nat_mul_catalan_eq_choose_pred (n : ℕ) (hn : 0 < n) :
    n * Nat.catalan n = (2 * n).choose (n - 1) := by
  apply Nat.mul_left_cancel (Nat.succ_pos n)
  calc
    (n + 1) * (n * Nat.catalan n) = n * ((n + 1) * Nat.catalan n) := by ring
    _ = n * n.centralBinom := by rw [succ_mul_catalan_eq_centralBinom]
    _ = (2 * n).choose (n - 1) * (n + 1) := by
      have hchoose := Nat.choose_succ_right_eq (2 * n) (n - 1)
      have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
      have hsub : 2 * n - (n - 1) = n + 1 := by omega
      rw [hsucc, hsub] at hchoose
      simpa [Nat.centralBinom, mul_comm, mul_left_comm, mul_assoc] using hchoose
    _ = (n + 1) * ((2 * n).choose (n - 1)) := by ring

private lemma inv_natCast_mul_choose_pred_eq_catalan (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) = (Nat.catalan n : ℚ) := by
  have hnat := nat_mul_catalan_eq_choose_pred n hn
  have hq : (n : ℚ) * (Nat.catalan n : ℚ) =
      (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) =
        (n : ℚ)⁻¹ * ((n : ℚ) * (Nat.catalan n : ℚ)) := by rw [← hq]
    _ = (Nat.catalan n : ℚ) := by field_simp [hnq]

private lemma coeff_one_add_X_pow_rat (m k : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ m) = (((m.choose k : ℕ) : ℚ)) := by
  have hright : ((1 + X : ℚ⟦X⟧) ^ m) =
      ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- The implicit solution of `T = X * (1 + T)^2` has Catalan coefficients. -/
theorem coeff_implicitSeries_one_add_X_sq (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries ((1 + X)^2 : ℚ⟦X⟧)) = Nat.catalan n := by
  have hunit : IsUnit (constantCoeff (((1 + X) ^ 2 : ℚ⟦X⟧))) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (((1 + X) ^ 2 : ℚ⟦X⟧)) hunit n hn
  have hcoeff : coeff (n - 1) ((((1 + X) ^ 2 : ℚ⟦X⟧) ^ n)) =
      (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
    have hpow : ((((1 + X) ^ 2 : ℚ⟦X⟧) ^ n) = (1 + X : ℚ⟦X⟧) ^ (2 * n)) := by
      rw [pow_mul]
    rw [hpow]
    exact coeff_one_add_X_pow_rat (2 * n) (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries ((1 + X)^2 : ℚ⟦X⟧)) =
        (n : ℚ)⁻¹ * (((2 * n).choose (n - 1) : ℕ) : ℚ) := by
      simpa using hlag
    _ = (Nat.catalan n : ℚ) := inv_natCast_mul_choose_pred_eq_catalan n hn

private lemma coeff_exp_pow_rat (n k : ℕ) :
    coeff k ((PowerSeries.exp ℚ) ^ n) = (n : ℚ) ^ k / k.factorial := by
  rw [PowerSeries.exp_pow_eq_rescale_exp]
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

private lemma inv_natCast_mul_pow_div_pred_factorial (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * ((n : ℚ) ^ (n - 1) / (n - 1).factorial) =
      (n : ℚ) ^ (n - 1) / n.factorial := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hfact_nat : n.factorial = n * (n - 1).factorial := by
    calc
      n.factorial = ((n - 1) + 1).factorial := by rw [Nat.sub_add_cancel hn]
      _ = ((n - 1) + 1) * (n - 1).factorial := Nat.factorial_succ (n - 1)
      _ = n * (n - 1).factorial := by rw [Nat.sub_add_cancel hn]
  have hfact : (n.factorial : ℚ) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    exact_mod_cast hfact_nat
  rw [hfact]
  field_simp [hnq]

/--
The implicit solution of `T = X * exp T` has Cayley rooted-tree coefficients.
This matches the analytic coefficient formula in `TreeFunctionNS`.
-/
theorem coeff_implicitSeries_exp (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries (PowerSeries.exp ℚ)) =
      (n : ℚ) ^ (n - 1) / n.factorial := by
  have hunit : IsUnit (constantCoeff (PowerSeries.exp ℚ)) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (PowerSeries.exp ℚ) hunit n hn
  have hcoeff : coeff (n - 1) ((PowerSeries.exp ℚ) ^ n) =
      (n : ℚ) ^ (n - 1) / (n - 1).factorial := by
    exact coeff_exp_pow_rat n (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries (PowerSeries.exp ℚ)) =
        (n : ℚ)⁻¹ * ((n : ℚ) ^ (n - 1) / (n - 1).factorial) := by
      simpa using hlag
    _ = (n : ℚ) ^ (n - 1) / n.factorial :=
      inv_natCast_mul_pow_div_pred_factorial n hn

end AnalyticCombinatorics.Ch1.Lagrange.Applications
