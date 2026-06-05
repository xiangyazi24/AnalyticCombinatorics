import Mathlib

/-!
# Implicit formal power series

This file constructs, coefficient by coefficient, the unique formal power
series `T` with zero constant term satisfying `T = X * φ.subst T`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

variable {R : Type*} [CommRing R]

namespace ImplicitSeries

lemma trunc_eq_of_coeff_eq {f g : R⟦X⟧} {n : ℕ}
    (h : ∀ i, i < n → coeff i f = coeff i g) :
    trunc n f = trunc n g := by
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma coeff_eq_coeff_trunc_pow (f : R⟦X⟧) (n d : ℕ) :
    coeff n (f ^ d) = coeff n (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d) := by
  symm
  rw [← coeff_coe_trunc_of_lt (n := n) (m := n + 1)
    (f := (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d)) (Nat.lt_succ_self n)]
  rw [PowerSeries.trunc_trunc_pow]
  rw [coeff_coe_trunc_of_lt (n := n) (m := n + 1) (f := f ^ d) (Nat.lt_succ_self n)]

lemma coeff_subst_eq_of_coeff_eq {f g : R⟦X⟧} (hf : PowerSeries.HasSubst f)
    (hg : PowerSeries.HasSubst g) (φ : R⟦X⟧) {n : ℕ}
    (h : ∀ i, i ≤ n → coeff i f = coeff i g) :
    coeff n (φ.subst f) = coeff n (φ.subst g) := by
  rw [PowerSeries.coeff_subst' hf φ n, PowerSeries.coeff_subst' hg φ n]
  apply finsum_congr
  intro d
  congr 1
  rw [coeff_eq_coeff_trunc_pow f n d, coeff_eq_coeff_trunc_pow g n d]
  congr 1
  exact congrArg (fun p : Polynomial R => ((p : R⟦X⟧) ^ d)) <|
    trunc_eq_of_coeff_eq (f := f) (g := g) (n := n + 1) fun i hi =>
      h i (Nat.le_of_lt_succ hi)

def partialSeries (a : ℕ → R) (n : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun k => if k < n then a k else 0

@[simp]
lemma coeff_partialSeries (a : ℕ → R) (n k : ℕ) :
    coeff k (partialSeries (R := R) a n) = if k < n then a k else 0 := by
  simp [partialSeries]

def implicitStep (φ : R⟦X⟧) (n : ℕ) (rec : ∀ k, k < n → R) : R :=
  match n with
  | 0 => 0
  | m + 1 =>
      coeff m (φ.subst (partialSeries (fun k => if h : k < m + 1 then rec k h else 0) (m + 1)))

def implicitCoeff (φ : R⟦X⟧) : ℕ → R :=
  Nat.strongRec (implicitStep φ)

def implicitSeries (φ : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk (implicitCoeff φ)

@[simp]
theorem coeff_implicitSeries (φ : R⟦X⟧) (n : ℕ) :
    coeff n (implicitSeries φ) = implicitCoeff φ n := by
  simp [implicitSeries]

@[simp]
theorem implicitCoeff_zero (φ : R⟦X⟧) :
    implicitCoeff φ 0 = 0 := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]

theorem implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    implicitCoeff φ (n + 1) =
      coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]
  congr 2
  ext k
  by_cases hk : k < n + 1
  · simp only [coeff_partialSeries, hk, ↓reduceIte]
    rfl
  · simp only [coeff_partialSeries, hk, ↓reduceIte]

@[simp]
theorem constantCoeff_partialSeries_succ (a : ℕ → R) (n : ℕ) (h0 : a 0 = 0) :
    constantCoeff (partialSeries (R := R) a (n + 1)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [h0]

@[simp]
theorem constantCoeff_implicitSeries (φ : R⟦X⟧) :
    constantCoeff (implicitSeries φ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

theorem hasSubst_implicitSeries (φ : R⟦X⟧) :
    PowerSeries.HasSubst (implicitSeries φ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_implicitSeries φ)

theorem hasSubst_partialSeries_implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    PowerSeries.HasSubst (partialSeries (implicitCoeff φ) (n + 1)) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (constantCoeff_partialSeries_succ (R := R) (implicitCoeff φ) n (implicitCoeff_zero φ))

theorem coeff_subst_partialSeries_implicitCoeff (φ : R⟦X⟧) (n : ℕ) :
    coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) =
      coeff n (φ.subst (implicitSeries φ)) := by
  apply coeff_subst_eq_of_coeff_eq
      (hasSubst_partialSeries_implicitCoeff_succ φ n) (hasSubst_implicitSeries φ)
  intro i hi
  simp [coeff_implicitSeries, hi]

theorem implicitSeries_spec (φ : R⟦X⟧) :
    implicitSeries φ = X * φ.subst (implicitSeries φ) := by
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
      rw [coeff_implicitSeries, implicitCoeff_succ, coeff_succ_X_mul]
      exact coeff_subst_partialSeries_implicitCoeff φ n

theorem derivative_implicitSeries (φ : R⟦X⟧) :
    d⁄dX R (implicitSeries φ) =
      φ.subst (implicitSeries φ) +
        X * ((d⁄dX R φ).subst (implicitSeries φ) * d⁄dX R (implicitSeries φ)) := by
  have h := congrArg (fun f : R⟦X⟧ => d⁄dX R f) (implicitSeries_spec φ)
  simpa [PowerSeries.derivative_subst R (hasSubst_implicitSeries φ), smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm, add_comm] using h

theorem implicitSeries_unique (φ T : R⟦X⟧)
    (hT : T = X * φ.subst T) (h0 : constantCoeff T = 0) :
    T = implicitSeries φ := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [coeff_implicitSeries, implicitCoeff_zero, coeff_zero_eq_constantCoeff_apply, h0]
      | succ n =>
          have hsubst : coeff n (φ.subst T) =
              coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
            apply coeff_subst_eq_of_coeff_eq
              (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
              (hasSubst_partialSeries_implicitCoeff_succ φ n)
            intro i hi
            have hlt : i < n + 1 := Nat.lt_succ_of_le hi
            have ih_i : coeff i T = coeff i (implicitSeries φ) := ih i hlt
            simp [coeff_implicitSeries, hlt, ih_i]
          have hcoeff := congrArg (coeff (n + 1)) hT
          rw [coeff_succ_X_mul] at hcoeff
          rw [coeff_implicitSeries, implicitCoeff_succ, ← hsubst, ← hcoeff]

section Sanity

def geometricTail : R⟦X⟧ :=
  X * (PowerSeries.mk fun _ => (1 : R))

@[simp]
theorem constantCoeff_geometricTail :
    constantCoeff (geometricTail (R := R)) = 0 := by
  rw [geometricTail, ← coeff_zero_eq_constantCoeff_apply]
  simp

theorem subst_one_add_X_geometricTail :
    (1 + X : R⟦X⟧).subst (geometricTail (R := R)) =
      1 + geometricTail := by
  let hgt : PowerSeries.HasSubst (geometricTail (R := R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_geometricTail (R := R))
  rw [PowerSeries.subst_add hgt]
  rw [PowerSeries.subst_X hgt]
  have hone : (1 : R⟦X⟧).subst (geometricTail (R := R)) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hgt]
    exact map_one (PowerSeries.substAlgHom hgt)
  rw [hone]

theorem geometricTail_spec_one_add_X :
    geometricTail (R := R) =
      X * (1 + X : R⟦X⟧).subst (geometricTail (R := R)) := by
  rw [subst_one_add_X_geometricTail]
  ext n
  cases n with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, geometricTail]
  | succ n =>
      rw [geometricTail, coeff_succ_X_mul, coeff_succ_X_mul]
      cases n with
      | zero => simp
      | succ n => simp

theorem implicitSeries_one_add_X_eq_geometricTail :
    implicitSeries (1 + X : R⟦X⟧) = geometricTail (R := R) := by
  symm
  exact implicitSeries_unique (φ := (1 + X : R⟦X⟧)) (T := geometricTail)
    geometricTail_spec_one_add_X constantCoeff_geometricTail

theorem coeff_implicitSeries_one_add_X_of_pos (n : ℕ) (hn : 0 < n) :
    coeff n (implicitSeries (1 + X : R⟦X⟧)) = 1 := by
  cases n with
  | zero => cases hn
  | succ n =>
      rw [implicitSeries_one_add_X_eq_geometricTail, geometricTail, coeff_succ_X_mul]
      simp

end Sanity

end ImplicitSeries

end AnalyticCombinatorics.Ch1.Lagrange
