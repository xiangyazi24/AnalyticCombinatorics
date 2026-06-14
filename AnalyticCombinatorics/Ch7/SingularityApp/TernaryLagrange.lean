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

/-! ## Part B.2 — connect `ternaryCount` to `implicitSeries ((1+X)³)` -/

/-- The generating function of `ternaryCount` over `ℚ⟦X⟧`. -/
noncomputable def ternaryGF : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (ternaryCount n : ℚ)

/-- The shifted series `T = B - 1`, with vanishing constant term. -/
noncomputable def ternaryT : ℚ⟦X⟧ :=
  ternaryGF - 1

@[simp] lemma coeff_ternaryGF (n : ℕ) :
    coeff n ternaryGF = (ternaryCount n : ℚ) := by
  simp [ternaryGF]

@[simp] lemma constantCoeff_ternaryGF :
    constantCoeff ternaryGF = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ternaryGF, ternaryCount_zero]
  norm_num

/-- Reshape the nested antidiagonal double sum (from two `coeff_mul`s) into the
`TripleIndex` sum used by the banked `ternaryCount_succ` recurrence. -/
lemma tripleIndex_sum_eq_nested_antidiag {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : ℕ → ℕ → ℕ → M) :
    ∑ p : TripleIndex n, g p.val.1 p.val.2.1 p.val.2.2 =
      ∑ x ∈ Finset.antidiagonal n,
        ∑ y ∈ Finset.antidiagonal x.2, g x.1 y.1 y.2 := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun p _ => (⟨(p.val.1, p.val.2.1 + p.val.2.2), (p.val.2.1, p.val.2.2)⟩ :
      (_ : ℕ × ℕ) × ℕ × ℕ))
    (j := fun s hs => (⟨(s.1.1, s.2.1, s.2.2), by
      rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at hs
      obtain ⟨h1, h2⟩ := hs
      change s.1.1 + s.2.1 + s.2.2 = n
      omega⟩ : TripleIndex n))
    ?hi ?hj ?left ?right ?h
  case hi =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    simp only at hp
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · change a + (b + c) = n; omega
    · rfl
  case hj =>
    rintro s hs
    exact Finset.mem_univ _
  case left =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    rfl
  case right =>
    rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩ hs
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at hs
    obtain ⟨h1, h2⟩ := hs
    -- goal: i (j s) = s, i.e. ((a, b+c), (b,c)) = ((a,d),(b,c)) ; need b+c = d
    have hd : b + c = d := h2
    subst hd
    rfl
  case h =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    rfl

/-- The triple-convolution coefficient of the cube of the generating function,
matching the banked `ternaryCount_succ` recurrence indexed by `TripleIndex`. -/
lemma coeff_ternaryGF_cube (n : ℕ) :
    coeff n (ternaryGF ^ 3) =
      ∑ p : TripleIndex n,
        (ternaryCount p.val.1 : ℚ) *
        (ternaryCount p.val.2.1 : ℚ) *
        (ternaryCount p.val.2.2 : ℚ) := by
  classical
  have hpow : ternaryGF ^ 3 = ternaryGF * (ternaryGF * ternaryGF) := by ring
  rw [hpow, PowerSeries.coeff_mul]
  rw [tripleIndex_sum_eq_nested_antidiag n
    (fun a b c => (ternaryCount a : ℚ) * (ternaryCount b : ℚ) * (ternaryCount c : ℚ))]
  apply Finset.sum_congr rfl
  intro x _
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [coeff_ternaryGF]
  ring

lemma ternaryGF_spec :
    ternaryGF = 1 + X * ternaryGF ^ 3 := by
  ext n
  cases n with
  | zero =>
      simp [coeff_ternaryGF, ternaryCount_zero]
  | succ m =>
      rw [map_add, PowerSeries.coeff_succ_X_mul, coeff_ternaryGF,
        ternaryCount_succ, coeff_ternaryGF_cube]
      push_cast
      simp [mul_assoc]

lemma constantCoeff_ternaryT :
    constantCoeff ternaryT = 0 := by
  rw [ternaryT, map_sub, constantCoeff_ternaryGF]
  simp

lemma ternaryGF_eq_one_add_ternaryT :
    ternaryGF = 1 + ternaryT := by
  rw [ternaryT]; ring

lemma ternaryT_spec :
    ternaryT = X * (((1 + X) ^ 3 : ℚ⟦X⟧).subst ternaryT) := by
  have hT0 : constantCoeff ternaryT = 0 := constantCoeff_ternaryT
  have hSubst : PowerSeries.HasSubst ternaryT :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  have hsubst : ((1 + X) ^ 3 : ℚ⟦X⟧).subst ternaryT = (1 + ternaryT) ^ 3 := by
    rw [PowerSeries.subst_pow hSubst, PowerSeries.subst_add hSubst,
      PowerSeries.subst_X hSubst]
    congr 2
    rw [← PowerSeries.coe_substAlgHom hSubst]
    exact map_one (PowerSeries.substAlgHom hSubst)
  rw [hsubst, ← ternaryGF_eq_one_add_ternaryT]
  -- goal: ternaryT = X * ternaryGF^3
  -- from hB: ternaryGF = 1 + X*ternaryGF^3, and ternaryT = ternaryGF - 1
  rw [ternaryT]
  have hB := ternaryGF_spec
  linear_combination hB

lemma ternaryT_eq_implicit_cube :
    ternaryT = ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧) :=
  ImplicitSeries.implicitSeries_unique
    ((1 + X) ^ 3 : ℚ⟦X⟧) ternaryT ternaryT_spec constantCoeff_ternaryT

lemma ternaryCount_eq_coeff_implicit_cube (n : ℕ) (hn : 0 < n) :
    (ternaryCount n : ℚ) =
      coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧)) := by
  rw [← ternaryT_eq_implicit_cube, ternaryT, map_sub, coeff_ternaryGF]
  have hone : coeff n (1 : ℚ⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_one]
    simp [Nat.ne_of_gt hn]
  rw [hone, sub_zero]

/-! ## Part B.3 — final Fuss–Catalan closed form + connection to `ternaryTreeCount` -/

/-- Rational closed form: `ternaryCount n = C(3n,n)/(2n+1)`. -/
theorem ternaryCount_eq_fussCatalan_rat (n : ℕ) :
    (ternaryCount n : ℚ) =
      ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  cases n with
  | zero =>
      simp [ternaryCount_zero]
  | succ m =>
      have hn : 0 < m + 1 := Nat.succ_pos m
      rw [ternaryCount_eq_coeff_implicit_cube (m + 1) hn,
        coeff_implicitSeries_one_add_X_cube (m + 1) hn]

/-- The main connection: the recursive species count `ternaryCount` equals the
banked Fuss–Catalan count `ternaryTreeCount`. CLOSES Part B. -/
theorem ternaryCount_eq_ternaryTreeCount (n : ℕ) :
    ternaryCount n = _root_.ternaryTreeCount n := by
  have hq : (ternaryCount n : ℚ) = (_root_.ternaryTreeCount n : ℚ) := by
    rw [ternaryCount_eq_fussCatalan_rat, ternaryTreeCount_eq_fc_one, fc_one_eq_ternary]
    norm_num
  exact_mod_cast hq

#print axioms ternaryCount_eq_ternaryTreeCount

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
