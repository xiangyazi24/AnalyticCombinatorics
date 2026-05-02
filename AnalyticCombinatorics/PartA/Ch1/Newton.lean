/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I Appendix: Newton bootstrapping for power series.

  This file records the coefficient-level Newton principle for the Catalan
  equation
      T = 1 + z T^2.
  The core point is that the functional equation determines each coefficient
  from earlier ones, so satisfying the equation modulo `X^N` determines the
  first `N` coefficients.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-! ## Truncation and finite agreement -/

/-- Keep the coefficients of order `< n` and discard the rest. -/
noncomputable def trunc (f : PowerSeries ℕ) (n : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun k => if k < n then coeff k f else 0

theorem coeff_trunc (f : PowerSeries ℕ) (n k : ℕ) :
    coeff k (trunc f n) = if k < n then coeff k f else 0 := by
  rw [trunc, PowerSeries.coeff_mk]

/-- Two power series agree through all coefficients of order `< n`. -/
def agreeUpTo (f g : PowerSeries ℕ) (n : ℕ) : Prop :=
  ∀ k < n, coeff k f = coeff k g

theorem agreeUpTo_refl (f : PowerSeries ℕ) (n : ℕ) : agreeUpTo f f n := by
  intro k _
  rfl

theorem trunc_agreeUpTo (f : PowerSeries ℕ) (n : ℕ) : agreeUpTo (trunc f n) f n := by
  intro k hk
  rw [coeff_trunc, if_pos hk]

/-! ## Catalan coefficient bootstrapping -/

private theorem catalan_coeff_eq_of_functional_prefix
    (f : PowerSeries ℕ) (N : ℕ)
    (hfunc : agreeUpTo f (1 + X * f ^ 2) N) :
    agreeUpTo f binaryTreeClass.ogf N := by
  intro k hkN
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          have hf0 := hfunc 0 hkN
          rw [hf0, binaryTree_ogf_eq]
          simp
      | succ k =>
          have hfsucc := hfunc (k + 1) hkN
          rw [hfsucc, binaryTree_ogf_eq]
          simp only [map_add, coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
            PowerSeries.coeff_succ_X_mul]
          rw [pow_two, PowerSeries.coeff_mul, pow_two, PowerSeries.coeff_mul]
          apply Finset.sum_congr rfl
          intro p hp
          have hsum : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
          have hp1 : p.1 < k + 1 := by omega
          have hp2 : p.2 < k + 1 := by omega
          have hp1N : p.1 < N := by omega
          have hp2N : p.2 < N := by omega
          rw [ih p.1 hp1 hp1N, ih p.2 hp2 hp2N]

/--
If a series agrees with the Catalan OGF through order `n`, and its own
functional equation is correct through order `2n`, then the agreement
bootstraps through order `2n`.
-/
theorem catalan_bootstrap (f : PowerSeries ℕ) (n : ℕ)
    (_hagree : agreeUpTo f binaryTreeClass.ogf n)
    (hfunc : agreeUpTo f (1 + X * f ^ 2) (2 * n)) :
    agreeUpTo f binaryTreeClass.ogf (2 * n) :=
  catalan_coeff_eq_of_functional_prefix f (2 * n) hfunc

/-! ## First finite iterates -/

/-- The zeroth Catalan approximation: `T₀ = 1`. -/
noncomputable def catalanIter0 : PowerSeries ℕ := 1

/-- The first Catalan approximation: `T₁ = 1 + z`. -/
noncomputable def catalanIter1 : PowerSeries ℕ := 1 + X

/-- The second Catalan approximation through order four: `T₂ = 1 + z + 2z² + 5z³`. -/
noncomputable def catalanIter2 : PowerSeries ℕ :=
  PowerSeries.mk fun k =>
    if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 else if k = 3 then 5 else 0

theorem catalanIter0_agree : agreeUpTo catalanIter0 binaryTreeClass.ogf 1 := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simp [catalanIter0, CombinatorialClass.coeff_ogf, binaryTree_count_zero]

theorem catalanIter1_agree : agreeUpTo catalanIter1 binaryTreeClass.ogf 2 := by
  intro k hk
  have hk_cases : k = 0 ∨ k = 1 := by omega
  rcases hk_cases with rfl | rfl <;>
    simp [catalanIter1, CombinatorialClass.coeff_ogf, binaryTree_count_zero,
      binaryTree_count_one]

theorem catalanIter2_agree : agreeUpTo catalanIter2 binaryTreeClass.ogf 4 := by
  intro k hk
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl <;>
    simp [catalanIter2, CombinatorialClass.coeff_ogf, binaryTree_count_zero,
      binaryTree_count_one, binaryTree_count_two, binaryTree_count_three]

/-! ## Uniqueness of the Catalan root -/

/-- The Catalan functional equation uniquely characterizes the binary-tree OGF. -/
theorem catalan_ogf_unique (f : PowerSeries ℕ) (hf : f = 1 + X * f ^ 2)
    (_h0 : coeff 0 f = 1) : f = binaryTreeClass.ogf := by
  ext n
  exact catalan_coeff_eq_of_functional_prefix f (n + 1)
    (by
      intro k _
      exact congrArg (fun s : PowerSeries ℕ => coeff k s) hf)
    n (Nat.lt_succ_self n)
