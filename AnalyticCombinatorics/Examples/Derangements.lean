import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Perm

open PowerSeries
open CombinatorialClass

namespace Nat

/-- Namespace bridge for Mathlib's derangement-counting sequence. -/
abbrev numDerangements : ℕ → ℕ := _root_.numDerangements

end Nat

/-- A derangement of size `n` is a fixed-point-free permutation of `Fin n`. -/
def derangementClass : CombinatorialClass where
  Obj := Σ n : ℕ, { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ :
      Set { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, σ⟩ hkσ
    simp only [Set.mem_setOf_eq] at hkσ
    change k = n at hkσ
    subst k
    exact ⟨σ, Set.mem_univ _, rfl⟩

namespace derangementClass

/-- Count of derangements of size `n` equals Mathlib's `Nat.numDerangements`. -/
theorem count_eq_numDerangements (n : ℕ) :
    derangementClass.count n = Nat.numDerangements n := by
  rw [CombinatorialClass.count]
  have hcard : (derangementClass.level n).card =
      (Finset.univ : Finset { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }).card := by
    refine Finset.card_bij'
      (s := derangementClass.level n)
      (t := (Finset.univ : Finset { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }))
      (fun x hx => by
        obtain ⟨k, σ⟩ := x
        have hsize : derangementClass.size ⟨k, σ⟩ = n :=
          (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨k, σ⟩).mp hx
        change k = n at hsize
        subst k
        exact σ)
      (fun σ _ => (⟨n, σ⟩ : derangementClass.Obj))
      ?_ ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro σ _
      exact (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨n, σ⟩).mpr rfl
    · intro x hx
      obtain ⟨k, σ⟩ := x
      have hsize : derangementClass.size ⟨k, σ⟩ = n :=
        (CombinatorialClass.level_mem_iff (C := derangementClass) ⟨k, σ⟩).mp hx
      change k = n at hsize
      subst k
      rfl
    · intro σ _
      rfl
  rw [hcard, Finset.card_univ]
  have htype :
      Fintype.card { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i } =
        Fintype.card (derangements (Fin n)) := by
    exact Fintype.card_congr
      { toFun := fun σ => ⟨σ.1, by
          show σ.1 ∈ derangements (Fin n)
          rw [derangements]
          exact σ.2⟩
        invFun := fun σ => ⟨σ.1, show ∀ i, σ.1 i ≠ i from σ.2⟩
        left_inv := by
          intro σ
          cases σ
          rfl
        right_inv := by
          intro σ
          cases σ
          rfl }
  rw [htype]
  exact card_derangements_fin_eq_numDerangements

end derangementClass

/-- Count of derangements of size `n` equals Mathlib's `Nat.numDerangements`. -/
theorem derangementClass_count_eq_numDerangements (n : ℕ) :
    derangementClass.count n = Nat.numDerangements n :=
  derangementClass.count_eq_numDerangements n

example : derangementClass.count 0 = 1 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 1 = 0 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 2 = 1 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 3 = 2 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 4 = 9 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 5 = 44 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 6 = 265 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 7 = 1854 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 8 = 14833 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 9 = 133496 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 10 = 1334961 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 11 = 14684570 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 12 = 176214841 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 13 = 2290792932 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 14 = 32071101049 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 15 = 481066515734 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 16 = 7697064251745 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 17 = 130850092279664 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 18 = 2355301661033953 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 19 = 44750731559645106 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 20 = 895014631192902121 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 21 = 18795307255050944540 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 22 = 413496759611120779881 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 23 = 9510425471055777937262 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example : derangementClass.count 24 = 228250211305338670494289 := by
  rw [derangementClass_count_eq_numDerangements]
  decide

example (n : ℕ) :
    derangementClass.egf.coeff n = (Nat.numDerangements n : ℚ) / n.factorial := by
  rw [CombinatorialClass.coeff_egf]
  rw [show (derangementClass.count n : ℕ) = Nat.numDerangements n from
        derangementClass_count_eq_numDerangements n]

example : derangementClass.ogf.coeff 0 = 1 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; rfl

example : derangementClass.ogf.coeff 1 = 0 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; rfl

example : derangementClass.ogf.coeff 4 = 9 := by
  rw [coeff_ogf, derangementClass_count_eq_numDerangements]; decide

/-- The normalized derangement numbers satisfy
    `D_{n+1}/(n+1)! - D_n/n! = (-1)^(n+1)/(n+1)!`. -/
lemma numDerangements_div_factorial_sub (n : ℕ) :
    (Nat.numDerangements (n + 1) : ℚ) / (n + 1).factorial -
      (Nat.numDerangements n : ℚ) / n.factorial =
      (-1 : ℚ) ^ (n + 1) / (n + 1).factorial := by
  have hZ := numDerangements_succ n
  have hQ : (Nat.numDerangements (n + 1) : ℚ) =
      ((n + 1 : ℕ) : ℚ) * (Nat.numDerangements n : ℚ) - (-1 : ℚ) ^ n := by
    exact_mod_cast hZ
  rw [hQ]
  rw [Nat.factorial_succ]
  norm_num
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne',
    show ((n : ℚ) + 1) ≠ 0 by positivity]
  ring_nf

/-- Coefficient form of `(1 - X) * derangementClass.egf = exp(-X)`. -/
lemma coeff_one_sub_X_mul_derangementClass_egf (n : ℕ) :
    coeff n ((1 - PowerSeries.X) * derangementClass.egf) =
      (-1 : ℚ) ^ n / n.factorial := by
  cases n with
  | zero =>
    rw [PowerSeries.coeff_mul]
    simp [CombinatorialClass.coeff_egf, derangementClass_count_eq_numDerangements]
  | succ n =>
    rw [sub_mul, one_mul, map_sub]
    rw [show PowerSeries.X * derangementClass.egf =
        PowerSeries.X ^ 1 * derangementClass.egf by rw [pow_one]]
    rw [PowerSeries.coeff_X_pow_mul']
    simp only [Nat.reduceLeDiff, ↓reduceIte, add_tsub_cancel_right]
    rw [CombinatorialClass.coeff_egf, CombinatorialClass.coeff_egf,
      derangementClass_count_eq_numDerangements, derangementClass_count_eq_numDerangements]
    exact numDerangements_div_factorial_sub n

/-- Coefficients of `exp(-X)`. -/
lemma coeff_evalNegHom_exp (n : ℕ) :
    coeff n (PowerSeries.evalNegHom (PowerSeries.exp ℚ)) =
      (-1 : ℚ) ^ n / n.factorial := by
  rw [PowerSeries.evalNegHom, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  simp [div_eq_mul_inv]

/-- Derangement EGF in reciprocal form: `(1 - X) D(X) = exp(-X)`. -/
theorem one_sub_X_mul_derangementClass_egf :
    (1 - PowerSeries.X) * derangementClass.egf =
      PowerSeries.evalNegHom (PowerSeries.exp ℚ) := by
  ext n
  rw [coeff_one_sub_X_mul_derangementClass_egf, coeff_evalNegHom_exp]

/-- Classical EGF identity: `D(X) * exp(X) = 1 / (1 - X)`,
    expressed here as equality with the permutation EGF. -/
theorem derangementClass_egf_mul_exp_eq_permClass_egf :
    derangementClass.egf * PowerSeries.exp ℚ = permClass.egf := by
  rw [permClass_egf_eq_mk_one]
  calc
    derangementClass.egf * PowerSeries.exp ℚ =
        (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) *
          ((1 - PowerSeries.X) * derangementClass.egf * PowerSeries.exp ℚ) := by
      rw [show (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) *
          ((1 - PowerSeries.X) * derangementClass.egf * PowerSeries.exp ℚ) =
            ((PowerSeries.mk fun _ : ℕ => (1 : ℚ)) * (1 - PowerSeries.X)) *
              (derangementClass.egf * PowerSeries.exp ℚ) by ring]
      have hgeom : (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) * (1 - PowerSeries.X) = 1 :=
        PowerSeries.mk_one_mul_one_sub_eq_one ℚ
      rw [hgeom, one_mul]
    _ = (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) *
          (PowerSeries.evalNegHom (PowerSeries.exp ℚ) * PowerSeries.exp ℚ) := by
      rw [one_sub_X_mul_derangementClass_egf]
    _ = (PowerSeries.mk fun _ : ℕ => (1 : ℚ)) * 1 := by
      rw [mul_comm (PowerSeries.evalNegHom (PowerSeries.exp ℚ)) (PowerSeries.exp ℚ),
        PowerSeries.exp_mul_exp_neg_eq_one]
    _ = PowerSeries.mk fun _ : ℕ => (1 : ℚ) := by
      rw [mul_one]

/-- Coefficient identity: numDerangements convolution with `1 / k!` gives `n! / n!`. -/
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (Nat.numDerangements (n - k) : ℚ) / (n - k).factorial / k.factorial = 1 := by
  have hmul : PowerSeries.exp ℚ * derangementClass.egf = permClass.egf := by
    rw [mul_comm, derangementClass_egf_mul_exp_eq_permClass_egf]
  have h : coeff n (PowerSeries.exp ℚ * derangementClass.egf) = coeff n permClass.egf := by
    simpa using congrArg (fun f : PowerSeries ℚ => coeff n f) hmul
  rw [permClass_egf_coeff] at h
  rw [PowerSeries.coeff_mul] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [PowerSeries.coeff_exp, CombinatorialClass.coeff_egf,
    derangementClass_count_eq_numDerangements] at h
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- Explicit intermediate form of the derangement EGF identity:
    `(1 - X) * D(X) = exp(-X)`.  Mathlib writes `exp(-X)` as
    `PowerSeries.evalNegHom (PowerSeries.exp ℚ)`. -/
example :
    (1 - PowerSeries.X) * derangementClass.egf =
      PowerSeries.evalNegHom (PowerSeries.exp ℚ) := by
  exact one_sub_X_mul_derangementClass_egf

/-- Derangement EGF closed form, in right-multiplied reciprocal form:
    `D(X) * (1 - X) = exp(-X)`.  Mathlib writes `exp(-X)` as
    `PowerSeries.evalNegHom (PowerSeries.exp ℚ)`. -/
theorem derangementClass_egf_mul_one_sub_X_eq_exp_neg :
    derangementClass.egf * (1 - PowerSeries.X) =
      PowerSeries.evalNegHom (PowerSeries.exp ℚ) := by
  rw [mul_comm, one_sub_X_mul_derangementClass_egf]

/-- Combined derangement EGF identity: `D(X) * exp(X) * (1 - X) = 1`. -/
theorem derangementClass_egf_mul_exp_mul_one_sub_X :
    derangementClass.egf * PowerSeries.exp ℚ * (1 - PowerSeries.X) = 1 := by
  rw [derangementClass_egf_mul_exp_eq_permClass_egf, permClass_egf_eq_mk_one]
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ

/-- Classical derangement recurrence. -/
theorem numDerangements_recurrence (n : ℕ) :
    Nat.numDerangements (n + 2) =
      (n + 1) * (Nat.numDerangements (n + 1) + Nat.numDerangements n) := by
  rw [Nat.numDerangements, numDerangements_add_two]
  rw [add_comm (numDerangements n) (numDerangements (n + 1))]

example : Nat.numDerangements 2 = 1 * (0 + 1) := by
  simpa using numDerangements_recurrence 0

example : Nat.numDerangements 3 = 2 * (1 + 0) := by
  simpa using numDerangements_recurrence 1

example : Nat.numDerangements 4 = 3 * (2 + 1) := by
  simpa using numDerangements_recurrence 2

example : Nat.numDerangements 5 = 4 * (9 + 2) := by
  simpa using numDerangements_recurrence 3

example : Nat.numDerangements 6 = 5 * (44 + 9) := by
  simpa using numDerangements_recurrence 4
