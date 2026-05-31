import AnalyticCombinatorics.Ch3.BGF.Moments
import AnalyticCombinatorics.Ch1.OGF.Compositions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Ch3 -- Variance and bivariate composition facts

The second factorial moment differentiates twice in the parameter variable.
Adding the first factorial moment gives the second raw moment, hence the usual
variance formula for any parameterized class.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Second factorial moment series: differentiate twice in `u`, then set
`u = 1`. -/
noncomputable def factorialMoment2 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv (uDeriv F))

/-- The second factorial moment coefficient is the cumulative `p(p-1)` on the
size-`n` fiber. -/
theorem ParamClass.coeff_factorialMoment2 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (factorialMoment2 C.bgf) =
      ∑ x : C.Obj n, (C.param n x : ℚ) * ((C.param n x : ℚ) - 1) := by
  classical
  simp [factorialMoment2, evalU, uDeriv, ParamClass.bgf, ParamClass.paramPoly,
    Polynomial.derivative_X_pow]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : C.param n x = 0
  · simp [hp]
  · have hp1 : 1 ≤ C.param n x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp)
    rw [Nat.cast_sub hp1]
    ring

/-- Second raw moment series: `E[p(p-1)] + E[p]` before normalization. -/
noncomputable def rawMoment2 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv (uDeriv F) + uDeriv F)

/-- The second raw moment coefficient is the cumulative square of the
parameter on the size-`n` fiber. -/
theorem ParamClass.coeff_rawMoment2 (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (rawMoment2 C.bgf) =
      ∑ x : C.Obj n, (C.param n x : ℚ) ^ 2 := by
  classical
  rw [rawMoment2, map_add]
  change PowerSeries.coeff n (factorialMoment2 C.bgf + factorialMoment1 C.bgf) =
    ∑ x : C.Obj n, (C.param n x : ℚ) ^ 2
  rw [map_add, ParamClass.coeff_factorialMoment2, ParamClass.coeff_factorialMoment1,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Variance of the parameter on the size-`n` fiber. -/
noncomputable def ParamClass.variance (C : ParamClass) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (rawMoment2 C.bgf) / (C.toCombClass.counts n : ℚ) - C.mean n ^ 2

/-- The variance is the normalized second raw moment minus the squared mean. -/
theorem ParamClass.variance_eq (C : ParamClass) (n : ℕ) :
    C.variance n =
      (∑ x : C.Obj n, (C.param n x : ℚ) ^ 2) / (C.toCombClass.counts n : ℚ) -
        C.mean n ^ 2 := by
  rw [ParamClass.variance, ParamClass.coeff_rawMoment2]

/-- Under Mathlib's boundary-set equivalence, a nonempty composition has one
more part than the number of interior boundary points. -/
private lemma compositionAsSetEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionAsSetEquiv n).symm s).length) = s.card + 1 := by
  let e : Fin (n - 1) ↪ Fin (n + 1) :=
    ⟨fun j => ⟨(j : ℕ) + 1, by omega⟩, by
      intro a b hab
      ext
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hab
      simp at this
      omega⟩
  let p : Fin (n + 1) → Prop :=
    fun i => i = 0 ∨ i = Fin.last n ∨ ∃ j ∈ s, (i : ℕ) = (j : ℕ) + 1
  have hset : (Finset.univ.filter p) = insert 0 (insert (Fin.last n) (s.map e)) := by
    ext i
    constructor
    · intro hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p] at hi
      rcases hi with h0 | hlast | ⟨j, hj, hval⟩
      · simp [h0]
      · simp [hlast]
      · rw [Finset.mem_insert, Finset.mem_insert]
        right
        right
        exact Finset.mem_map.mpr ⟨j, hj, by
          ext
          simp [e, hval]⟩
    · intro hi
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p]
      rcases hi with h0 | hlast | himage
      · exact Or.inl h0
      · exact Or.inr (Or.inl hlast)
      · rcases Finset.mem_map.mp himage with ⟨j, hj, hji⟩
        exact Or.inr (Or.inr ⟨j, hj, by
          have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hji.symm
          simpa [e] using this⟩)
  have hlast_ne_zero : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro hz
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hz
    simp at this
    omega
  have hzero_not_map : (0 : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
    simp [e] at this
  have hlast_not_map : (Fin.last n : Fin (n + 1)) ∉ s.map e := by
    intro hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, hj_eq⟩
    have hjlt : (j : ℕ) < n - 1 := j.2
    have hv : (j : ℕ) + 1 = n := by
      have := congrArg (fun x : Fin (n + 1) => (x : ℕ)) hj_eq
      simpa [e] using this
    omega
  have hzero_not_insert : (0 : Fin (n + 1)) ∉ insert (Fin.last n) (s.map e) := by
    simp [Ne.symm hlast_ne_zero, hzero_not_map]
  simp [compositionAsSetEquiv, CompositionAsSet.length]
  change (Finset.univ.filter p).card = s.card + 2
  rw [hset]
  rw [Finset.card_insert_of_notMem hzero_not_insert]
  rw [Finset.card_insert_of_notMem hlast_not_map]
  simp

private lemma compositionEquiv_symm_length (n : ℕ) (h : 0 < n)
    (s : Finset (Fin (n - 1))) :
    (((compositionEquiv n).symm ((compositionAsSetEquiv n).symm s)).length) =
      s.card + 1 := by
  simpa [compositionEquiv] using compositionAsSetEquiv_symm_length n h s

private lemma sum_pow_card_finset (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ s : Finset α, (Polynomial.X : ℚ[X]) ^ s.card) =
      (1 + Polynomial.X) ^ Fintype.card α := by
  simpa [Finset.prod_eq_pow_card] using
    (Finset.prod_one_add (s := (Finset.univ : Finset α))
      (f := fun _ : α => (Polynomial.X : ℚ[X]))).symm

private lemma paramPoly_compositionsByParts_zero :
    ParamClass.compositionsByParts.paramPoly 0 = (1 : ℚ[X]) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.compositionsByParts]
  change (∑ c : Composition 0, (Polynomial.X : ℚ[X]) ^ c.length) = 1
  calc
    (∑ c : Composition 0, (Polynomial.X : ℚ[X]) ^ c.length)
        = ∑ _c : Composition 0, (1 : ℚ[X]) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          have hc : c.length = 0 := (Composition.length_eq_zero c).2 rfl
          simp [hc]
    _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, composition_card]
          norm_num

private lemma paramPoly_compositionsByParts_pos (n : ℕ) (h : 0 < n) :
    ParamClass.compositionsByParts.paramPoly n =
      Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.compositionsByParts]
  change (∑ c : Composition n, (Polynomial.X : ℚ[X]) ^ c.length) =
    Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1)
  let eComp : Composition n ≃ Finset (Fin (n - 1)) :=
    (compositionEquiv n).trans (compositionAsSetEquiv n)
  calc
    (∑ c : Composition n, (Polynomial.X : ℚ[X]) ^ c.length)
        = ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ ((eComp.symm s).length) := by
          simpa using
            (Equiv.sum_comp eComp.symm
              (fun c : Composition n => (Polynomial.X : ℚ[X]) ^ c.length)).symm
    _ = ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ (s.card + 1) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [eComp, compositionEquiv_symm_length n h s]
    _ = Polynomial.X * ∑ s : Finset (Fin (n - 1)),
            (Polynomial.X : ℚ[X]) ^ s.card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [pow_succ']
    _ = Polynomial.X * (1 + Polynomial.X : ℚ[X]) ^ (n - 1) := by
          rw [sum_pow_card_finset]
          simp

private lemma coeff_mul_C_mul_X (F : ℚ[X]⟦X⟧) (A : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * (PowerSeries.C A * PowerSeries.X)) =
      PowerSeries.coeff n F * A := by
  rw [show F * (PowerSeries.C A * PowerSeries.X) =
      (F * PowerSeries.C A) * PowerSeries.X by ring]
  rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]

/-- The bivariate generating function for compositions counted by number of
parts is `(1 - z)/(1 - (1 + u)z)`, stated as a polynomial identity in formal
power series. -/
theorem ParamClass.bgf_compositionsByParts_closed :
    ParamClass.compositionsByParts.bgf *
        (1 - PowerSeries.C (1 + Polynomial.X : ℚ[X]) *
          (PowerSeries.X : ℚ[X]⟦X⟧)) =
      PowerSeries.C (1 : ℚ[X]) - (PowerSeries.X : ℚ[X]⟦X⟧) := by
  classical
  let F : ℚ[X]⟦X⟧ := ParamClass.compositionsByParts.bgf
  let A : ℚ[X] := 1 + Polynomial.X
  have hF0 : PowerSeries.coeff 0 F = (1 : ℚ[X]) := by
    simp [F, ParamClass.bgf, paramPoly_compositionsByParts_zero]
  have hFpos : ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n F = Polynomial.X * A ^ (n - 1) := by
    intro n hn
    simp [F, A, ParamClass.bgf, paramPoly_compositionsByParts_pos n hn]
  have hmain : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) =
      PowerSeries.C (1 : ℚ[X]) - (PowerSeries.X : ℚ[X]⟦X⟧) := by
    have expand : F * (1 - PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) =
        F - F * (PowerSeries.C A * (PowerSeries.X : ℚ[X]⟦X⟧)) := by
      ring
    rw [expand]
    apply PowerSeries.ext
    intro n
    rcases n with _ | _ | k
    · simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hF0
    · rw [map_sub, hFpos 1 (by omega), coeff_mul_C_mul_X F A 0, hF0]
      simp [A]
    · have hk1 : 0 < k + 1 := by omega
      have hk2 : 0 < k + 2 := by omega
      rw [map_sub, hFpos (k + 2) hk2, coeff_mul_C_mul_X F A (k + 1),
        hFpos (k + 1) hk1]
      simp [A]
      rw [pow_succ']
      ring_nf
      rw [PowerSeries.coeff_X]
      simp [show 2 + k ≠ 1 by omega]
  simpa [F, A] using hmain

end AnalyticCombinatorics.Ch1
