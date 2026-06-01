import AnalyticCombinatorics.Ch3.BGF.Variance

/-!
# Ch3 -- Mean and variance for parts in compositions

For a fixed `n ≥ 1`, Mathlib's boundary-set equivalence identifies
compositions of `n` with subsets of `Fin (n - 1)`.  The number of parts is one
plus the number of chosen interior boundaries.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

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

private lemma coeff_factorialMoment1_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (factorialMoment1 ParamClass.compositionsByParts.bgf) =
      (((n : ℚ) + 1) / 2) * (2 : ℚ) ^ (n - 1) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 1 (by omega)]
  · simp [factorialMoment1, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos (n + 2) (by omega),
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.eval_pow]
    ring_nf

private lemma coeff_rawMoment2_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.coeff n (rawMoment2 ParamClass.compositionsByParts.bgf) =
      ((n : ℚ) * ((n : ℚ) + 3) / 4) * (2 : ℚ) ^ (n - 1) := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 1 (by omega)]
    norm_num
  rcases n with _ | n
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos 2 (by omega), Polynomial.derivative_mul]
    norm_num
  · simp [rawMoment2, evalU, uDeriv, ParamClass.bgf,
      paramPoly_compositionsByParts_pos (n + 3) (by omega),
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.eval_pow]
    ring_nf

theorem ParamClass.mean_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.compositionsByParts.mean n = ((n : ℚ) + 1) / 2 := by
  rw [ParamClass.mean_eq]
  rw [← ParamClass.coeff_factorialMoment1 ParamClass.compositionsByParts n,
    coeff_factorialMoment1_compositionsByParts hn]
  simp [ParamClass.compositionsByParts, CombClass.counts_compositions]

theorem ParamClass.variance_compositionsByParts {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.compositionsByParts.variance n = ((n : ℚ) - 1) / 4 := by
  rw [ParamClass.variance_eq]
  rw [← ParamClass.coeff_rawMoment2 ParamClass.compositionsByParts n,
    coeff_rawMoment2_compositionsByParts hn, ParamClass.mean_compositionsByParts hn]
  simp [ParamClass.compositionsByParts, CombClass.counts_compositions]
  ring

end AnalyticCombinatorics.Ch1
