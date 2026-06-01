import AnalyticCombinatorics.Ch3.BGF.SeqMarked
import AnalyticCombinatorics.Ch2.EGF.LabelledSeq
import AnalyticCombinatorics.Ch2.EGF.Applications

/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sequences

For a labelled class `C`, `lseqMarked C` is `SEQ(C)` with the number of
components marked by the parameter variable `u`.  Its bivariate EGF satisfies

  `F(z,u) = 1 / (1 - u C(z))`,

represented here as `F * (1 - u C(z)) = 1` over `ℚ[u]⟦z⟧`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Bivariate exponential generating function, represented as `ℚ[u]⟦z⟧`. -/
noncomputable def ParamClass.begf (C : ParamClass) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => ((n.factorial : ℚ)⁻¹) • C.paramPoly n

@[simp] theorem ParamClass.coeff_begf (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n C.begf =
      ((n.factorial : ℚ)⁻¹) • C.paramPoly n := by
  rw [ParamClass.begf, PowerSeries.coeff_mk]

theorem ParamClass.coeff_begf_coeff (C : ParamClass) (n k : ℕ) :
    (PowerSeries.coeff n C.begf).coeff k =
      (C.bcounts n k : ℚ) / (n.factorial : ℚ) := by
  rw [ParamClass.coeff_begf, Polynomial.coeff_smul]
  have hcoeff : (C.paramPoly n).coeff k = (C.bcounts n k : ℚ) := by
    rw [← ParamClass.coeff_bgf C n k]
    simp [ParamClass.bgf]
  simp [hcoeff, div_eq_mul_inv, mul_comm]

theorem ParamClass.evalU1_begf (C : ParamClass) :
    evalU 1 C.begf = C.toCombClass.egf := by
  apply PowerSeries.ext
  intro n
  rw [evalU, ParamClass.begf, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    CombClass.coeff_egf, ParamClass.paramPoly, CombClass.counts]
  change Polynomial.eval (1 : ℚ)
      (((n.factorial : ℚ)⁻¹) •
        ∑ x : C.Obj n, (Polynomial.X : ℚ[X]) ^ C.param n x)
    = (Fintype.card (C.Obj n) : ℚ) / (n.factorial : ℚ)
  rw [Polynomial.eval_smul, Polynomial.eval_finset_sum]
  simp [div_eq_mul_inv, mul_comm]

lemma CombClass.coeff_egf_pow_eq_zero_of_lt
    (C : CombClass) (hC : C.counts 0 = 0) {n k : ℕ} (h : n < k) :
    PowerSeries.coeff n (C.egf ^ k) = 0 := by
  have h0 : constantCoeff C.egf = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
    norm_num
  exact coeff_of_lt_order n
    ((ENat.coe_lt_coe.mpr h).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k h0))

private lemma CombClass.counts_lpow_eq_zero_of_lt
    (C : CombClass) (hC : C.counts 0 = 0) {n k : ℕ} (h : n < k) :
    (C.lpow k).counts n = 0 := by
  have hcoeff : PowerSeries.coeff n ((C.lpow k).egf) = 0 := by
    rw [CombClass.egf_lpow]
    exact CombClass.coeff_egf_pow_eq_zero_of_lt C hC h
  rw [CombClass.coeff_egf] at hcoeff
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hcast : ((C.lpow k).counts n : ℚ) = 0 := by
    field_simp [hfac] at hcoeff
    simpa using hcoeff
  exact_mod_cast hcast

/-- `SEQ(C)` with the number of labelled components marked by the parameter variable. -/
def ParamClass.lseqMarked (C : CombClass) : ParamClass where
  toCombClass := C.lseq
  param _ x := (x.1 : ℕ)

lemma ParamClass.paramPoly_lseqMarked_eq_lpowCounts (C : CombClass) (n : ℕ) :
    (ParamClass.lseqMarked C).paramPoly n =
      ∑ k : Fin (n + 1),
        ((C.lpow k).counts n : ℚ) • (Polynomial.X : ℚ[X]) ^ (k : ℕ) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.lseqMarked]
  change (∑ x : Σ k : Fin (n + 1), (C.lpow k).Obj n,
      (Polynomial.X : ℚ[X]) ^ (x.1 : ℕ)) = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (∑ _y : (C.lpow k).Obj n,
      (Polynomial.X : ℚ[X]) ^ (k : ℕ)) =
    ((C.lpow k).counts n : ℚ) • (Polynomial.X : ℚ[X]) ^ (k : ℕ)
  rw [Finset.sum_const, Finset.card_univ]
  rw [nat_smul_eq_rat_smul]
  rfl

private lemma ParamClass.coeff_paramPoly_lseqMarked (C : CombClass) (n r : ℕ) :
    ((ParamClass.lseqMarked C).paramPoly n).coeff r =
      if _h : r ≤ n then ((C.lpow r).counts n : ℚ) else 0 := by
  classical
  rw [ParamClass.paramPoly_lseqMarked_eq_lpowCounts]
  rw [Polynomial.finset_sum_coeff]
  by_cases h : r ≤ n
  · rw [dif_pos h]
    let kr : Fin (n + 1) := ⟨r, Nat.lt_succ_of_le h⟩
    rw [Finset.sum_eq_single kr]
    · simp [kr]
    · intro b _ hb
      have hrb : r ≠ (b : ℕ) := by
        intro e
        apply hb
        ext
        exact e.symm
      simp [Polynomial.coeff_smul, Polynomial.coeff_X_pow, hrb]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro k _
    have hrk : r ≠ (k : ℕ) := by
      intro e
      apply h
      rw [e]
      exact Nat.le_of_lt_succ k.isLt
    simp [Polynomial.coeff_smul, Polynomial.coeff_X_pow, hrk]

lemma ParamClass.paramPoly_lseqMarked_zero (C : CombClass) :
    (ParamClass.lseqMarked C).paramPoly 0 = 1 := by
  ext r
  rw [ParamClass.coeff_paramPoly_lseqMarked]
  rcases r with _ | r
  · simp [CombClass.lpow, CombClass.counts_neutral]
  · simp [Polynomial.coeff_one]

private lemma CombClass.counts_lpow_succ_cast
    (C : CombClass) (hC : C.counts 0 = 0) (n s : ℕ) :
    ((C.lpow (s + 1)).counts (n + 1) : ℚ) =
      ∑ k : Fin (n + 1),
        (((n + 1).choose ((k : ℕ) + 1) * C.counts ((k : ℕ) + 1) *
          (C.lpow s).counts (n - (k : ℕ)) : ℕ) : ℚ) := by
  rw [CombClass.lpow, CombClass.counts_lprod, Nat.cast_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (((n + 1).choose i * C.counts i *
      (C.lpow s).counts (n + 1 - i) : ℕ) : ℚ)) (n + 2)]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (((n + 1).choose (k + 1) * C.counts (k + 1) *
      (C.lpow s).counts (n - k) : ℕ) : ℚ)) (n + 1)]
  rw [Finset.sum_range_succ']
  simp [hC, Nat.succ_sub_succ_eq_sub]

private lemma coeff_X_C_mul_succ (a : ℚ) (p : ℚ[X]) (r : ℕ) :
    ((Polynomial.X : ℚ[X]) * Polynomial.C a * p).coeff (r + 1) = a * p.coeff r := by
  rw [show (Polynomial.X : ℚ[X]) * Polynomial.C a * p =
      Polynomial.X * (Polynomial.C a * p) by ring]
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]

lemma ParamClass.paramPoly_lseqMarked_succ
    (C : CombClass) (hC : C.counts 0 = 0) (n : ℕ) :
    (ParamClass.lseqMarked C).paramPoly (n + 1) =
      ∑ k : Fin (n + 1),
        Polynomial.X *
          Polynomial.C
            ((((n + 1).choose ((k : ℕ) + 1) *
              C.counts ((k : ℕ) + 1) : ℕ) : ℚ)) *
          (ParamClass.lseqMarked C).paramPoly (n - (k : ℕ)) := by
  classical
  apply Polynomial.ext
  intro r
  rcases r with _ | s
  · rw [ParamClass.coeff_paramPoly_lseqMarked]
    simp [CombClass.lpow, CombClass.counts_neutral]
  · rw [ParamClass.coeff_paramPoly_lseqMarked]
    by_cases hs : s ≤ n
    · rw [dif_pos (Nat.succ_le_succ hs)]
      rw [CombClass.counts_lpow_succ_cast C hC n s]
      rw [Polynomial.finset_sum_coeff]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_X_C_mul_succ, ParamClass.coeff_paramPoly_lseqMarked]
      by_cases hk : s ≤ n - (k : ℕ)
      · rw [dif_pos hk]
        norm_num
      · rw [dif_neg hk]
        have hz : (C.lpow s).counts (n - (k : ℕ)) = 0 := by
          exact CombClass.counts_lpow_eq_zero_of_lt C hC (Nat.lt_of_not_ge hk)
        simp [hz]
    · rw [dif_neg]
      · rw [Polynomial.finset_sum_coeff]
        symm
        apply Finset.sum_eq_zero
        intro k _
        rw [coeff_X_C_mul_succ, ParamClass.coeff_paramPoly_lseqMarked]
        have hk : ¬ s ≤ n - (k : ℕ) := by
          intro hsk
          apply hs
          exact hsk.trans (Nat.sub_le n (k : ℕ))
        rw [dif_neg hk]
        simp
      · exact fun hsn1 => hs (Nat.le_of_succ_le_succ hsn1)

@[simp] theorem coeff_liftU (f : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (liftU f) = Polynomial.C (PowerSeries.coeff n f) := by
  simp [liftU]

theorem coeff_liftU_egf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n (liftU C.egf) =
      Polynomial.C ((C.counts n : ℚ) / (n.factorial : ℚ)) := by
  simp [liftU, CombClass.coeff_egf]

theorem coeff_U_liftU_egf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
      =
    Polynomial.X *
      Polynomial.C ((C.counts n : ℚ) / (n.factorial : ℚ)) := by
  simp [liftU, CombClass.coeff_egf]

private lemma constantCoeff_liftU_egf (C : CombClass) (hC : C.counts 0 = 0) :
    constantCoeff (liftU C.egf) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_liftU_egf, hC]
  simp

private lemma factorial_choose_scalar (n k a : ℕ) (hk : k ≤ n) :
    (a : ℚ) / (((k + 1).factorial : ℚ)) * (((n - k).factorial : ℚ)⁻¹) =
      (((n + 1).choose (k + 1) * a : ℕ) : ℚ) * (((n + 1).factorial : ℚ)⁻¹) := by
  have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_succ hk
  have hchooseQ : (((n + 1).choose (k + 1) : ℚ) * ((k + 1).factorial : ℚ) *
      ((n - k).factorial : ℚ)) = ((n + 1).factorial : ℚ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial hk1
    exact_mod_cast (by simpa [Nat.succ_sub_succ_eq_sub] using hnat)
  have hkfac : (((k + 1).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k + 1)
  have hnkfac : (((n - k).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hnfac : (((n + 1).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  field_simp [hkfac, hnkfac, hnfac]
  norm_num
  rw [← hchooseQ]
  ring

private lemma invFactorial_smul_C_X_eq
    (C : CombClass) (n k : ℕ) (p : ℚ[X]) (hk : k ≤ n) :
    (((n - k).factorial : ℚ)⁻¹) •
        (Polynomial.C ((C.counts (k + 1) : ℚ) / (((k + 1).factorial : ℚ))) *
          (Polynomial.X : ℚ[X]) * p) =
      (((n + 1).factorial : ℚ)⁻¹) •
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
  have hscalar := factorial_choose_scalar n k (C.counts (k + 1)) hk
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  calc
    Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
        (Polynomial.C ((C.counts (k + 1) : ℚ) / (((k + 1).factorial : ℚ))) *
          (Polynomial.X : ℚ[X]) * p)
        = Polynomial.C (((C.counts (k + 1) : ℚ) / (((k + 1).factorial : ℚ))) *
            (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [show Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
              (Polynomial.C ((C.counts (k + 1) : ℚ) / (((k + 1).factorial : ℚ))) *
                (Polynomial.X : ℚ[X]) * p) =
              (Polynomial.C ((C.counts (k + 1) : ℚ) / (((k + 1).factorial : ℚ))) *
                Polynomial.C (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]
    _ = Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ) *
            (((n + 1).factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [hscalar]
    _ = Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
          rw [show Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
              ((Polynomial.X : ℚ[X]) *
                Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ)) * p) =
              (Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ)) *
                Polynomial.C (((n + 1).factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]

private lemma coeff_U_liftU_mul_lseqMarked_begf_succ
    (C : CombClass) (hC : C.counts 0 = 0) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) *
        (ParamClass.lseqMarked C).begf)
      =
    ((n + 1).factorial : ℚ)⁻¹ •
      (ParamClass.lseqMarked C).paramPoly (n + 1) := by
  classical
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  rw [coeff_U_liftU_egf, hC]
  simp [ParamClass.begf, Nat.succ_sub_succ_eq_sub]
  rw [ParamClass.paramPoly_lseqMarked_succ C hC n, Finset.smul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((n + 1).factorial : ℚ)⁻¹ •
      ((Polynomial.X : ℚ[X]) *
        Polynomial.C ((((n + 1).choose (k + 1) * C.counts (k + 1) : ℕ) : ℚ)) *
        (ParamClass.lseqMarked C).paramPoly (n - k))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  exact invFactorial_smul_C_X_eq C n k
    ((ParamClass.lseqMarked C).paramPoly (n - k)) hk

theorem ParamClass.begf_lseqMarked_functional_eq
    (C : CombClass) (hC : C.counts 0 = 0) :
    (ParamClass.lseqMarked C).begf =
      1 +
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) *
          (ParamClass.lseqMarked C).begf := by
  apply PowerSeries.ext
  intro m
  rcases m with _ | n
  · simp [ParamClass.begf, ParamClass.paramPoly_lseqMarked_zero,
      constantCoeff_liftU_egf C hC]
  · rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
      coeff_U_liftU_mul_lseqMarked_begf_succ C hC n]
    rw [ParamClass.begf, PowerSeries.coeff_mk]

theorem ParamClass.begf_lseqMarked_closed (C : CombClass) (hC : C.counts 0 = 0) :
    (ParamClass.lseqMarked C).begf *
      (1 - PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) = 1 := by
  linear_combination ParamClass.begf_lseqMarked_functional_eq C hC

theorem ParamClass.evalU1_lseqMarked (C : CombClass) :
    evalU 1 (ParamClass.lseqMarked C).begf = C.lseq.egf := by
  simpa [ParamClass.lseqMarked] using
    ParamClass.evalU1_begf (ParamClass.lseqMarked C)

theorem ParamClass.begf_surjections :
    (ParamClass.lseqMarked CombClass.posInt).begf *
      (1 - PowerSeries.C (Polynomial.X : ℚ[X]) *
        liftU (PowerSeries.exp ℚ - 1)) = 1 := by
  have h := ParamClass.begf_lseqMarked_closed CombClass.posInt
    (by simp [CombClass.counts_posInt])
  rwa [CombClass.egf_posInt] at h

end AnalyticCombinatorics.Ch1
