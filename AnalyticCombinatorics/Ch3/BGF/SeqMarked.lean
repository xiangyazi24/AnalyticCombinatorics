import AnalyticCombinatorics.Ch3.BGF.Defs
import AnalyticCombinatorics.Ch1.OGF.SequenceInverse

/-!
# Ch3 -- BGF transfer theorem for marked sequences

For an ordinary class `C`, `seqMarked C` is `SEQ(C)` with the sequence length
marked by the parameter variable `u`.  Its BGF satisfies
`F(z,u) = 1 / (1 - u C(z))`, represented here as
`F * (1 - u C(z)) = 1`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Coefficientwise embedding from OGFs into BGFs. -/
noncomputable def liftU : ℚ⟦X⟧ →+* ℚ[X]⟦X⟧ :=
  PowerSeries.map (Polynomial.C : ℚ →+* ℚ[X])

theorem evalU_liftU (a : ℚ) (f : ℚ⟦X⟧) :
    evalU a (liftU f) = f := by
  apply PowerSeries.ext
  intro n
  simp [evalU, liftU]

theorem coeff_liftU_ogf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n (liftU C.ogf) =
      Polynomial.C (C.counts n : ℚ) := by
  simp [liftU, CombClass.coeff_ogf]

theorem evalU_C_u (a : ℚ) :
    evalU a (PowerSeries.C (Polynomial.X : ℚ[X])) = PowerSeries.C a := by
  simp [evalU]

private lemma nat_smul_eq_rat_smul (m : ℕ) (p : ℚ[X]) :
    m • p = (m : ℚ) • p := by
  rw [nsmul_eq_mul]
  rw [show (m : ℚ[X]) = Polynomial.C (m : ℚ) by norm_num]
  rw [← Polynomial.smul_eq_C_mul]

private lemma X_C_mul_smul_X_pow (a b : ℚ) (m : ℕ) :
    (Polynomial.X : ℚ[X]) * Polynomial.C a * (b • (Polynomial.X : ℚ[X]) ^ m) =
      (a * b) • (Polynomial.X : ℚ[X]) ^ (m + 1) := by
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [pow_succ]
  calc
    (Polynomial.X : ℚ[X]) * Polynomial.C a *
          (Polynomial.C b * (Polynomial.X : ℚ[X]) ^ m)
        = (Polynomial.C a * Polynomial.C b) *
            ((Polynomial.X : ℚ[X]) ^ m * Polynomial.X) := by
          ring
    _ = Polynomial.C (a * b) * ((Polynomial.X : ℚ[X]) ^ m * Polynomial.X) := by
          rw [Polynomial.C_mul]

/-- `SEQ(C)` with the sequence length marked by the parameter variable. -/
def ParamClass.seqMarked (C : CombClass) : ParamClass where
  toCombClass := C.seq
  param _ x := x.1.length

lemma consSeq_length (n : ℕ) (k : Fin (n + 1))
    (c : Composition (n - (k : ℕ))) :
    (consSeq n k c).length = c.length + 1 := by
  have hb := congrArg List.length (consSeq_blocks n k c)
  simpa using hb

lemma ParamClass.paramPoly_seqMarked_eq_listProd (C : CombClass) (n : ℕ) :
    (ParamClass.seqMarked C).paramPoly n =
      ∑ c : Composition n,
        ((c.blocks.map C.counts).prod : ℚ) •
          (Polynomial.X : ℚ[X]) ^ c.length := by
  classical
  rw [ParamClass.paramPoly, ParamClass.seqMarked]
  change (∑ x : Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i),
      (Polynomial.X : ℚ[X]) ^ x.1.length) = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (∑ _y : ∀ i : Fin c.length, C.Obj (c.blocksFun i),
      (Polynomial.X : ℚ[X]) ^ c.length) =
    ((c.blocks.map C.counts).prod : ℚ) • (Polynomial.X : ℚ[X]) ^ c.length
  rw [Finset.sum_const]
  rw [Finset.card_univ, Fintype.card_pi]
  rw [← Composition.ofFn_blocksFun c, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, CombClass.counts]
  rw [nat_smul_eq_rat_smul]

lemma ParamClass.paramPoly_seqMarked_zero (C : CombClass) :
    (ParamClass.seqMarked C).paramPoly 0 = 1 := by
  rw [ParamClass.paramPoly_seqMarked_eq_listProd]
  have h : ∀ c : Composition 0,
      (List.map (((fun m : ℕ => (m : ℚ)) ∘ C.counts)) c.blocks).prod •
          (Polynomial.X : ℚ[X]) ^ c.length = 1 := by
    intro c
    have hnil : c.blocks = [] := (Composition.blocks_eq_nil c).2 rfl
    have hlen : c.length = 0 := (Composition.length_eq_zero c).2 rfl
    simp [hnil, hlen]
  simp [h, Finset.card_univ, composition_card]

lemma ParamClass.paramPoly_seqMarked_succ (C : CombClass) (n : ℕ) :
    (ParamClass.seqMarked C).paramPoly (n + 1) =
      ∑ k : Fin (n + 1),
        Polynomial.X *
          Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
          (ParamClass.seqMarked C).paramPoly (n - (k : ℕ)) := by
  classical
  rw [ParamClass.paramPoly_seqMarked_eq_listProd]
  rw [← Fintype.sum_bijective _ (consSeq_bijective n)
        (fun p : Σ k : Fin (n + 1), Composition (n - (k : ℕ)) =>
          (((consSeq n p.1 p.2).blocks.map C.counts).prod : ℚ) •
            (Polynomial.X : ℚ[X]) ^ (consSeq n p.1 p.2).length)
        (fun c : Composition (n + 1) =>
          ((c.blocks.map C.counts).prod : ℚ) •
            (Polynomial.X : ℚ[X]) ^ c.length)
        (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (∑ c : Composition (n - (k : ℕ)),
      (((consSeq n k c).blocks.map C.counts).prod : ℚ) •
        (Polynomial.X : ℚ[X]) ^ (consSeq n k c).length) =
    Polynomial.X * Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
      (ParamClass.seqMarked C).paramPoly (n - (k : ℕ))
  calc
    (∑ c : Composition (n - (k : ℕ)),
      (((consSeq n k c).blocks.map C.counts).prod : ℚ) •
        (Polynomial.X : ℚ[X]) ^ (consSeq n k c).length)
        = ∑ c : Composition (n - (k : ℕ)),
            Polynomial.X * Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
              (((c.blocks.map C.counts).prod : ℚ) •
                (Polynomial.X : ℚ[X]) ^ c.length) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [prod_consSeq, consSeq_length]
          rw [show ((C.counts ((k : ℕ) + 1) *
                (c.blocks.map C.counts).prod : ℕ) : ℚ) =
              (C.counts ((k : ℕ) + 1) : ℚ) *
                ((c.blocks.map C.counts).prod : ℚ) by norm_num]
          rw [← X_C_mul_smul_X_pow]
    _ = Polynomial.X * Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
          (∑ c : Composition (n - (k : ℕ)),
            ((c.blocks.map C.counts).prod : ℚ) •
              (Polynomial.X : ℚ[X]) ^ c.length) := by
          rw [Finset.mul_sum]
    _ = Polynomial.X * Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
          (ParamClass.seqMarked C).paramPoly (n - (k : ℕ)) := by
          rw [← ParamClass.paramPoly_seqMarked_eq_listProd]

lemma coeff_U_liftU_ogf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.ogf)
      =
    Polynomial.X * Polynomial.C (C.counts n : ℚ) := by
  simp [liftU, CombClass.coeff_ogf]

private lemma constantCoeff_liftU_ogf (C : CombClass) (hC0 : C.counts 0 = 0) :
    constantCoeff (liftU C.ogf) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_liftU_ogf, hC0]
  simp

lemma coeff_U_liftU_mul_seqMarked_succ
    (C : CombClass) (hC0 : C.counts 0 = 0) (n : ℕ) :
    PowerSeries.coeff (n + 1)
      ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.ogf) *
        (ParamClass.seqMarked C).bgf)
      =
    ∑ k : Fin (n + 1),
      Polynomial.X *
        Polynomial.C (C.counts ((k : ℕ) + 1) : ℚ) *
        (ParamClass.seqMarked C).paramPoly (n - (k : ℕ)) := by
  classical
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  rw [coeff_U_liftU_ogf, hC0]
  simp
  rw [@Fin.sum_univ_eq_sum_range ℚ[X] _
    (fun k : ℕ => (Polynomial.X : ℚ[X]) * (C.counts (k + 1) : ℚ[X]) *
      (ParamClass.seqMarked C).paramPoly (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [liftU, CombClass.coeff_ogf, ParamClass.bgf]

/-- Functional equation for marked sequences: `F = 1 + u C(z) F`. -/
theorem ParamClass.bgf_seqMarked_functional_eq
    (C : CombClass) (hC0 : C.counts 0 = 0) :
    (ParamClass.seqMarked C).bgf =
      1 +
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.ogf) *
          (ParamClass.seqMarked C).bgf := by
  apply PowerSeries.ext
  intro m
  rcases m with _ | n
  · simp [ParamClass.bgf, ParamClass.paramPoly_seqMarked_zero,
      constantCoeff_liftU_ogf C hC0]
  · rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
      coeff_U_liftU_mul_seqMarked_succ C hC0 n]
    rw [ParamClass.bgf, PowerSeries.coeff_mk, ParamClass.paramPoly_seqMarked_succ]

/-- Closed form for marked sequences: `F(z,u) * (1 - u C(z)) = 1`. -/
theorem ParamClass.bgf_seqMarked_closed (C : CombClass) (hC0 : C.counts 0 = 0) :
    (ParamClass.seqMarked C).bgf *
      (1 - PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.ogf) = 1 := by
  linear_combination ParamClass.bgf_seqMarked_functional_eq C hC0

theorem ParamClass.evalU1_seqMarked (C : CombClass) :
    evalU 1 (ParamClass.seqMarked C).bgf = C.seq.ogf := by
  simpa [ParamClass.seqMarked] using
    ParamClass.evalU1_bgf (ParamClass.seqMarked C)

end AnalyticCombinatorics.Ch1
