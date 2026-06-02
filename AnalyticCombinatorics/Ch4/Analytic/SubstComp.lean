import AnalyticCombinatorics.Ch4.Analytic.Bridge
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution

open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private noncomputable def finsuppAntidiagRangeEquivFin (m g : ℕ) :
    (Finset.range g).finsuppAntidiag m ≃
      { l : Fin g → ℕ // ∑ i, l i = m } where
  toFun l := by
    refine ⟨fun i => l.1 i.val, ?_⟩
    have hl := (Finset.mem_finsuppAntidiag.mp l.2).1
    calc
      (∑ i : Fin g, l.1 i.val) =
          ∑ i ∈ Finset.range g, if h : i < g then l.1 i else 0 :=
        Finset.sum_fin_eq_sum_range (fun i : Fin g => l.1 i.val)
      _ = ∑ i ∈ Finset.range g, l.1 i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [dif_pos (Finset.mem_range.mp hi)]
      _ = m := hl
  invFun l := by
    classical
    let f : ℕ → ℕ := fun i => if h : i < g then l.1 ⟨i, h⟩ else 0
    let fs : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range g) f (by
      intro i hi
      by_cases h : i < g
      · exact Finset.mem_range.mpr h
      · simp [f, h] at hi)
    refine ⟨fs, ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · change ∑ i ∈ Finset.range g, fs i = m
      have hsum : (∑ i : Fin g, fs i.val) = m := by
        simpa [fs, f] using l.2
      calc
        (∑ i ∈ Finset.range g, fs i) =
            ∑ i ∈ Finset.range g, if h : i < g then fs i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [dif_pos (Finset.mem_range.mp hi)]
        _ = ∑ i : Fin g, fs i.val :=
          (Finset.sum_fin_eq_sum_range (fun i : Fin g => fs i.val)).symm
        _ = m := hsum
    · intro i hi
      rw [Finsupp.mem_support_iff] at hi
      by_cases h : i < g
      · exact Finset.mem_range.mpr h
      · exfalso
        exact hi (by simp [fs, f, h])
  left_inv l := by
    apply Subtype.ext
    ext i
    by_cases h : i < g
    · simp [h]
    · have hsupp := (Finset.mem_finsuppAntidiag.mp l.2).2
      have hinotsupp : i ∉ l.1.support := by
        intro hi
        exact h (Finset.mem_range.mp (hsupp hi))
      have hzero : l.1 i = 0 := by
        simpa [Finsupp.mem_support_iff] using hinotsupp
      simp [h, hzero]
  right_inv l := by
    apply Subtype.ext
    funext i
    simp

private noncomputable def positiveFinTupleCompositionEquiv (n d : ℕ) :
    { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n } ≃
      { c : Composition n // c.length = d } where
  toFun l := by
    refine ⟨{ blocks := List.ofFn l.1, blocks_pos := ?_, blocks_sum := ?_ }, ?_⟩
    · intro x hx
      rw [List.mem_ofFn'] at hx
      rcases hx with ⟨i, rfl⟩
      exact l.2.1 i
    · simpa [List.sum_ofFn] using l.2.2
    · simp [Composition.length]
  invFun c := by
    refine ⟨fun i : Fin d => c.1.blocksFun ((finCongr c.2.symm) i), ?_⟩
    constructor
    · intro i
      exact c.1.one_le_blocksFun ((finCongr c.2.symm) i)
    · calc
        (∑ i : Fin d, c.1.blocksFun ((finCongr c.2.symm) i)) =
            ∑ j : Fin c.1.length, c.1.blocksFun j := by
          exact Fintype.sum_equiv (finCongr c.2.symm)
            (fun i : Fin d => c.1.blocksFun ((finCongr c.2.symm) i))
            (fun j : Fin c.1.length => c.1.blocksFun j) (by intro i; rfl)
        _ = n := c.1.sum_blocksFun
  left_inv l := by
    apply Subtype.ext
    funext i
    simp [Composition.blocksFun]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    ext1
    change List.ofFn (fun i : Fin d => c.blocksFun ((finCongr hc.symm) i)) = c.blocks
    subst d
    simp [Composition.ofFn_blocksFun]

private noncomputable def positiveSubtypeEquiv (n d : ℕ) :
    { x : { y : Fin d → ℕ // ∑ i, y i = n } // ∀ i, 0 < x.1 i } ≃
      { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n } where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv x := by rfl
  right_inv x := by rfl

private noncomputable def sigmaLengthCompositionEquiv (n : ℕ) :
    (Sigma fun d : Fin (n + 1) => { c : Composition n // c.length = d.val }) ≃
      Composition n where
  toFun x := x.2.1
  invFun c := ⟨⟨c.length, Nat.lt_succ_of_le c.length_le⟩, ⟨c, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨d, _hd⟩, c, hc⟩
    dsimp at hc
    subst d
    simp
  right_inv c := by rfl

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  exact PowerSeries.coeff_of_lt_order n
    (lt_of_lt_of_le (by exact_mod_cast hnd)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries

