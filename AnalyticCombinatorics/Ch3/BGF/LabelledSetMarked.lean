import AnalyticCombinatorics.Ch3.BGF.LabelledSeqMarked
import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch2.EGF.SetExp

/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sets

For a labelled class `C`, `setMarked C` is `SET(C)` with the number of blocks
marked by the parameter variable `u`. Its bivariate EGF is

  `F(z,u) = exp(u C(z))`,

represented here as substitution into `PowerSeries.exp ℚ[X]`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem derivative_liftU (f : ℚ⟦X⟧) :
    d⁄dX ℚ[X] (liftU f) = liftU (d⁄dX ℚ f) := by
  ext n
  rw [coeff_derivative, coeff_liftU, coeff_liftU, coeff_derivative]
  simp [Polynomial.C_mul]

theorem derivative_U_liftU (f : ℚ⟦X⟧) :
    d⁄dX ℚ[X] (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU f) =
      PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ f) := by
  change PowerSeries.derivativeFun (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU f) = _
  rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_C]
  rw [show PowerSeries.derivativeFun (liftU f) = liftU (d⁄dX ℚ f) by
    change d⁄dX ℚ[X] (liftU f) = liftU (d⁄dX ℚ f)
    exact derivative_liftU f]
  simp [smul_eq_mul]

lemma hasSubst_U_liftU_egf {C : CombClass} (hC : C.counts 0 = 0) :
    HasSubst (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) := by
  apply HasSubst.of_constantCoeff_zero'
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_U_liftU_egf, hC]
  simp

theorem subst_exp_ode_U_liftU {C : CombClass} (hC : C.counts 0 = 0) :
    d⁄dX ℚ[X]
        ((PowerSeries.exp ℚ[X]).subst
          (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        ((PowerSeries.exp ℚ[X]).subst
          (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) := by
  rw [derivative_subst (hg := hasSubst_U_liftU_egf hC),
    derivative_exp, derivative_U_liftU]
  ring

/-- `SET(C)` with the number of labelled blocks marked by the parameter variable. -/
noncomputable def ParamClass.setMarked (C : CombClass) : ParamClass where
  toCombClass := C.set
  param _ x := x.1.parts.card

/-- Polynomial-weighted SET sum over all partitions of a finite label type. -/
noncomputable def setMarkedWeightFull (C : CombClass)
    (α : Type*) [Fintype α] [DecidableEq α] : ℚ[X] :=
  ∑ P : Finpartition (Finset.univ : Finset α),
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card

/-- Polynomial-weighted SET sum over partitions of a finset. -/
noncomputable def setMarkedWeightFinset (C : CombClass) {α : Type*} [DecidableEq α]
    (s : Finset α) : ℚ[X] :=
  ∑ P : Finpartition s,
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card

@[simp] lemma setMarkedWeightFinset_univ
    (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setMarkedWeightFinset C (Finset.univ : Finset α) = setMarkedWeightFull C α := rfl

lemma ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull (C : CombClass) (n : ℕ) :
    (ParamClass.setMarked C).paramPoly n = setMarkedWeightFull C (Fin n) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.setMarked]
  change (∑ x : Σ P : Finpartition (Finset.univ : Finset (Fin n)),
      ∀ B : P.parts, C.Obj B.val.card,
      (Polynomial.X : ℚ[X]) ^ x.1.parts.card) = _
  rw [Fintype.sum_sigma]
  unfold setMarkedWeightFull
  refine Finset.sum_congr rfl fun P _ => ?_
  change (∑ _y : ∀ B : P.parts, C.Obj B.val.card,
      (Polynomial.X : ℚ[X]) ^ P.parts.card) =
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
  rw [nat_smul_eq_rat_smul]
  rfl

lemma ParamClass.paramPoly_setMarked_zero (C : CombClass) :
    (ParamClass.setMarked C).paramPoly 0 = 1 := by
  classical
  rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
  unfold setMarkedWeightFull
  have huniv : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := by
    simp
  rw [huniv]
  rw [Fintype.sum_unique]
  let P : Finpartition (⊥ : Finset (Fin 0)) := default
  have hparts : P.parts = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    exact P.ne_empty hA (by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxbot : x ∈ (⊥ : Finset (Fin 0)) := P.subset hA hx
      simp at hxbot)
  change (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card = 1
  rw [hparts]
  simp

@[simp] lemma finpartitionUnivCongr_parts_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    (finpartitionUnivCongr e P).parts.card = P.parts.card := by
  have h := Fintype.card_congr (finpartitionUnivCongrParts e P)
  simpa using h.symm

lemma prod_parts_finpartitionUnivCongr (C : CombClass)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    (∏ B : (finpartitionUnivCongr e P).parts, C.counts B.val.card) =
      ∏ B : P.parts, C.counts B.val.card := by
  symm
  exact Fintype.prod_equiv (M := ℕ) (finpartitionUnivCongrParts e P)
    (fun B : P.parts => C.counts B.val.card)
    (fun B : (finpartitionUnivCongr e P).parts => C.counts B.val.card)
    (fun B => by
      exact congrArg C.counts (finpartitionUnivCongrParts_card e P B).symm)

lemma prod_parts_finpartitionUnivCongr_rat (C : CombClass)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    (∏ B : (finpartitionUnivCongr e P).parts, (C.counts B.val.card : ℚ)) =
      ∏ B : P.parts, (C.counts B.val.card : ℚ) := by
  exact_mod_cast prod_parts_finpartitionUnivCongr C e P

lemma setMarkedWeightFull_congr (C : CombClass)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) :
    setMarkedWeightFull C α = setMarkedWeightFull C β := by
  classical
  unfold setMarkedWeightFull
  exact Fintype.sum_equiv (finpartitionUnivCongr e)
    (fun P : Finpartition (Finset.univ : Finset α) =>
      (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card)
    (fun P : Finpartition (Finset.univ : Finset β) =>
      (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card)
    (fun P => by
      dsimp
      have hprod := prod_parts_finpartitionUnivCongr C e P
      have hcard := finpartitionUnivCongr_parts_card e P
      have hprod_attach :
          ((finpartitionUnivCongr e P).parts.attach.prod fun i => C.counts i.val.card) =
            (P.parts.attach.prod fun i => C.counts i.val.card) := by
        simpa [Finset.prod_coe_sort] using hprod
      rw [hprod_attach, hcard])

lemma setMarkedWeightFull_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setMarkedWeightFull C α = setMarkedWeightFull C (Fin (Fintype.card α)) :=
  setMarkedWeightFull_congr C (Fintype.equivFin α)

lemma parts_card_sdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (finpartitionSdiffSubtype B Q).parts.card = Q.parts.card := by
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : Set.InjOn (fun A : Finset α => A.subtype (fun x => x ∉ B)) Q.parts := by
    intro A hA D hD hsub
    change A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) at hsub
    ext x
    constructor
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [hsub] at hxsub
      simpa using hxsub
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ D.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [← hsub] at hxsub
      simpa using hxsub
  exact Finset.card_image_of_injOn hinj

lemma setMarkedWeightFinset_sdiff_eq_setMarkedWeightFull (C : CombClass) {α : Type*}
    [Fintype α] [DecidableEq α] (B : Finset α) :
    setMarkedWeightFinset C ((Finset.univ : Finset α) \ B) =
      setMarkedWeightFull C {x : α // x ∉ B} := by
  classical
  unfold setMarkedWeightFinset setMarkedWeightFull
  have hprod_rat :
      ∀ Q : Finpartition ((Finset.univ : Finset α) \ B),
        (∏ A : (finpartitionSdiffSubtype B Q).parts, (C.counts A.val.card : ℚ)) =
          ∏ A : Q.parts, (C.counts A.val.card : ℚ) := by
    intro Q
    exact_mod_cast prod_parts_sdiffSubtype C B Q
  exact Fintype.sum_equiv (finpartitionSdiffSubtypeCongr B)
    (fun Q : Finpartition ((Finset.univ : Finset α) \ B) =>
      (((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ Q.parts.card)
    (fun Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B}) =>
      (((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ Q.parts.card)
    (fun Q => by
      dsimp
      have hprod := prod_parts_sdiffSubtype C B Q
      have hcard := parts_card_sdiffSubtype B Q
      have hprod_attach :
          ((finpartitionSdiffSubtype B Q).parts.attach.prod fun i => C.counts i.val.card) =
            (Q.parts.attach.prod fun i => C.counts i.val.card) := by
        simpa [Finset.prod_coe_sort] using hprod
      change (((Q.parts.attach.prod fun A => C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ Q.parts.card =
        ((((finpartitionSdiffSubtype B Q).parts.attach.prod fun A =>
            C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ (finpartitionSdiffSubtype B Q).parts.card
      rw [hprod_attach, hcard])

lemma prod_parts_eq_root_mul_avoid_marked (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (((∏ A : P.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card =
      Polynomial.X * Polynomial.C (C.counts B.card : ℚ) *
        ((((∏ A : (P.avoid B).parts, C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ (P.avoid B).parts.card) := by
  rw [prod_parts_eq_root_mul_avoid C hB]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  have hcard : P.parts.card = (P.avoid B).parts.card + 1 := by
    rw [hparts, Finset.card_insert_of_notMem hBnot]
  rw [hcard, pow_succ]
  rw [show (((C.counts B.card * ∏ A : (P.avoid B).parts,
        C.counts A.val.card : ℕ) : ℚ) : ℚ) =
      (C.counts B.card : ℚ) *
        (((∏ A : (P.avoid B).parts, C.counts A.val.card) : ℕ) : ℚ) by
        norm_num]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [Polynomial.C_mul]
  ring_nf

lemma sum_finset_by_card_nsmul {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k : Fin (n + 1), n.choose (k : ℕ) • f (k : ℕ) := by
  classical
  let len : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, by
      exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
  have hsplit :
      (∑ S : Finset (Fin n), f S.card) =
        ∑ x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}), f x.2.val.card := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv len)
      (fun x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}) =>
        f x.2.val.card)
      (fun S : Finset (Fin n) => f S.card)
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcard :
      Fintype.card {S : Finset (Fin n) // len S = k} = n.choose (k : ℕ) := by
    have hcard' :
        Fintype.card {S : Finset (Fin n) // len S = k} =
          (Fintype.card (Fin n)).choose (k : ℕ) := by
      rw [← Fintype.card_finset_len (α := Fin n) (k := (k : ℕ))]
      exact Fintype.card_congr
        { toFun := fun S => ⟨S.val, by
            have h := congrArg Fin.val S.property
            exact h⟩
          invFun := fun S => ⟨S.val, by
            apply Fin.ext
            exact S.property⟩
          left_inv := by intro S; apply Subtype.ext; rfl
          right_inv := by intro S; apply Subtype.ext; rfl }
    simpa [Fintype.card_fin] using hcard'
  trans Fintype.card {S : Finset (Fin n) // len S = k} • f (k : ℕ)
  · rw [← Finset.card_univ, Finset.sum_eq_card_nsmul]
    intro S _hS
    have h := congrArg Fin.val S.property
    simpa using congrArg f h
  · rw [hcard]

lemma setMarkedWeightFull_root (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) :
    setMarkedWeightFull C α =
      ∑ B : {B : Finset α // r ∈ B},
        Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
          setMarkedWeightFull C {x : α // x ∉ B.val} := by
  classical
  unfold setMarkedWeightFull
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, P.mem_part (by simp)⟩
  let w : Finpartition (Finset.univ : Finset α) → ℚ[X] :=
    fun P => (((∏ A : P.parts, C.counts A.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card
  have hsplit :
      ∑ P : Finpartition (Finset.univ : Finset α), w P =
        ∑ x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}), w x.2.val := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block)
      (fun x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}) => w x.2.val)
      w
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun B _ => ?_
  let fiberEquiv :
      {P : Finpartition (Finset.univ : Finset α) // block P = B} ≃
        {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} :=
    { toFun := fun P => ⟨P.val, by
        have h := congrArg Subtype.val P.property
        exact h⟩
      invFun := fun P => ⟨P.val, by
        apply Subtype.ext
        exact P.property⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  let rootEquiv := finpartitionRootFiberEquiv r B.property
  have hfiber :
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val =
        ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
          Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
            ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
              (Polynomial.X : ℚ[X]) ^ Q.parts.card) := by
    calc
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val
          = ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val},
              w P.val := by
            exact Fintype.sum_equiv fiberEquiv
              (fun P => w P.val) (fun P => w P.val) (by intro P; rfl)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              w ((rootEquiv.symm Q).val) := by
            exact Fintype.sum_equiv rootEquiv
              (fun P => w P.val)
              (fun Q => w ((rootEquiv.symm Q).val))
              (by intro P; simp)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
                ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
                  (Polynomial.X : ℚ[X]) ^ Q.parts.card) := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            have hruniv : r ∈ (Finset.univ : Finset α) := by simp
            have hBmem : B.val ∈ (rootEquiv.symm Q).val.parts := by
              have hprop := (rootEquiv.symm Q).property
              simpa [hprop] using (rootEquiv.symm Q).val.part_mem.2 hruniv
            dsimp [w]
            change (((∏ A : (rootEquiv.symm Q).val.parts, C.counts A.val.card) : ℕ) : ℚ) •
                (Polynomial.X : ℚ[X]) ^ (rootEquiv.symm Q).val.parts.card =
              Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
                ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
                  (Polynomial.X : ℚ[X]) ^ Q.parts.card)
            rw [prod_parts_eq_root_mul_avoid_marked C hBmem]
            have havoid : (rootEquiv.symm Q).val.avoid B.val = Q := by
              exact Equiv.apply_symm_apply rootEquiv Q
            rw [havoid]
  rw [hfiber]
  rw [← Finset.mul_sum]
  change Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
      setMarkedWeightFinset C ((Finset.univ : Finset α) \ B.val) =
    Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
      setMarkedWeightFull C {x : α // x ∉ B.val}
  rw [setMarkedWeightFinset_sdiff_eq_setMarkedWeightFull]

lemma ParamClass.paramPoly_setMarked_succ (C : CombClass) (n : ℕ) :
    (ParamClass.setMarked C).paramPoly (n + 1) =
      ∑ k : Fin (n + 1),
        Polynomial.X *
          Polynomial.C
            (((n.choose (k : ℕ) * C.counts ((k : ℕ) + 1) : ℕ) : ℚ)) *
          (ParamClass.setMarked C).paramPoly (n - (k : ℕ)) := by
  classical
  rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
  rw [setMarkedWeightFull_root C (Fin.last n)]
  have hblocks :
      (∑ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
          Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
            setMarkedWeightFull C {x : Fin (n + 1) // x ∉ B.val})
        =
      ∑ S : Finset (Fin n),
        Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
          (ParamClass.setMarked C).paramPoly (n - S.card) := by
    symm
    exact Fintype.sum_equiv (rootBlockEquiv n)
      (fun S : Finset (Fin n) =>
        Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
          (ParamClass.setMarked C).paramPoly (n - S.card))
      (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
        Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
          setMarkedWeightFull C {x : Fin (n + 1) // x ∉ B.val})
      (by
        intro S
        change Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
            (ParamClass.setMarked C).paramPoly (n - S.card) =
          Polynomial.X * Polynomial.C (C.counts ((rootBlockEquiv n S).val.card) : ℚ) *
            setMarkedWeightFull C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}
        rw [rootBlockEquiv_card]
        rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
        rw [setMarkedWeightFull_card C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}]
        rw [rootBlockEquiv_compl_card])
  rw [hblocks]
  rw [sum_finset_by_card_nsmul n
    (fun k => Polynomial.X * Polynomial.C (C.counts (k + 1) : ℚ) *
      (ParamClass.setMarked C).paramPoly (n - k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nat_smul_eq_rat_smul, Polynomial.smul_eq_C_mul]
  have hcast : (((n.choose (k : ℕ) * C.counts ((k : ℕ) + 1) : ℕ) : ℚ) =
      (n.choose (k : ℕ) : ℚ) * (C.counts ((k : ℕ) + 1) : ℚ)) := by
    norm_num
  rw [hcast]
  rw [Polynomial.C_mul]
  ring

theorem ParamClass.coeff_derivative_begf (P : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX ℚ[X] P.begf) =
      ((n.factorial : ℚ)⁻¹) • P.paramPoly (n + 1) := by
  rw [coeff_derivative, ParamClass.coeff_begf]
  have hscalar :
      (((n + 1).factorial : ℚ)⁻¹ * ((n + 1 : ℕ) : ℚ)) =
        (n.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ]
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hn, hnf]
    norm_num [Nat.cast_mul]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [show ((n : ℚ[X]) + 1) = Polynomial.C ((n + 1 : ℕ) : ℚ) by norm_num]
  calc
    Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
          P.paramPoly (n + 1) * Polynomial.C ((n + 1 : ℕ) : ℚ)
        = Polynomial.C ((((n + 1).factorial : ℚ)⁻¹ * ((n + 1 : ℕ) : ℚ))) *
            P.paramPoly (n + 1) := by
          rw [show Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
              P.paramPoly (n + 1) * Polynomial.C ((n + 1 : ℕ) : ℚ) =
              (Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
                Polynomial.C ((n + 1 : ℕ) : ℚ)) * P.paramPoly (n + 1) by ring]
          rw [Polynomial.C_mul]
    _ = Polynomial.C ((n.factorial : ℚ)⁻¹) * P.paramPoly (n + 1) := by
          rw [hscalar]

theorem coeff_U_liftU_derivative_egf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) =
  Polynomial.X *
      Polynomial.C ((C.counts (n + 1) : ℚ) / (n.factorial : ℚ)) := by
  rw [← CombClass.egf_deriv C]
  simp [CombClass.counts_deriv]

private lemma factorial_choose_scalar_set (n k a : ℕ) (hk : k ≤ n) :
    (a : ℚ) / (k.factorial : ℚ) * (((n - k).factorial : ℚ)⁻¹) =
      (((n.choose k * a : ℕ) : ℚ) * ((n.factorial : ℚ)⁻¹)) := by
  have hchooseQ : (((n.choose k : ℚ) * (k.factorial : ℚ) *
      ((n - k).factorial : ℚ)) = (n.factorial : ℚ)) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial hk
    exact_mod_cast hnat
  have hkfac : ((k.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hnkfac : (((n - k).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hnfac : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hkfac, hnkfac, hnfac]
  norm_num
  rw [← hchooseQ]
  ring

private lemma invFactorial_smul_C_X_eq_set
    (C : CombClass) (n k : ℕ) (p : ℚ[X]) (hk : k ≤ n) :
    (((n - k).factorial : ℚ)⁻¹) •
        (Polynomial.X *
          Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p) =
      ((n.factorial : ℚ)⁻¹) •
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
  have hscalar := factorial_choose_scalar_set n k (C.counts (k + 1)) hk
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  calc
    Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p)
        = Polynomial.C (((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) *
            (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [show Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
              ((Polynomial.X : ℚ[X]) *
                Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p) =
              (Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) *
                Polynomial.C (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]
    _ = Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ) *
            ((n.factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [hscalar]
    _ = Polynomial.C ((n.factorial : ℚ)⁻¹) *
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
          rw [show Polynomial.C ((n.factorial : ℚ)⁻¹) *
              ((Polynomial.X : ℚ[X]) *
                Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) =
              (Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) *
                Polynomial.C ((n.factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]

private lemma mul_invFactorial_smul_assoc_set (a b : ℚ) (p : ℚ[X]) :
    (Polynomial.X : ℚ[X]) * Polynomial.C a * (b • p) =
      b • ((Polynomial.X : ℚ[X]) * Polynomial.C a * p) := by
  rw [Polynomial.smul_eq_C_mul]
  rw [Polynomial.smul_eq_C_mul]
  ring

private lemma coeff_U_liftU_derivative_mul_setMarked_begf
    (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        (ParamClass.setMarked C).begf)
      =
    ((n.factorial : ℚ)⁻¹) •
      (ParamClass.setMarked C).paramPoly (n + 1) := by
  classical
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [ParamClass.paramPoly_setMarked_succ C n, Finset.smul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((n.factorial : ℚ)⁻¹) •
      ((Polynomial.X : ℚ[X]) *
        Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) *
        (ParamClass.setMarked C).paramPoly (n - k))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [coeff_U_liftU_derivative_egf, ParamClass.coeff_begf]
  rw [mul_invFactorial_smul_assoc_set]
  exact invFactorial_smul_C_X_eq_set C n k
    ((ParamClass.setMarked C).paramPoly (n - k)) hk

theorem ParamClass.begf_setMarked_ode (C : CombClass) :
    d⁄dX ℚ[X] (ParamClass.setMarked C).begf =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        (ParamClass.setMarked C).begf := by
  apply PowerSeries.ext
  intro n
  rw [ParamClass.coeff_derivative_begf,
    coeff_U_liftU_derivative_mul_setMarked_begf]

theorem ParamClass.begf_setMarked_exp (C : CombClass) (hC : C.counts 0 = 0) :
    (ParamClass.setMarked C).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) := by
  let H : ℚ[X]⟦X⟧ :=
    (ParamClass.setMarked C).begf -
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
  have hode : d⁄dX ℚ[X] H =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) * H := by
    dsimp [H]
    rw [map_sub, ParamClass.begf_setMarked_ode,
      subst_exp_ode_U_liftU hC]
    ring
  have h0C : constantCoeff (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_U_liftU_egf, hC]
    simp
  have h0set : constantCoeff (ParamClass.setMarked C).begf = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ParamClass.coeff_begf,
      ParamClass.paramPoly_setMarked_zero]
    simp
  have h0subst :
      constantCoeff ((PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) = 1 := by
    change MvPowerSeries.constantCoeff
      (PowerSeries.subst (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
        (PowerSeries.exp ℚ[X])) = 1
    rw [constantCoeff_subst (hasSubst_U_liftU_egf hC)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      have hpow : MvPowerSeries.constantCoeff
          ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) ^ d) = 0 := by
        change constantCoeff
          ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) ^ d) = 0
        rw [map_pow, h0C, zero_pow hd]
      rw [hpow, smul_zero]
  have h0 : constantCoeff H = 0 := by
    dsimp [H]
    rw [map_sub, h0set, h0subst, sub_self]
  have hH : H = 0 := ode_unique (H := H)
    (G := PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) hode h0
  exact sub_eq_zero.mp hH

theorem ParamClass.evalU1_setMarked (C : CombClass) :
    evalU 1 (ParamClass.setMarked C).begf = C.set.egf := by
  simpa [ParamClass.setMarked] using
    ParamClass.evalU1_begf (ParamClass.setMarked C)

end AnalyticCombinatorics.Ch1
