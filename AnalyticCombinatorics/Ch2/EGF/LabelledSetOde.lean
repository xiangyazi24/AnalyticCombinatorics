import AnalyticCombinatorics.Ch2.EGF.LabelledSet
import AnalyticCombinatorics.Ch2.EGF.SetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledProduct
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin

/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The order isomorphism on finsets induced by an equivalence of labels. -/
noncomputable def finsetOrderIsoOfEquiv {α β : Type*} (e : α ≃ β) :
    Finset α ≃o Finset β :=
  e.finsetCongr.toOrderIso
    (by
      intro s t h
      rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply]
      exact Finset.map_subset_map.mpr h)
    (by
      intro s t h
      rw [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Equiv.finsetCongr_apply]
      exact Finset.map_subset_map.mpr h)

@[simp] lemma finsetOrderIsoOfEquiv_apply {α β : Type*} (e : α ≃ β) (s : Finset α) :
    finsetOrderIsoOfEquiv e s = s.map e.toEmbedding := by
  rfl

@[simp] lemma finsetOrderIsoOfEquiv_symm_apply {α β : Type*} (e : α ≃ β)
    (s : Finset β) :
    (finsetOrderIsoOfEquiv e).symm s = s.map e.symm.toEmbedding := by
  rfl

/-- Relabel finpartitions of the full label type along an equivalence of labels. -/
noncomputable def finpartitionUnivCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃ Finpartition (Finset.univ : Finset β) where
  toFun P := (P.map (finsetOrderIsoOfEquiv e)).copy (by
    change (Finset.univ : Finset α).map e.toEmbedding = (Finset.univ : Finset β)
    rw [Finset.map_univ_equiv])
  invFun Q := (Q.map (finsetOrderIsoOfEquiv e).symm).copy (by
    change (Finset.univ : Finset β).map e.symm.toEmbedding = (Finset.univ : Finset α)
    rw [Finset.map_univ_equiv])
  left_inv P := by
    ext A
    simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
    constructor
    · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
      subst hBA
      subst hCB
      simpa [Finset.map_map] using hC
    · intro hA
      refine ⟨(finsetOrderIsoOfEquiv e) A, ?_, ?_⟩
      · exact ⟨A, hA, rfl⟩
      · simp [Finset.map_map]
  right_inv Q := by
    ext A
    simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
    constructor
    · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
      subst hBA
      subst hCB
      simpa [Finset.map_map] using hC
    · intro hA
      refine ⟨(finsetOrderIsoOfEquiv e).symm A, ?_, ?_⟩
      · exact ⟨A, hA, rfl⟩
      · simp [Finset.map_map]

/-- SET-objects over an arbitrary finite label type. -/
abbrev labelledSetObj (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :=
  Σ P : Finpartition (Finset.univ : Finset α), ∀ B : P.parts, C.Obj B.val.card

/-- The parts of a relabelled full finpartition are equivalent to the original parts. -/
noncomputable def finpartitionUnivCongrParts {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    P.parts ≃ (finpartitionUnivCongr e P).parts where
  toFun B := ⟨(finsetOrderIsoOfEquiv e) B.val, by
    change (finsetOrderIsoOfEquiv e) B.val ∈ (P.map (finsetOrderIsoOfEquiv e)).parts
    rw [Finpartition.parts_map]
    exact Finset.mem_map.mpr ⟨B.val, B.property, rfl⟩⟩
  invFun B := ⟨(finsetOrderIsoOfEquiv e).symm B.val, by
    have hB : B.val ∈ (P.map (finsetOrderIsoOfEquiv e)).parts := by
      simpa [finpartitionUnivCongr] using B.property
    rw [Finpartition.parts_map, Finset.mem_map] at hB
    rcases hB with ⟨A, hA, hAmap⟩
    have hAmap' : (finsetOrderIsoOfEquiv e) A = B.val := by simpa using hAmap
    rw [← hAmap']
    simpa [Finset.map_map] using hA⟩
  left_inv B := by
    ext x
    simp [Finset.map_map]
  right_inv B := by
    ext x
    simp [Finset.map_map]

@[simp] lemma finpartitionUnivCongrParts_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) (B : P.parts) :
    ((finpartitionUnivCongrParts e P B).val.card) = B.val.card := by
  simp [finpartitionUnivCongrParts]

/-- Relabel SET-objects over equivalent finite label types. -/
noncomputable def labelledSetObjCongr (C : CombClass) {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    labelledSetObj C α ≃ labelledSetObj C β :=
  Equiv.sigmaCongr (finpartitionUnivCongr e) fun P =>
    (Equiv.piCongrRight fun B =>
      Equiv.cast (by rw [finpartitionUnivCongrParts_card e P B])).trans
    (Equiv.piCongrLeft (fun B : (finpartitionUnivCongr e P).parts => C.Obj B.val.card)
      (finpartitionUnivCongrParts e P))

@[simp] lemma labelledSetObj_fin_card (C : CombClass) (n : ℕ) :
    Fintype.card (labelledSetObj C (Fin n)) = C.set.counts n := rfl

lemma labelledSetObj_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_fin_card C (Fintype.card α)]
  exact Fintype.card_congr (labelledSetObjCongr C (Fintype.equivFin α))

/-- Weighted SET sum over all partitions of a finite label type. -/
noncomputable def setWeightFull (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] : ℕ :=
  ∑ P : Finpartition (Finset.univ : Finset α), ∏ B : P.parts, C.counts B.val.card

/-- Weighted SET sum over partitions of a finset. -/
noncomputable def setWeightFinset (C : CombClass) {α : Type*} [DecidableEq α]
    (s : Finset α) : ℕ :=
  ∑ P : Finpartition s, ∏ B : P.parts, C.counts B.val.card

@[simp] lemma setWeightFinset_univ (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setWeightFinset C (Finset.univ : Finset α) = setWeightFull C α := rfl

lemma labelledSetObj_card_eq_setWeightFull (C : CombClass) (α : Type*) [Fintype α]
    [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = setWeightFull C α := by
  change Fintype.card
      (Σ P : Finpartition (Finset.univ : Finset α), ∀ B : P.parts, C.Obj B.val.card) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Fintype.card_pi]
  rfl

lemma setWeightFull_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setWeightFull C α = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_card_eq_setWeightFull, labelledSetObj_card]

/-- Turn a partition of the complement finset into a partition of the complement subtype. -/
noncomputable def finpartitionSdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    Finpartition (Finset.univ : Finset {x : α // x ∉ B}) :=
  Finpartition.ofExistsUnique
    (Q.parts.image fun A => A.subtype (fun x => x ∉ B))
    (by
      intro p hp x hx
      simp)
    (by
      intro a _ha
      have ha : (a.val : α) ∈ (Finset.univ : Finset α) \ B := by simp [a.property]
      obtain ⟨A, hA, hAuniq⟩ := Q.existsUnique_mem ha
      refine ⟨A.subtype (fun x => x ∉ B), ?_, ?_⟩
      · exact ⟨Finset.mem_image.mpr ⟨A, hA.1, rfl⟩, by simpa using hA.2⟩
      · intro T hT
        rcases Finset.mem_image.mp hT.1 with ⟨A', hA', rfl⟩
        have haA' : (a.val : α) ∈ A' := by simpa using hT.2
        have hAeq : A' = A := hAuniq A' ⟨hA', haA'⟩
        rw [hAeq])
    (by
      intro h
      rcases Finset.mem_image.mp h with ⟨A, hA, hAempty⟩
      exact Q.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        have hxnot : x ∉ B := by
          have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
          simpa using hxcomp
        have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
          simpa using hx
        rw [hAempty] at hxsub
        simpa using hxsub))

/-- Turn a partition of the complement subtype back into a partition of the complement finset. -/
noncomputable def finpartitionSubtypeSdiff {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B})) :
    Finpartition ((Finset.univ : Finset α) \ B) :=
  Finpartition.ofExistsUnique
    (Q.parts.image fun A => A.map (Function.Embedding.subtype fun x : α => x ∉ B))
    (by
      intro p hp x hx
      rcases Finset.mem_image.mp hp with ⟨A, _hA, rfl⟩
      rcases Finset.mem_map.mp hx with ⟨a, _ha, rfl⟩
      simp [a.property])
    (by
      intro x hx
      have hxnot : x ∉ B := by simpa using hx
      let a : {x : α // x ∉ B} := ⟨x, hxnot⟩
      obtain ⟨A, hA, hAuniq⟩ := Q.existsUnique_mem (by simp [a])
      refine ⟨A.map (Function.Embedding.subtype fun x : α => x ∉ B), ?_, ?_⟩
      · exact ⟨Finset.mem_image.mpr ⟨A, hA.1, rfl⟩,
          Finset.mem_map.mpr ⟨a, hA.2, rfl⟩⟩
      · intro T hT
        rcases Finset.mem_image.mp hT.1 with ⟨A', hA', rfl⟩
        rcases Finset.mem_map.mp hT.2 with ⟨a', ha', ha'val⟩
        have haeq : a' = a := Subtype.ext (by simpa [a] using ha'val)
        subst haeq
        have hAeq : A' = A := hAuniq A' ⟨hA', ha'⟩
        rw [hAeq])
    (by
      intro h
      rcases Finset.mem_image.mp h with ⟨A, hA, hAempty⟩
      obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hA
      have hamap : (a.val : α) ∈ A.map (Function.Embedding.subtype fun x : α => x ∉ B) :=
        Finset.mem_map.mpr ⟨a, ha, rfl⟩
      rw [hAempty] at hamap
      simpa using hamap)

/-- Partitions of a complement finset are the same as partitions of the complement subtype. -/
noncomputable def finpartitionSdiffSubtypeCongr {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) :
    Finpartition ((Finset.univ : Finset α) \ B) ≃
      Finpartition (Finset.univ : Finset {x : α // x ∉ B}) where
  toFun := finpartitionSdiffSubtype B
  invFun := finpartitionSubtypeSdiff B
  left_inv Q := by
    ext A
    simp [finpartitionSdiffSubtype, finpartitionSubtypeSdiff, Finset.mem_subtype,
      Finset.mem_map, Finset.mem_image, Finset.map_map]
    constructor
    · rintro ⟨A', hA'mem, hAeq⟩
      have hfilter : {x ∈ A' | x ∉ B} = A' := by
        ext x
        constructor
        · intro hx
          exact (Finset.mem_filter.mp hx).1
        · intro hx
          exact Finset.mem_filter.mpr
            ⟨hx, by
              have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA'mem hx
              simpa using hxcomp⟩
      rw [← hAeq, hfilter]
      exact hA'mem
    · intro hA
      refine ⟨A, hA, ?_⟩
      ext x
      constructor
      · intro hx
        exact (Finset.mem_filter.mp hx).1
      · intro hx
        exact Finset.mem_filter.mpr
          ⟨hx, by
            have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
            simpa using hxcomp⟩
  right_inv Q := by
    ext A
    simp [finpartitionSdiffSubtype, finpartitionSubtypeSdiff, Finset.mem_subtype,
      Finset.mem_map, Finset.mem_image, Finset.map_map]
    constructor
    · rintro ⟨A', hA'mem, hAeq⟩
      have hsubtype : Finset.subtype (fun x => x ∉ B)
          (A'.map (Function.Embedding.subtype fun x : α => x ∉ B)) = A' := by
        ext x
        simp [x.property]
      rw [← hAeq, hsubtype]
      exact hA'mem
    · intro hA
      refine ⟨A, hA, ?_⟩
      ext x
      simp [x.property]

lemma prod_parts_sdiffSubtype (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (∏ A : (finpartitionSdiffSubtype B Q).parts, C.counts A.val.card) =
      ∏ A : Q.parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort (finpartitionSdiffSubtype B Q).parts
      (fun A : Finset {x : α // x ∉ B} => C.counts A.card),
    Finset.prod_coe_sort Q.parts (fun A : Finset α => C.counts A.card)]
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : ∀ A ∈ Q.parts, ∀ D ∈ Q.parts,
      A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) → A = D := by
    intro A hA D hD hsub
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
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun A hA => ?_
  have hmap : (A.subtype (fun x => x ∉ B)).map
      (Function.Embedding.subtype fun x : α => x ∉ B) = A :=
    Finset.subtype_map_of_mem (fun x hx => by
      have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
      simpa using hxcomp)
  have hcard : (A.subtype (fun x => x ∉ B)).card = A.card := by
    rw [← Finset.card_map (Function.Embedding.subtype fun x : α => x ∉ B), hmap]
  rw [hcard]

lemma setWeightFinset_sdiff_eq_setWeightFull (C : CombClass) {α : Type*}
    [Fintype α] [DecidableEq α] (B : Finset α) :
    setWeightFinset C ((Finset.univ : Finset α) \ B) =
      setWeightFull C {x : α // x ∉ B} := by
  unfold setWeightFinset setWeightFull
  exact Fintype.sum_equiv (finpartitionSdiffSubtypeCongr B)
    (fun Q : Finpartition ((Finset.univ : Finset α) \ B) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B}) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q => (prod_parts_sdiffSubtype C B Q).symm)

lemma Finpartition.mem_avoid_of_mem_part {α : Type*} [DecidableEq α] {s B A : Finset α}
    {P : Finpartition s} (hB : B ∈ P.parts) :
    A ∈ (P.avoid B).parts ↔ A ∈ P.parts ∧ A ≠ B := by
  constructor
  · intro hA
    rcases (Finpartition.mem_avoid P).mp hA with ⟨D, hD, hnle, hDA⟩
    have hDB : D ≠ B := by
      intro h
      exact hnle (by rw [h])
    have hdisj : Disjoint D B := P.disjoint hD hB hDB
    have hsdiff : D \ B = D := Finset.sdiff_eq_self_of_disjoint hdisj
    rw [hsdiff] at hDA
    subst hDA
    exact ⟨hD, hDB⟩
  · rintro ⟨hA, hAB⟩
    have hdisj : Disjoint A B := P.disjoint hA hB hAB
    refine (Finpartition.mem_avoid P).mpr ⟨A, hA, ?_, ?_⟩
    · intro hle
      exact P.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        exact (Finset.disjoint_left.mp hdisj) hx (hle hx))
    · exact Finset.sdiff_eq_self_of_disjoint hdisj

/-- Fixing the root block leaves an arbitrary partition of the complement. -/
noncomputable def finpartitionRootFiberEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) {B : Finset α} (hr : r ∈ B) :
    {P : Finpartition (Finset.univ : Finset α) // P.part r = B} ≃
      Finpartition ((Finset.univ : Finset α) \ B) where
  toFun P := P.val.avoid B
  invFun Q :=
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    let P : Finpartition (Finset.univ : Finset α) :=
      Q.extend hBne disjoint_sdiff_self_left hc
    ⟨P, by
      have hBmem : B ∈ P.parts := by
        simp [P, Finpartition.extend]
      exact P.part_eq_of_mem hBmem hr⟩
  left_inv P := by
    apply Subtype.ext
    ext A
    have hruniv : r ∈ (Finset.univ : Finset α) := by simp
    have hBmem : B ∈ P.val.parts := by
      simpa [P.property] using P.val.part_mem.2 hruniv
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    simp [Finpartition.mem_avoid_of_mem_part hBmem, Finpartition.extend]
    constructor
    · rintro (rfl | hA)
      · exact hBmem
      · exact hA.1
    · intro hA
      by_cases h : A = B
      · exact Or.inl h
      · exact Or.inr ⟨hA, h⟩
  right_inv Q := by
    ext A
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    let P : Finpartition (Finset.univ : Finset α) :=
      Q.extend hBne disjoint_sdiff_self_left hc
    have hBmem : B ∈ P.parts := by
      simp [P, Finpartition.extend]
    have hBnot : B ∉ Q.parts := by
      intro h
      have hrcomp : r ∈ (Finset.univ : Finset α) \ B := Q.subset h hr
      simpa [hr] using hrcomp
    simp [P, Finpartition.extend, hBnot]
    constructor
    · rintro ⟨D, hD, _hnle, hDA⟩
      have hdisj : Disjoint D B := by
        rw [Finset.disjoint_left]
        intro x hxD hxB
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hxD
        exact (by simpa [hxB] using hxcomp)
      have hsdiff : D \ B = D := Finset.sdiff_eq_self_of_disjoint hdisj
      rw [hsdiff] at hDA
      subst hDA
      exact hD
    · intro hA
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hxA
        exact (by simpa [hxB] using hxcomp)
      refine ⟨A, hA, ?_, Finset.sdiff_eq_self_of_disjoint hdisj⟩
      intro hle
      exact Q.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        exact (Finset.disjoint_left.mp hdisj) hx (hle hx))

lemma prod_parts_eq_root_mul_avoid (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (∏ A : P.parts, C.counts A.val.card) =
      C.counts B.card * ∏ A : (P.avoid B).parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort P.parts (fun A : Finset α => C.counts A.card),
    Finset.prod_coe_sort (P.avoid B).parts (fun A : Finset α => C.counts A.card)]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  rw [hparts, Finset.prod_insert hBnot]

lemma setWeightFull_root (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) :
    setWeightFull C α =
      ∑ B : {B : Finset α // r ∈ B},
        C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val} := by
  classical
  unfold setWeightFull
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, by simpa using P.mem_part (by simp)⟩
  let w : Finpartition (Finset.univ : Finset α) → ℕ :=
    fun P => ∏ A : P.parts, C.counts A.val.card
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
          C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
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
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            have hruniv : r ∈ (Finset.univ : Finset α) := by simp
            have hBmem : B.val ∈ (rootEquiv.symm Q).val.parts := by
              have hprop := (rootEquiv.symm Q).property
              simpa [hprop] using (rootEquiv.symm Q).val.part_mem.2 hruniv
            change (∏ A : (rootEquiv.symm Q).val.parts, C.counts A.val.card) =
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card
            rw [prod_parts_eq_root_mul_avoid C hBmem]
            have havoid : (rootEquiv.symm Q).val.avoid B.val = Q := by
              exact Equiv.apply_symm_apply rootEquiv Q
            rw [havoid]
  rw [hfiber]
  rw [← Finset.mul_sum]
  change C.counts B.val.card * setWeightFinset C ((Finset.univ : Finset α) \ B.val) =
    C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val}
  rw [setWeightFinset_sdiff_eq_setWeightFull]

/-- `Fin n` is the subtype of `Fin (n+1)` away from the last element. -/
def finEquivNotLast (n : ℕ) : Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} where
  toFun i := ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  invFun x := Fin.castPred x.val x.property
  left_inv i := by
    exact Fin.castPred_castSucc
  right_inv x := by
    apply Subtype.ext
    exact (Fin.castSucc_castPred x.val x.property).symm

/-- Subsets of `Fin n` correspond to subsets of `Fin (n+1)` containing `Fin.last n`. -/
noncomputable def rootBlockEquiv (n : ℕ) :
    Finset (Fin n) ≃ {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} where
  toFun S := ⟨insert (Fin.last n) (S.map Fin.castSuccEmb), by simp⟩
  invFun B := (B.val.subtype fun x => x ≠ Fin.last n).map (finEquivNotLast n).symm.toEmbedding
  left_inv S := by
    ext i
    simp [finEquivNotLast]
  right_inv B := by
    apply Subtype.ext
    ext x
    by_cases hx : x = Fin.last n
    · subst hx
      simpa using B.property
    · have hx' :
        (⟨x, hx⟩ : {x : Fin (n + 1) // x ≠ Fin.last n}) ∈
            B.val.subtype (fun x => x ≠ Fin.last n) ↔ x ∈ B.val := by
        constructor
        · intro h
          simpa using h
        · intro h
          exact Finset.mem_subtype.mpr h
      simp [finEquivNotLast, hx]
      constructor
      · rintro ⟨a, ha, hax⟩
        rw [← hax]
        exact ha
      · intro hxB
        refine ⟨Fin.castPred x hx, ?_, ?_⟩
        · rwa [Fin.castSucc_castPred]
        · exact Fin.castSucc_castPred x hx

@[simp] lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ (rootBlockEquiv n S).val} : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin (n + 1))) \ (rootBlockEquiv n S).val := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
    rootBlockEquiv_card]
  omega

lemma sum_finset_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k : Fin (n + 1), n.choose (k : ℕ) * f (k : ℕ) := by
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
  trans Fintype.card {S : Finset (Fin n) // len S = k} * f (k : ℕ)
  · rw [← Finset.card_univ, Finset.sum_eq_card_nsmul]
    · rw [nsmul_eq_mul]
      refine congrArg (fun m => m * f (k : ℕ)) rfl
    · intro S _hS
      have h := congrArg Fin.val S.property
      simpa using congrArg f h
  · rw [hcard]

lemma CombClass.counts_set_succ (C : CombClass) (n : ℕ) :
    C.set.counts (n + 1)
      = ∑ i : Fin (n + 1),
          n.choose (i : ℕ) * C.counts ((i : ℕ) + 1) *
            C.set.counts (n - (i : ℕ)) := by
  classical
  conv_lhs => rw [show n + 1 = Fintype.card (Fin (n + 1)) by simp]
  rw [← setWeightFull_card C (Fin (n + 1))]
  rw [setWeightFull_root C (Fin.last n)]
  have hblocks :
      (∑ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
          C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
        =
      ∑ S : Finset (Fin n),
        C.counts (S.card + 1) * C.set.counts (n - S.card) := by
    symm
    exact Fintype.sum_equiv (rootBlockEquiv n)
      (fun S : Finset (Fin n) =>
        C.counts (S.card + 1) * C.set.counts (n - S.card))
      (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
        C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
      (by
        intro S
        change C.counts (S.card + 1) * C.set.counts (n - S.card) =
          C.counts ((rootBlockEquiv n S).val.card) *
            setWeightFull C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}
        rw [rootBlockEquiv_card, setWeightFull_card,
          rootBlockEquiv_compl_card])
  rw [hblocks]
  rw [sum_finset_by_card n (fun k => C.counts (k + 1) * C.set.counts (n - k))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.mul_assoc]

/-- The labelled derivative class: an object of size `n` is a `C`-object of size `n+1`. -/
def CombClass.deriv (C : CombClass) : CombClass where
  Obj n := C.Obj (n + 1)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_deriv (C : CombClass) (n : ℕ) :
    C.deriv.counts n = C.counts (n + 1) := rfl

/-- The EGF of the derivative class is the formal derivative of the EGF. -/
theorem CombClass.egf_deriv (C : CombClass) :
    C.deriv.egf = d⁄dX ℚ C.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, coeff_derivative,
    CombClass.coeff_egf]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [Nat.factorial_succ, hn, hnf]
  rw [Nat.factorial_succ]
  push_cast
  ring_nf

/-- The pointed SET recurrence is exactly the labelled product `C' ⋆ SET(C)`. -/
theorem CombClass.egf_set_deriv_lprod (C : CombClass) :
    C.set.deriv.egf = (C.deriv.lprod C.set).egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, CombClass.counts_set_succ,
    CombClass.coeff_egf, CombClass.counts_lprod]
  simp [CombClass.counts_deriv]

/-- The labelled SET construction satisfies `SET(C)' = C' * SET(C)`. -/
theorem CombClass.egf_set_ode (C : CombClass) :
    d⁄dX ℚ C.set.egf = d⁄dX ℚ C.egf * C.set.egf := by
  calc
    d⁄dX ℚ C.set.egf = C.set.deriv.egf := (CombClass.egf_deriv C.set).symm
    _ = (C.deriv.lprod C.set).egf := CombClass.egf_set_deriv_lprod C
    _ = C.deriv.egf * C.set.egf := CombClass.egf_lprod C.deriv C.set
    _ = d⁄dX ℚ C.egf * C.set.egf := by rw [CombClass.egf_deriv C]

end AnalyticCombinatorics.Ch1
