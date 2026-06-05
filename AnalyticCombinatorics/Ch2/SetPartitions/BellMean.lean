import Mathlib

/-!
# Bell numbers as finite set partitions

This file uses `Finpartition (Finset.univ : Finset (Fin n))` as the type of genuine
set partitions of `[n]`.
-/

namespace AnalyticCombinatorics.Ch2.SetPartitions

open Finset Function

noncomputable section

-- The equivalences below transport `Finpartition`s through finset/subtype complements;
-- the larger heartbeat budget is for those local `simp`/`grind` calls.
set_option maxHeartbeats 400000

/-- The Bell number as the number of genuine finset partitions of `[n]`. -/
def bellNumber (n : ℕ) : ℕ :=
  Fintype.card (Finpartition (Finset.univ : Finset (Fin n)))

/-- The order isomorphism on finsets induced by an equivalence of labels. -/
private noncomputable def finsetOrderIsoOfEquiv {α β : Type*} (e : α ≃ β) :
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

@[simp] private lemma finsetOrderIsoOfEquiv_apply {α β : Type*} (e : α ≃ β)
    (s : Finset α) :
    finsetOrderIsoOfEquiv e s = s.map e.toEmbedding := by
  rfl

@[simp] private lemma finsetOrderIsoOfEquiv_symm_apply {α β : Type*} (e : α ≃ β)
    (s : Finset β) :
    (finsetOrderIsoOfEquiv e).symm s = s.map e.symm.toEmbedding := by
  rfl

/-- Relabel finpartitions of the full label type along an equivalence of labels. -/
private noncomputable def finpartitionUnivCongr {α β : Type*} [Fintype α] [Fintype β]
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

private lemma bellNumber_univ_card (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Finpartition (Finset.univ : Finset α)) =
      bellNumber (Fintype.card α) := by
  unfold bellNumber
  exact Fintype.card_congr (finpartitionUnivCongr (Fintype.equivFin α))

/-- Turn a partition of a complement finset into a partition of the complement subtype. -/
private noncomputable def finpartitionSdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
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
        have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈
            A.subtype (fun x => x ∉ B) := by
          simpa using hx
        rw [hAempty] at hxsub
        simpa using hxsub))

/-- Turn a partition of the complement subtype back into a partition of the complement finset. -/
private noncomputable def finpartitionSubtypeSdiff {α : Type*} [Fintype α] [DecidableEq α]
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
private noncomputable def finpartitionSdiffSubtypeCongr {α : Type*} [Fintype α]
    [DecidableEq α] (B : Finset α) :
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

private lemma Finpartition.mem_avoid_of_mem_part {α : Type*} [DecidableEq α]
    {s B A : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
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
private noncomputable def finpartitionRootFiberEquiv {α : Type*} [Fintype α] [DecidableEq α]
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

private lemma card_fiber_eq_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := by
      rw [Fintype.card_sigma]

private lemma subtype_notMem_card {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) :
    Fintype.card {x : α // x ∉ B} = Fintype.card α - B.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ B} : Finset α) = (Finset.univ : Finset α) \ B := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ]

/-- Counts partitions by the block containing a distinguished root. -/
private lemma bellNumber_root_sum (α : Type*) [Fintype α] [DecidableEq α] (r : α) :
    Fintype.card (Finpartition (Finset.univ : Finset α)) =
      ∑ B : {B : Finset α // r ∈ B},
        Fintype.card (Finpartition (Finset.univ : Finset {x : α // x ∉ B.val})) := by
  classical
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, by simpa using P.mem_part (by simp)⟩
  rw [card_fiber_eq_sum block]
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
  calc
    Fintype.card {P : Finpartition (Finset.univ : Finset α) // block P = B}
        = Fintype.card {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} := by
          exact Fintype.card_congr fiberEquiv
    _ = Fintype.card (Finpartition ((Finset.univ : Finset α) \ B.val)) := by
          exact Fintype.card_congr rootEquiv
    _ = Fintype.card (Finpartition (Finset.univ : Finset {x : α // x ∉ B.val})) := by
          exact Fintype.card_congr (finpartitionSdiffSubtypeCongr B.val)

/-- `Fin n` is the subtype of `Fin (n+1)` away from the last element. -/
private def finEquivNotLast (n : ℕ) : Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} where
  toFun i := ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  invFun x := Fin.castPred x.val x.property
  left_inv i := by
    exact Fin.castPred_castSucc
  right_inv x := by
    apply Subtype.ext
    exact (Fin.castSucc_castPred x.val x.property).symm

/-- Subsets of `Fin n` correspond to subsets of `Fin (n+1)` containing `Fin.last n`. -/
private noncomputable def rootBlockEquiv (n : ℕ) :
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

@[simp] private lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

private lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [subtype_notMem_card, Fintype.card_fin, rootBlockEquiv_card]
  omega

private lemma bellNumber_succ_eq_sum_subsets (n : ℕ) :
    bellNumber (n + 1) = ∑ S : Finset (Fin n), bellNumber (n - S.card) := by
  classical
  unfold bellNumber
  rw [bellNumber_root_sum (Fin (n + 1)) (Fin.last n)]
  symm
  exact Fintype.sum_equiv (rootBlockEquiv n)
    (fun S : Finset (Fin n) => bellNumber (n - S.card))
    (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
      Fintype.card (Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ∉ B.val})))
    (by
      intro S
      change bellNumber (n - S.card) =
        Fintype.card
          (Finpartition
            (Finset.univ : Finset {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}))
      rw [bellNumber_univ_card, rootBlockEquiv_compl_card])

private lemma sum_finset_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k ∈ Finset.range (n + 1), n.choose k * f k := by
  classical
  let len : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, by
      exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
  have hsplit :
      (∑ S : Finset (Fin n), f S.card) =
        ∑ x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}),
          f x.2.val.card := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv len)
      (fun x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}) =>
        f x.2.val.card)
      (fun S : Finset (Fin n) => f S.card)
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  have hk :
      (∑ k : Fin (n + 1),
          ∑ S : {S : Finset (Fin n) // len S = k}, f S.val.card)
        = ∑ k : Fin (n + 1), n.choose (k : ℕ) * f (k : ℕ) := by
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
  rw [hk]
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hklt : k < n + 1 := by simpa using hk
  simp [hklt]

/-- The Bell recurrence, for genuine finite set partitions. -/
theorem bellNumber_succ (n : ℕ) :
    bellNumber (n + 1) =
      ∑ k ∈ Finset.range (n + 1), n.choose k * bellNumber (n - k) := by
  rw [bellNumber_succ_eq_sum_subsets]
  exact sum_finset_by_card n (fun k => bellNumber (n - k))

@[simp] theorem bellNumber_zero : bellNumber 0 = 1 := by
  classical
  unfold bellNumber
  have huniv : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := by
    simp
  rw [huniv]
  exact Fintype.card_unique

@[simp] theorem bellNumber_one : bellNumber 1 = 1 := by
  simpa using bellNumber_succ 0

@[simp] theorem bellNumber_two : bellNumber 2 = 2 := by
  have h := bellNumber_succ 1
  norm_num at h ⊢
  simpa using h

@[simp] theorem bellNumber_three : bellNumber 3 = 5 := by
  have h := bellNumber_succ 2
  norm_num at h ⊢
  simpa using h

private abbrev MarkedBlock (n : ℕ) :=
  Σ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts

private noncomputable def markedBlockMap (n : ℕ) :
    MarkedBlock n → {A : Finset (Fin n) // A.Nonempty} :=
  fun x => ⟨x.2.val, Finpartition.nonempty_of_mem_parts x.1 x.2.property⟩

private noncomputable def markedBlockFiberEquiv (n : ℕ)
    (A : {A : Finset (Fin n) // A.Nonempty}) :
    {x : MarkedBlock n // markedBlockMap n x = A} ≃
      {P : Finpartition (Finset.univ : Finset (Fin n)) // P.part A.property.choose = A.val} :=
  let a : Fin n := A.property.choose
  let ha : a ∈ A.val := A.property.choose_spec
  { toFun := fun x => ⟨x.val.1, by
      have hval : x.val.2.val = A.val := congrArg Subtype.val x.property
      have haBlock : a ∈ x.val.2.val := by simpa [hval] using ha
      calc
        x.val.1.part a = x.val.2.val := x.val.1.part_eq_of_mem x.val.2.property haBlock
        _ = A.val := hval⟩
    invFun := fun P =>
      ⟨⟨P.val, ⟨A.val, by
        have hmem : P.val.part A.property.choose ∈ P.val.parts := P.val.part_mem.2 (by simp)
        convert hmem using 1
        exact P.property.symm⟩⟩, by
        apply Subtype.ext
        rfl⟩
    left_inv := by
      rintro ⟨⟨P, B⟩, hx⟩
      apply Subtype.ext
      cases B with
      | mk B hB =>
        dsimp at hx ⊢
        have hval : B = A.val := congrArg Subtype.val hx
        subst hval
        simp
    right_inv := by
      intro P
      apply Subtype.ext
      rfl }

private lemma markedBlock_fiber_card (n : ℕ)
    (A : {A : Finset (Fin n) // A.Nonempty}) :
    Fintype.card {x : MarkedBlock n // markedBlockMap n x = A} =
      bellNumber (n - A.val.card) := by
  classical
  let a : Fin n := A.property.choose
  have ha : a ∈ A.val := A.property.choose_spec
  let e₁ := markedBlockFiberEquiv n A
  let e₂ := finpartitionRootFiberEquiv a ha
  calc
    Fintype.card {x : MarkedBlock n // markedBlockMap n x = A}
        = Fintype.card
            {P : Finpartition (Finset.univ : Finset (Fin n)) // P.part a = A.val} := by
          exact Fintype.card_congr e₁
    _ = Fintype.card (Finpartition ((Finset.univ : Finset (Fin n)) \ A.val)) := by
          exact Fintype.card_congr e₂
    _ = Fintype.card (Finpartition (Finset.univ : Finset {x : Fin n // x ∉ A.val})) := by
          exact Fintype.card_congr (finpartitionSdiffSubtypeCongr A.val)
    _ = bellNumber (n - A.val.card) := by
          rw [bellNumber_univ_card, subtype_notMem_card, Fintype.card_fin]

private lemma sum_parts_eq_nonempty_subsets (n : ℕ) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card) =
      ∑ A : {A : Finset (Fin n) // A.Nonempty}, bellNumber (n - A.val.card) := by
  classical
  calc
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card)
        = Fintype.card (MarkedBlock n) := by
          rw [Fintype.card_sigma]
          refine Finset.sum_congr rfl fun P _ => ?_
          simp
    _ = ∑ A : {A : Finset (Fin n) // A.Nonempty},
          Fintype.card {x : MarkedBlock n // markedBlockMap n x = A} := by
          exact card_fiber_eq_sum (markedBlockMap n)
    _ = ∑ A : {A : Finset (Fin n) // A.Nonempty}, bellNumber (n - A.val.card) := by
          refine Finset.sum_congr rfl fun A _ => markedBlock_fiber_card n A

private lemma sum_finsets_empty_or_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℕ) :
    (∑ S : Finset α, f S) =
      f ∅ + ∑ A : {S : Finset α // S.Nonempty}, f A.val := by
  classical
  let e : Finset α ≃ Option {S : Finset α // S.Nonempty} :=
    { toFun := fun S => if h : S.Nonempty then some ⟨S, h⟩ else none
      invFun := fun o => match o with
        | none => ∅
        | some S => S.val
      left_inv := by
        intro S
        by_cases h : S.Nonempty
        · simp [h]
        · simp [h, Finset.not_nonempty_iff_eq_empty.mp h]
      right_inv := by
        intro o
        cases o with
        | none => simp
        | some S => simp [S.property] }
  calc
    (∑ S : Finset α, f S)
        = ∑ o : Option {S : Finset α // S.Nonempty},
            match o with
            | none => f ∅
            | some S => f S.val := by
          exact Fintype.sum_equiv e
            f
            (fun o : Option {S : Finset α // S.Nonempty} =>
              match o with
              | none => f ∅
              | some S => f S.val)
            (by
              intro S
              by_cases h : S.Nonempty
              · simp [e, h]
              · simp [e, h, Finset.not_nonempty_iff_eq_empty.mp h])
    _ = f ∅ + ∑ A : {S : Finset α // S.Nonempty}, f A.val := by
          simp

/-- Addition form of the exact first moment identity. -/
theorem bellNumber_succ_eq_sum_parts_add (n : ℕ) :
    bellNumber (n + 1) =
      (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card) + bellNumber n := by
  classical
  rw [bellNumber_succ_eq_sum_subsets]
  rw [sum_finsets_empty_or_nonempty (α := Fin n) (fun S => bellNumber (n - S.card))]
  rw [sum_parts_eq_nonempty_subsets]
  simp [add_comm]

/-- The total number of blocks over all partitions of `[n]`. -/
theorem sum_parts_eq (n : ℕ) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card) =
      bellNumber (n + 1) - bellNumber n := by
  have h := bellNumber_succ_eq_sum_parts_add n
  omega

/-- Exact mean number of blocks in a uniformly random set partition of `[n]`. -/
theorem expected_blocks_eq (n : ℕ) (hB : 0 < bellNumber n) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)) / bellNumber n
      = bellNumber (n + 1) / bellNumber n - 1 := by
  classical
  let Sℕ : ℕ := ∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card
  have hNat : bellNumber (n + 1) = Sℕ + bellNumber n := bellNumber_succ_eq_sum_parts_add n
  have hRat : ((Sℕ : ℚ) + (bellNumber n : ℚ)) = (bellNumber (n + 1) : ℚ) := by
    exact_mod_cast hNat.symm
  have hBq : (bellNumber n : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hB)
  have hsumCast :
      (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)) = (Sℕ : ℚ) := by
    simp [Sℕ]
  rw [hsumCast]
  change (Sℕ : ℚ) / (bellNumber n : ℚ) =
    (bellNumber (n + 1) : ℚ) / (bellNumber n : ℚ) - 1
  rw [← hRat]
  field_simp [hBq]
  ring

end

end AnalyticCombinatorics.Ch2.SetPartitions
