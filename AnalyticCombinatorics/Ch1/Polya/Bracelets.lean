import Mathlib
import AnalyticCombinatorics.Ch1.Polya.Enumeration
import AnalyticCombinatorics.Ch1.Polya.NecklacePhi

/-!
# Binary bracelets

This file applies the Pólya enumeration theorem to binary colorings of `ZMod n`
under the dihedral action.  With Mathlib's multiplication convention for
`DihedralGroup`, the compatible left action is `r i : x ↦ x - i` and
`sr i : x ↦ i - x`.
-/

namespace AnalyticCombinatorics.Ch1.Polya.Bracelets

open scoped BigOperators

attribute [local instance] arrowAction

noncomputable local instance orbitRelDecidableRel {G X : Type*} [Group G] [MulAction G X] :
    DecidableRel (MulAction.orbitRel G X).r :=
  Classical.decRel _

noncomputable local instance orbitQuotientFintype {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] :
    Fintype (MulAction.orbitRel.Quotient G X) :=
  Quotient.fintype (MulAction.orbitRel G X)

noncomputable local instance subtypeFintypeClassical {X : Type*} [Fintype X] (p : X → Prop) :
    Fintype {x // p x} :=
  @Subtype.fintype X p (Classical.decPred p) inferInstance

section Action

/-- The faithful-on-rotations dihedral action on vertices.  Mathlib's multiplication rules force
rotations to act as `x - i` for a left action with reflections `x ↦ i - x`. -/
instance dihedralZModMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul g x :=
    match g with
    | DihedralGroup.r i => x - i
    | DihedralGroup.sr i => i - x
  one_smul x := by
    change x - (0 : ZMod n) = x
    simp
  mul_smul g h x := by
    cases g with
    | r i =>
        cases h with
        | r j =>
            change x - (i + j) = (x - j) - i
            ring
        | sr j =>
            change (j - i) - x = (j - x) - i
            ring
    | sr i =>
        cases h with
        | r j =>
            change (i + j) - x = i - (x - j)
            ring
        | sr j =>
            change x - (j - i) = i - (j - x)
            ring

@[simp]
theorem dihedral_r_smul (n : ℕ) (i x : ZMod n) :
    (DihedralGroup.r i : DihedralGroup n) • x = x - i :=
  rfl

@[simp]
theorem dihedral_sr_smul (n : ℕ) (i x : ZMod n) :
    (DihedralGroup.sr i : DihedralGroup n) • x = i - x :=
  rfl

end Action

section FixedPoints

variable {n : ℕ}

/-- Reflection fixed points are exactly the solutions of `x + x = i`. -/
noncomputable def reflectionFixedByEquivAddSelf (i : ZMod n) :
    MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n) ≃
      {x : ZMod n // x + x = i} where
  toFun x := by
    refine ⟨x.1, ?_⟩
    have hx : i - x.1 = x.1 := x.2
    rw [sub_eq_iff_eq_add] at hx
    simpa [add_comm] using hx.symm
  invFun x := by
    refine ⟨x.1, ?_⟩
    rw [MulAction.mem_fixedBy]
    rw [dihedral_sr_smul, sub_eq_iff_eq_add]
    simpa [add_comm] using x.2.symm
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl

lemma card_add_self_solutions_of_exists [NeZero n] (i : ZMod n)
    (h : ∃ a : ZMod n, a + a = i) :
    Fintype.card {x : ZMod n // x + x = i} = Nat.gcd n 2 := by
  classical
  rcases h with ⟨a, rfl⟩
  let f : ZMod n →+ ZMod n := nsmulAddMonoidHom 2
  calc
    Fintype.card {x : ZMod n // x + x = a + a} =
        Fintype.card (f ⁻¹' {f a}) := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
      intro x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      change x + x = a + a ↔ (2 : ℕ) • x = (2 : ℕ) • a
      constructor
      · intro h
        calc
          (2 : ℕ) • x = x + x := by rw [two_nsmul]
          _ = a + a := h
          _ = (2 : ℕ) • a := by rw [two_nsmul]
      · intro h
        calc
          x + x = (2 : ℕ) • x := by rw [two_nsmul]
          _ = (2 : ℕ) • a := h
          _ = a + a := by rw [two_nsmul]
    _ = Fintype.card f.ker := by
      exact Fintype.card_congr (f.fiberEquivKer a)
    _ = Nat.card f.ker := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.gcd n 2 := by
      rw [IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod n) 2, Nat.card_zmod]

lemma card_add_self_solutions_of_not_exists [NeZero n] (i : ZMod n)
    (h : ¬ ∃ a : ZMod n, a + a = i) :
    Fintype.card {x : ZMod n // x + x = i} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  rw [isEmpty_subtype]
  simpa [not_exists] using h

lemma exists_add_self_eq_of_odd [NeZero n] (hn : Odd n) (i : ZMod n) :
    ∃ x : ZMod n, x + x = i := by
  classical
  have hinj : Function.Injective fun x : ZMod n => x + x := by
    intro x y hxy
    have hdiff : (x - y) + (x - y) = 0 := by
      have hsub : x + x - (y + y) = 0 := sub_eq_zero.mpr hxy
      rw [← hsub]
      ring
    have hzero : x - y = 0 :=
      (ZMod.add_self_eq_zero_iff_eq_zero hn).mp hdiff
    exact sub_eq_zero.mp hzero
  exact (hinj.surjective_of_finite (Equiv.refl (ZMod n))) i

lemma gcd_two_eq_one_of_odd (hn : Odd n) : Nat.gcd n 2 = 1 := by
  have hcop : Nat.Coprime 2 n :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat
  rw [Nat.gcd_comm, Nat.coprime_iff_gcd_eq_one.mp hcop]

lemma gcd_two_eq_two_of_even (heven : n % 2 = 0) : Nat.gcd n 2 = 2 := by
  exact Nat.gcd_eq_right (Nat.dvd_iff_mod_eq_zero.mpr heven)

lemma exists_add_self_eq_of_val_even [NeZero n] (i : ZMod n) (hi : i.val % 2 = 0) :
    ∃ x : ZMod n, x + x = i := by
  have hdiv : 2 ∣ i.val := Nat.dvd_iff_mod_eq_zero.mpr hi
  rcases hdiv with ⟨m, hm⟩
  refine ⟨(m : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val i, hm]
  rw [Nat.cast_mul]
  ring

lemma val_even_of_exists_add_self_eq_of_even [NeZero n] (heven : n % 2 = 0)
    (i : ZMod n) (h : ∃ x : ZMod n, x + x = i) :
    i.val % 2 = 0 := by
  have hdiv : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr heven
  rcases h with ⟨x, hx⟩
  have hcast : (ZMod.castHom hdiv (ZMod 2)) i = 0 := by
    rw [← hx]
    rw [map_add]
    exact CharTwo.add_self_eq_zero ((ZMod.castHom hdiv (ZMod 2)) x)
  have hval : (i.val : ZMod 2) = 0 := by
    simpa [ZMod.castHom_apply] using hcast
  exact Nat.even_iff.mp (ZMod.natCast_eq_zero_iff_even.mp hval)

theorem card_add_self_solutions_of_odd [NeZero n] (hn : Odd n) (i : ZMod n) :
    Fintype.card {x : ZMod n // x + x = i} = 1 := by
  rw [card_add_self_solutions_of_exists i (exists_add_self_eq_of_odd hn i),
    gcd_two_eq_one_of_odd hn]

theorem card_add_self_solutions_of_even [NeZero n] (heven : n % 2 = 0) (i : ZMod n) :
    Fintype.card {x : ZMod n // x + x = i} =
      if i.val % 2 = 0 then 2 else 0 := by
  by_cases hi : i.val % 2 = 0
  · rw [if_pos hi, card_add_self_solutions_of_exists i
      (exists_add_self_eq_of_val_even i hi), gcd_two_eq_two_of_even heven]
  · rw [if_neg hi]
    exact card_add_self_solutions_of_not_exists i
      (fun h => hi (val_even_of_exists_add_self_eq_of_even heven i h))

theorem card_reflection_fixedBy_of_odd [NeZero n] (hn : Odd n) (i : ZMod n) :
    Fintype.card (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) = 1 := by
  rw [Fintype.card_congr (reflectionFixedByEquivAddSelf i),
    card_add_self_solutions_of_odd hn i]

theorem card_reflection_fixedBy_of_even [NeZero n] (heven : n % 2 = 0) (i : ZMod n) :
    Fintype.card (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) =
      if i.val % 2 = 0 then 2 else 0 := by
  rw [Fintype.card_congr (reflectionFixedByEquivAddSelf i),
    card_add_self_solutions_of_even heven i]

end FixedPoints

section ReflectionOrbits

variable {n : ℕ} [NeZero n]

private lemma card_fixedBy_subgroup_eq_card_fixedBy {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] (H : Subgroup G) (h : H) :
    Fintype.card (MulAction.fixedBy X h) =
      Fintype.card (MulAction.fixedBy X (h : G)) := by
  refine Fintype.card_congr (Equiv.subtypeEquivRight ?_)
  intro x
  rfl

private lemma sum_card_fixedBy_reflection_zpowers (i : ZMod n) :
    (∑ h : Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n),
        Fintype.card (MulAction.fixedBy (ZMod n) h)) =
      n + Fintype.card
        (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) := by
  classical
  let s : DihedralGroup n := DihedralGroup.sr i
  let H : Subgroup (DihedralGroup n) := Subgroup.zpowers s
  have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
  have hcast : 2 = orderOf s := by
    subst s
    rw [DihedralGroup.orderOf_sr i]
  let e : Fin 2 ≃ H :=
    (Fin.castOrderIso hcast).toEquiv.trans (finEquivZPowers hs)
  have e0 : ((e 0 : H) : DihedralGroup n) = 1 := by
    change s ^ (((Fin.cast hcast (0 : Fin 2)) : Fin (orderOf s)) : ℕ) = 1
    rw [show (((Fin.cast hcast (0 : Fin 2)) : Fin (orderOf s)) : ℕ) = 0 by rfl]
    simp
  have e1 : ((e 1 : H) : DihedralGroup n) = DihedralGroup.sr i := by
    change s ^ (((Fin.cast hcast (1 : Fin 2)) : Fin (orderOf s)) : ℕ) =
      DihedralGroup.sr i
    rw [show (((Fin.cast hcast (1 : Fin 2)) : Fin (orderOf s)) : ℕ) = 1 by rfl]
    subst s
    simp
  have h0 : Fintype.card (MulAction.fixedBy (ZMod n) (e 0 : H)) = n := by
    rw [card_fixedBy_subgroup_eq_card_fixedBy H (e 0), e0]
    simp [ZMod.card]
  have h1 :
      Fintype.card (MulAction.fixedBy (ZMod n) (e 1 : H)) =
        Fintype.card
          (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) := by
    rw [card_fixedBy_subgroup_eq_card_fixedBy H (e 1), e1]
  calc
    (∑ h : H, Fintype.card (MulAction.fixedBy (ZMod n) h)) =
        ∑ j : Fin 2,
          Fintype.card (MulAction.fixedBy (ZMod n) (e j : H)) := by
      refine Fintype.sum_equiv e.symm _ _ ?_
      intro h
      rw [Equiv.apply_symm_apply]
    _ = n + Fintype.card
        (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) := by
      rw [Fin.sum_univ_two, h0, h1]

theorem card_reflection_zpowers_orbitQuotient_mul_two (i : ZMod n) :
    Fintype.card
        (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) * 2 =
      n + Fintype.card
        (MulAction.fixedBy (ZMod n) (DihedralGroup.sr i : DihedralGroup n)) := by
  classical
  let H : Subgroup (DihedralGroup n) :=
    Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)
  have hburn :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (ZMod n)
  rw [sum_card_fixedBy_reflection_zpowers (n := n) i,
    Fintype.card_zpowers, DihedralGroup.orderOf_sr] at hburn
  exact hburn.symm

theorem card_reflection_zpowers_orbitQuotient_of_odd (hn : Odd n) (i : ZMod n) :
    Fintype.card
        (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) =
      (n + 1) / 2 := by
  have hmul := card_reflection_zpowers_orbitQuotient_mul_two (n := n) i
  rw [card_reflection_fixedBy_of_odd hn i] at hmul
  apply Nat.mul_right_cancel (by decide : 0 < 2)
  rw [hmul, Nat.div_mul_cancel]
  exact even_iff_two_dvd.mp hn.add_one

theorem card_reflection_zpowers_orbitQuotient_of_even (heven : n % 2 = 0) (i : ZMod n) :
    Fintype.card
        (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) =
      if i.val % 2 = 0 then n / 2 + 1 else n / 2 := by
  have hmul := card_reflection_zpowers_orbitQuotient_mul_two (n := n) i
  have hdiv : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr heven
  rw [card_reflection_fixedBy_of_even heven i] at hmul
  by_cases hi : i.val % 2 = 0
  · rw [if_pos hi] at hmul ⊢
    apply Nat.mul_right_cancel (by decide : 0 < 2)
    rw [hmul, Nat.add_mul, Nat.div_mul_cancel hdiv]
  · rw [if_neg hi] at hmul ⊢
    apply Nat.mul_right_cancel (by decide : 0 < 2)
    rw [hmul, Nat.add_zero, Nat.div_mul_cancel hdiv]

theorem card_reflection_fixedBy_colorings_of_odd (hn : Odd n) (i : ZMod n) :
    Fintype.card
        {f : ZMod n → Bool //
          (DihedralGroup.sr i : DihedralGroup n) • f = f} =
      2 ^ ((n + 1) / 2) := by
  rw [AnalyticCombinatorics.Ch1.Polya.card_fixedBy_colorings
    (G := DihedralGroup n) (D := ZMod n) (C := Bool)
    (g := DihedralGroup.sr i)]
  rw [Fintype.card_bool, card_reflection_zpowers_orbitQuotient_of_odd hn i]

theorem card_reflection_fixedBy_colorings_of_even (heven : n % 2 = 0) (i : ZMod n) :
    Fintype.card
        {f : ZMod n → Bool //
          (DihedralGroup.sr i : DihedralGroup n) • f = f} =
      if i.val % 2 = 0 then 2 ^ (n / 2 + 1) else 2 ^ (n / 2) := by
  rw [AnalyticCombinatorics.Ch1.Polya.card_fixedBy_colorings
    (G := DihedralGroup n) (D := ZMod n) (C := Bool)
    (g := DihedralGroup.sr i)]
  rw [Fintype.card_bool, card_reflection_zpowers_orbitQuotient_of_even heven i]
  split <;> rfl

end ReflectionOrbits

section RotationOrbits

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private lemma rotation_zpow_smul_eq_translation_zpow_smul (i x : ZMod n) (m : ℤ) :
    ((DihedralGroup.r i : DihedralGroup n) ^ m) • x =
      ((Multiplicative.ofAdd (-i) : Multiplicative (ZMod n)) ^ m) • x := by
  cases m with
  | ofNat k =>
      simp [zpow_natCast, toAdd_pow, sub_eq_add_neg]
      ring
  | negSucc k =>
      simp [zpow_negSucc, toAdd_pow, sub_eq_add_neg]
      ring

omit [NeZero n] in
private lemma rotation_orbitRel_iff_translation (i x y : ZMod n) :
    MulAction.orbitRel (Subgroup.zpowers (DihedralGroup.r i : DihedralGroup n)) (ZMod n) x y ↔
      MulAction.orbitRel
        (Subgroup.zpowers (Multiplicative.ofAdd (-i) : Multiplicative (ZMod n))) (ZMod n) x y := by
  constructor
  · intro h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    rcases h with ⟨g, hg⟩
    have hgmem := g.property
    rw [Subgroup.mem_zpowers_iff] at hgmem
    rcases hgmem with ⟨m, hm⟩
    refine ⟨⟨(Multiplicative.ofAdd (-i) : Multiplicative (ZMod n)) ^ m, ?_⟩, ?_⟩
    · exact Subgroup.zpow_mem_zpowers _ _
    · change ((g : DihedralGroup n) • y = x) at hg
      rw [← hm] at hg
      change ((Multiplicative.ofAdd (-i) : Multiplicative (ZMod n)) ^ m) • y = x
      rwa [← rotation_zpow_smul_eq_translation_zpow_smul i y m]
  · intro h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    rcases h with ⟨g, hg⟩
    have hgmem := g.property
    rw [Subgroup.mem_zpowers_iff] at hgmem
    rcases hgmem with ⟨m, hm⟩
    refine ⟨⟨(DihedralGroup.r i : DihedralGroup n) ^ m, ?_⟩, ?_⟩
    · exact Subgroup.zpow_mem_zpowers _ _
    · change ((g : Multiplicative (ZMod n)) • y = x) at hg
      rw [← hm] at hg
      change ((DihedralGroup.r i : DihedralGroup n) ^ m) • y = x
      rwa [rotation_zpow_smul_eq_translation_zpow_smul i y m]

theorem card_rotation_zpowers_orbitQuotient (i : ZMod n) :
    Fintype.card
        (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (DihedralGroup.r i : DihedralGroup n)) (ZMod n)) =
      Nat.gcd n i.val := by
  classical
  have hquot :
      Fintype.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers (DihedralGroup.r i : DihedralGroup n)) (ZMod n)) =
        Fintype.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers (Multiplicative.ofAdd (-i) : Multiplicative (ZMod n))) (ZMod n)) := by
    refine Fintype.card_congr (Quotient.congr (Equiv.refl (ZMod n)) ?_)
    intro x y
    exact rotation_orbitRel_iff_translation i x y
  rw [hquot]
  have hneg :
      Nat.gcd n (-i).val = Nat.gcd n i.val := by
    by_cases hi : i = 0
    · simp [hi]
    · rw [ZMod.neg_val i, if_neg hi, Nat.gcd_self_sub_right i.val_le]
  rw [AnalyticCombinatorics.Ch1.Polya.card_zmod_zpowers_orbitQuotient
    (n := n) (k := -i), hneg]

end RotationOrbits

section Sums

lemma card_filter_range_even_mod_two (m : ℕ) :
    ((Finset.range (2 * m)).filter fun j => j % 2 = 0).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      rw [Finset.range_add_one, Finset.filter_insert, if_neg]
      · rw [Finset.range_add_one, Finset.filter_insert, if_pos]
        · rw [Finset.card_insert_of_notMem]
          · simp [ih]
          · simp
        · omega
      · omega

lemma card_filter_range_odd_mod_two (m : ℕ) :
    ((Finset.range (2 * m)).filter fun j => j % 2 = 1).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      rw [Finset.range_add_one, Finset.filter_insert, if_pos]
      · rw [Finset.card_insert_of_notMem]
        · rw [Finset.range_add_one, Finset.filter_insert, if_neg]
          · simp [ih]
          · omega
        · simp
      · omega

lemma sum_zmod_if_val_even_of_even (n : ℕ) [NeZero n] (heven : n % 2 = 0) (A B : ℕ) :
    (∑ i : ZMod n, (if i.val % 2 = 0 then A else B)) =
      n / 2 * A + n / 2 * B := by
  classical
  have hdiv : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr heven
  rcases hdiv with ⟨m, hm⟩
  subst n
  have hzmod_fin :
      (∑ i : ZMod (2 * m), (if i.val % 2 = 0 then A else B)) =
        ∑ i : Fin (2 * m), (if i.val % 2 = 0 then A else B) := by
    cases m with
    | zero => exact (NeZero.ne (2 * 0) rfl).elim
    | succ _ => rfl
  have hfin_range :
      (∑ i : Fin (2 * m), (if i.val % 2 = 0 then A else B)) =
        ∑ i ∈ Finset.range (2 * m), (if i % 2 = 0 then A else B) := by
    refine
      (Finset.sum_fin_eq_sum_range
        (fun i : Fin (2 * m) => if i.val % 2 = 0 then A else B)).trans ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  calc
    (∑ i : ZMod (2 * m), (if i.val % 2 = 0 then A else B)) =
        ∑ i ∈ Finset.range (2 * m), (if i % 2 = 0 then A else B) :=
      hzmod_fin.trans hfin_range
    _ = m * A + m * B := by
      rw [Finset.sum_ite]
      simp [card_filter_range_even_mod_two, card_filter_range_odd_mod_two]
    _ = (2 * m) / 2 * A + (2 * m) / 2 * B := by
      simp

variable {n : ℕ} [NeZero n]

lemma sum_rotation_orbitContrib :
    (∑ i : ZMod n,
        2 ^ Fintype.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers (DihedralGroup.r i : DihedralGroup n)) (ZMod n))) =
      ∑ i : ZMod n, 2 ^ Nat.gcd n i.val := by
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [card_rotation_zpowers_orbitQuotient i]

lemma sum_reflection_orbitContrib_of_odd (hn : Odd n) :
    (∑ i : ZMod n,
        2 ^ Fintype.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n))) =
      n * 2 ^ ((n + 1) / 2) := by
  simp [card_reflection_zpowers_orbitQuotient_of_odd hn, ZMod.card]

lemma sum_reflection_orbitContrib_of_even (heven : n % 2 = 0) :
    (∑ i : ZMod n,
        2 ^ Fintype.card
          (MulAction.orbitRel.Quotient
            (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n))) =
      n / 2 * 2 ^ (n / 2 + 1) + n / 2 * 2 ^ (n / 2) := by
  simp_rw [card_reflection_zpowers_orbitQuotient_of_even heven]
  simp_rw [pow_ite]
  exact sum_zmod_if_val_even_of_even n heven (2 ^ (n / 2 + 1)) (2 ^ (n / 2))

private lemma sum_dihedral_orbitContrib :
    (∑ g : DihedralGroup n,
        2 ^ Fintype.card
          (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (ZMod n))) =
      (∑ i : ZMod n, 2 ^ Nat.gcd n i.val) +
        ∑ i : ZMod n,
          2 ^ Fintype.card
            (MulAction.orbitRel.Quotient
              (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) := by
  classical
  calc
    (∑ g : DihedralGroup n,
        2 ^ Fintype.card
          (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (ZMod n))) =
        ∑ s : (ZMod n) ⊕ (ZMod n),
          2 ^ Fintype.card
            (MulAction.orbitRel.Quotient
              (Subgroup.zpowers (DihedralGroup.equivSum.symm s)) (ZMod n)) := by
      refine Fintype.sum_equiv DihedralGroup.equivSum _ _ ?_
      intro g
      rw [Equiv.symm_apply_apply]
    _ =
        (∑ i : ZMod n,
          2 ^ Fintype.card
            (MulAction.orbitRel.Quotient
              (Subgroup.zpowers (DihedralGroup.r i : DihedralGroup n)) (ZMod n))) +
          ∑ i : ZMod n,
            2 ^ Fintype.card
              (MulAction.orbitRel.Quotient
                (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) := by
      simp [DihedralGroup.equivSum]
      rfl
    _ =
      (∑ i : ZMod n, 2 ^ Nat.gcd n i.val) +
        ∑ i : ZMod n,
          2 ^ Fintype.card
            (MulAction.orbitRel.Quotient
              (Subgroup.zpowers (DihedralGroup.sr i : DihedralGroup n)) (ZMod n)) := by
      rw [sum_rotation_orbitContrib]

end Sums

section Formula

/-- Binary bracelets: Burnside/Pólya formula for the dihedral action on binary strings. -/
theorem card_binary_bracelets (n : ℕ) (hn : 0 < n) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    Fintype.card
        (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → Bool)) * (2 * n) =
      (∑ k : ZMod n, 2 ^ Nat.gcd n k.val) +
        if n % 2 = 1 then
          n * 2 ^ ((n + 1) / 2)
        else
          n / 2 * 2 ^ (n / 2 + 1) + n / 2 * 2 ^ (n / 2) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hpolya :
      Fintype.card
          (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → Bool)) * (2 * n) =
        ∑ g : DihedralGroup n,
          2 ^ Fintype.card
            (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (ZMod n)) := by
    calc
      Fintype.card
            (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → Bool)) * (2 * n) =
          Fintype.card
            (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → Bool)) *
            Fintype.card (DihedralGroup n) := by
        rw [DihedralGroup.card]
      _ =
          ∑ g : DihedralGroup n,
            Fintype.card Bool ^
              Fintype.card
                (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (ZMod n)) := by
        rw [AnalyticCombinatorics.Ch1.Polya.polya_card_orbits_mul_card_group
          (G := DihedralGroup n) (D := ZMod n) (C := Bool)]
      _ =
          ∑ g : DihedralGroup n,
            2 ^ Fintype.card
              (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (ZMod n)) := by
        simp [Fintype.card_bool]
  rw [hpolya, sum_dihedral_orbitContrib]
  by_cases hodd : n % 2 = 1
  · have hnodd : Odd n := Nat.odd_iff.mpr hodd
    rw [if_pos hodd, sum_reflection_orbitContrib_of_odd hnodd]
  · have heven : n % 2 = 0 := by
      have h01 := Nat.mod_two_eq_zero_or_one n
      omega
    rw [if_neg hodd, sum_reflection_orbitContrib_of_even heven]

end Formula

end AnalyticCombinatorics.Ch1.Polya.Bracelets
