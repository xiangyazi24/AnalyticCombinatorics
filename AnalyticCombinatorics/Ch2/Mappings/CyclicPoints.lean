import Mathlib
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQ
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQSharp
import AnalyticCombinatorics.Ch2.Mappings.ConnectedMappings

/-!
# Cyclic points in random mappings

This file counts mappings for which a fixed point is cyclic and derives the
expected number of cyclic points from Ramanujan's finite `Q`-function.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

abbrev NonBase {n : ℕ} (x₀ : Fin n) : Type :=
  {x : Fin n // x ≠ x₀}

abbrev TailEmbedding {n : ℕ} (x₀ : Fin n) (l : ℕ) : Type :=
  Fin l ↪ NonBase x₀

abbrev FreeDomain {n : ℕ} {x₀ : Fin n} {l : ℕ} (e : TailEmbedding x₀ l) : Type :=
  {x : NonBase x₀ // x ∉ Set.range e}

abbrev CycleFiberData {n : ℕ} (x₀ : Fin n) (l : ℕ) : Type :=
  Sigma fun e : TailEmbedding x₀ l => FreeDomain e → Fin n

def nextTailValue {n l : ℕ} {x₀ : Fin n} (e : TailEmbedding x₀ l) (i : Fin l) :
    Fin n :=
  if h : i.1 + 1 < l then (e ⟨i.1 + 1, h⟩).1 else x₀

def firstCycleValue {n l : ℕ} {x₀ : Fin n} (e : TailEmbedding x₀ l) : Fin n :=
  if h : 0 < l then (e ⟨0, h⟩).1 else x₀

def mapOfCycleFiberData {n l : ℕ} {x₀ : Fin n} (d : CycleFiberData x₀ l) :
    Fin n → Fin n :=
  fun x =>
    if hx : x = x₀ then
      firstCycleValue d.1
    else
      let y : NonBase x₀ := ⟨x, hx⟩
      if hy : y ∈ Set.range d.1 then
        nextTailValue d.1 (Classical.choose hy)
      else
        d.2 ⟨y, hy⟩

@[simp] lemma firstCycleValue_of_pos {n l : ℕ} {x₀ : Fin n}
    (e : TailEmbedding x₀ l) (hl : 0 < l) :
    firstCycleValue e = (e ⟨0, hl⟩).1 := by
  simp [firstCycleValue, hl]

@[simp] lemma firstCycleValue_of_zero {n : ℕ} {x₀ : Fin n}
    (e : TailEmbedding x₀ 0) :
    firstCycleValue e = x₀ := by
  simp [firstCycleValue]

lemma mapOfCycleFiberData_base {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) :
    mapOfCycleFiberData d x₀ = firstCycleValue d.1 := by
  simp [mapOfCycleFiberData]

lemma mapOfCycleFiberData_base_of_pos {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) (hl : 0 < l) :
    mapOfCycleFiberData d x₀ = (d.1 ⟨0, hl⟩).1 := by
  rw [mapOfCycleFiberData_base, firstCycleValue_of_pos]

lemma mapOfCycleFiberData_base_of_zero {n : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ 0) :
    mapOfCycleFiberData d x₀ = x₀ := by
  rw [mapOfCycleFiberData_base, firstCycleValue_of_zero]

lemma mapOfCycleFiberData_tail {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) (i : Fin l) :
    mapOfCycleFiberData d (d.1 i).1 = nextTailValue d.1 i := by
  classical
  have hx : (d.1 i).1 ≠ x₀ := (d.1 i).2
  have hy : (⟨(d.1 i).1, hx⟩ : NonBase x₀) ∈ Set.range d.1 := by
    exact ⟨i, rfl⟩
  simp [mapOfCycleFiberData, hx, hy]

lemma mapOfCycleFiberData_free {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) (x : FreeDomain d.1) :
    mapOfCycleFiberData d x.1.1 = d.2 x := by
  classical
  have hx : x.1.1 ≠ x₀ := x.1.2
  have hy : (⟨x.1.1, hx⟩ : NonBase x₀) ∉ Set.range d.1 := by
    simpa using x.2
  simp [mapOfCycleFiberData, hx, hy]

lemma mapOfCycleFiberData_iterate_tail {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) :
    ∀ m : ℕ, (hm : m < l) →
      (mapOfCycleFiberData d)^[m + 1] x₀ = (d.1 ⟨m, hm⟩).1
  | 0, hm => by
      simpa using mapOfCycleFiberData_base_of_pos d hm
  | m + 1, hm => by
      have hm' : m < l := Nat.lt_trans (Nat.lt_succ_self m) hm
      have hstep : m + 1 < l := hm
      calc
        (mapOfCycleFiberData d)^[m + 1 + 1] x₀ =
            mapOfCycleFiberData d ((mapOfCycleFiberData d)^[m + 1] x₀) := by
              rw [Function.iterate_succ_apply']
        _ = mapOfCycleFiberData d (d.1 ⟨m, hm'⟩).1 := by
              rw [mapOfCycleFiberData_iterate_tail d m hm']
        _ = (d.1 ⟨m + 1, hm⟩).1 := by
              rw [mapOfCycleFiberData_tail]
              simp [nextTailValue, hstep]

lemma mapOfCycleFiberData_return {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) :
    (mapOfCycleFiberData d)^[l + 1] x₀ = x₀ := by
  classical
  cases l with
  | zero =>
      simpa using mapOfCycleFiberData_base_of_zero d
  | succ l =>
      have hlast : l < l + 1 := Nat.lt_succ_self l
      calc
        (mapOfCycleFiberData d)^[l + 1 + 1] x₀ =
            mapOfCycleFiberData d ((mapOfCycleFiberData d)^[l + 1] x₀) := by
              rw [Function.iterate_succ_apply']
        _ = mapOfCycleFiberData d (d.1 ⟨l, hlast⟩).1 := by
              rw [mapOfCycleFiberData_iterate_tail d l hlast]
        _ = x₀ := by
              rw [mapOfCycleFiberData_tail]
              simp [nextTailValue]

lemma mapOfCycleFiberData_no_early_return {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) {m : ℕ} (hmpos : 0 < m) (hmlt : m < l + 1) :
    (mapOfCycleFiberData d)^[m] x₀ ≠ x₀ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hr : r < l := by omega
  rw [mapOfCycleFiberData_iterate_tail d r hr]
  exact (d.1 ⟨r, hr⟩).2

lemma mapOfCycleFiberData_periodic {n l : ℕ} {x₀ : Fin n}
    (d : CycleFiberData x₀ l) :
    PeriodicPoint (mapOfCycleFiberData d) x₀ := by
  exact ⟨l + 1, Nat.succ_pos l, mapOfCycleFiberData_return d⟩

lemma orbit_tail_no_repeat {n l : ℕ} {x₀ : Fin n} {f : Fin n → Fin n}
    (hret : f^[l + 1] x₀ = x₀)
    (hmin : ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀)
    {a b : ℕ} (ha : 0 < a) (hb : b ≤ l) (hab : a < b)
    (heq : f^[a] x₀ = f^[b] x₀) : False := by
  let m := l + 1 - b + a
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmlt : m < l + 1 := by
    dsimp [m]
    omega
  have htail : l + 1 - b + b = l + 1 := by omega
  have hmret : f^[m] x₀ = x₀ := by
    dsimp [m]
    calc
      f^[l + 1 - b + a] x₀ =
          f^[l + 1 - b] (f^[a] x₀) := by
            rw [← Function.iterate_add_apply]
      _ = f^[l + 1 - b] (f^[b] x₀) := by
            rw [heq]
      _ = f^[l + 1 - b + b] x₀ := by
            rw [Function.iterate_add_apply]
      _ = f^[l + 1] x₀ := by
            rw [htail]
      _ = x₀ := hret
  exact hmin m hmpos hmlt hmret

def orbitTailEmbedding {n l : ℕ} {x₀ : Fin n} (f : Fin n → Fin n)
    (hret : f^[l + 1] x₀ = x₀)
    (hmin : ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀) :
    TailEmbedding x₀ l where
  toFun i := by
    refine ⟨f^[i.1 + 1] x₀, ?_⟩
    exact hmin (i.1 + 1) (Nat.succ_pos i.1) (Nat.succ_lt_succ i.2)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval : f^[i.1 + 1] x₀ = f^[j.1 + 1] x₀ := congrArg Subtype.val hij
    rcases lt_trichotomy i.1 j.1 with hijlt | hijeq | hjilt
    · exfalso
      exact orbit_tail_no_repeat hret hmin (Nat.succ_pos i.1)
        (Nat.succ_le_of_lt j.2) (Nat.succ_lt_succ hijlt) hval
    · exact hijeq
    · exfalso
      exact orbit_tail_no_repeat hret hmin (Nat.succ_pos j.1)
        (Nat.succ_le_of_lt i.2) (Nat.succ_lt_succ hjilt) hval.symm

@[simp] lemma orbitTailEmbedding_apply_coe {n l : ℕ} {x₀ : Fin n}
    {f : Fin n → Fin n}
    {hret : f^[l + 1] x₀ = x₀}
    {hmin : ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀}
    (i : Fin l) :
    ((orbitTailEmbedding f hret hmin i : NonBase x₀) : Fin n) = f^[i.1 + 1] x₀ := by
  rfl

def cycleFiberToFirstReturn {n l : ℕ} {x₀ : Fin n} (d : CycleFiberData x₀ l) :
    {f : Fin n → Fin n //
      f^[l + 1] x₀ = x₀ ∧
        ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀} :=
  ⟨mapOfCycleFiberData d, mapOfCycleFiberData_return d,
    fun m hmpos hmlt => mapOfCycleFiberData_no_early_return d (m := m) hmpos hmlt⟩

def cycleFiberDataOfFirstReturn {n l : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n //
      f^[l + 1] x₀ = x₀ ∧
        ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀}) :
    CycleFiberData x₀ l := by
  let e : TailEmbedding x₀ l := orbitTailEmbedding F.1 F.2.1 F.2.2
  exact ⟨e, fun x => F.1 x.1.1⟩

lemma mapOfCycleFiberData_of_firstReturn {n l : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n //
      f^[l + 1] x₀ = x₀ ∧
        ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀}) :
    mapOfCycleFiberData (cycleFiberDataOfFirstReturn F) = F.1 := by
  classical
  funext x
  let e : TailEmbedding x₀ l := orbitTailEmbedding F.1 F.2.1 F.2.2
  change mapOfCycleFiberData (⟨e, fun x => F.1 x.1.1⟩ : CycleFiberData x₀ l) x = F.1 x
  by_cases hx : x = x₀
  · subst x
    by_cases hl : 0 < l
    · simp [mapOfCycleFiberData_base_of_pos, e, hl]
    · have hl0 : l = 0 := Nat.eq_zero_of_not_pos hl
      subst l
      calc
        mapOfCycleFiberData (⟨e, fun x => F.1 x.1.1⟩ : CycleFiberData x₀ 0) x₀ = x₀ := by
          exact mapOfCycleFiberData_base_of_zero _
        _ = F.1 x₀ := by
          simpa [Function.iterate_one] using F.2.1.symm
  · let y : NonBase x₀ := ⟨x, hx⟩
    by_cases hy : y ∈ Set.range e
    · let i : Fin l := Classical.choose hy
      have hi : e i = y := Classical.choose_spec hy
      have hx_iter : x = F.1^[i.1 + 1] x₀ := by
        have hval := congrArg Subtype.val hi
        simpa [e, y] using hval.symm
      have hfx_iter : F.1 x = F.1^[i.1 + 1 + 1] x₀ := by
        rw [hx_iter]
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          (Function.iterate_succ_apply' F.1 (i.1 + 1) x₀).symm
      by_cases hnext : i.1 + 1 < l
      · calc
          mapOfCycleFiberData (⟨e, fun x => F.1 x.1.1⟩ : CycleFiberData x₀ l) x =
              nextTailValue e i := by
                have hxy : x = (e i).1 := by
                  have hval := congrArg Subtype.val hi
                  simpa [y] using hval.symm
                rw [hxy]
                exact mapOfCycleFiberData_tail _ i
          _ = (e ⟨i.1 + 1, hnext⟩).1 := by
                simp [nextTailValue, hnext]
          _ = F.1^[i.1 + 1 + 1] x₀ := by
                simp [e]
          _ = F.1 x := hfx_iter.symm
      · have hilast : i.1 + 1 = l := by omega
        calc
          mapOfCycleFiberData (⟨e, fun x => F.1 x.1.1⟩ : CycleFiberData x₀ l) x =
              nextTailValue e i := by
                have hxy : x = (e i).1 := by
                  have hval := congrArg Subtype.val hi
                  simpa [y] using hval.symm
                rw [hxy]
                exact mapOfCycleFiberData_tail _ i
          _ = x₀ := by
                simp [nextTailValue, hnext]
          _ = F.1^[i.1 + 1 + 1] x₀ := by
                rw [hilast]
                exact F.2.1.symm
          _ = F.1 x := hfx_iter.symm
    · have hy' : (⟨x, hx⟩ : NonBase x₀) ∉ Set.range e := hy
      simp [mapOfCycleFiberData, hx, hy', e]

def cycleFiberFirstReturnEquiv {n l : ℕ} (x₀ : Fin n) :
    CycleFiberData x₀ l ≃
      {f : Fin n → Fin n //
        f^[l + 1] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀} where
  toFun := cycleFiberToFirstReturn
  invFun := cycleFiberDataOfFirstReturn
  left_inv d := by
    classical
    rcases d with ⟨e, g⟩
    let d : CycleFiberData x₀ l := ⟨e, g⟩
    let e' : TailEmbedding x₀ l :=
      orbitTailEmbedding (mapOfCycleFiberData d)
        (mapOfCycleFiberData_return d)
        (fun m hmpos hmlt => mapOfCycleFiberData_no_early_return d (m := m) hmpos hmlt)
    have he : e' = e := by
      ext i
      dsimp [e']
      rw [orbitTailEmbedding_apply_coe]
      exact congrArg Fin.val (by
        simpa [d] using mapOfCycleFiberData_iterate_tail d i.1 i.2)
    change (⟨e', fun x : FreeDomain e' => mapOfCycleFiberData d x.1.1⟩ :
        CycleFiberData x₀ l) = ⟨e, g⟩
    rw [he]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext x
      exact mapOfCycleFiberData_free d x
  right_inv F := by
    apply Subtype.ext
    exact mapOfCycleFiberData_of_firstReturn F

theorem card_firstReturnFiber_length {n l : ℕ} (x₀ : Fin n) :
    Fintype.card
      {f : Fin n → Fin n //
        f^[l + 1] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀} =
      Fintype.card (CycleFiberData x₀ l) := by
  classical
  let P : (Fin n → Fin n) → Prop :=
    fun f => f^[l + 1] x₀ = x₀ ∧
      ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀
  change @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
    Fintype.card (CycleFiberData x₀ l)
  calc
    @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card {f : Fin n → Fin n // P f} (Subtype.fintype P) := by
          exact @Fintype.card_congr {f : Fin n → Fin n // P f} {f : Fin n → Fin n // P f}
            CategoryTheory.FinCategory.fintypeObj (Subtype.fintype P) (Equiv.refl _)
    _ = Fintype.card (CycleFiberData x₀ l) := by
          exact (Fintype.card_congr (cycleFiberFirstReturnEquiv (n := n) (l := l) x₀)).symm

lemma card_nonBase {n : ℕ} (x₀ : Fin n) :
    Fintype.card (NonBase x₀) = n - 1 := by
  classical
  change Fintype.card {x : Fin n // ¬ x = x₀} = n - 1
  rw [Fintype.card_subtype_compl (fun x : Fin n => x = x₀)]
  rw [Fintype.card_fin, Fintype.card_subtype_eq x₀]

lemma card_tailEmbedding {n l : ℕ} (x₀ : Fin n) :
    Fintype.card (TailEmbedding x₀ l) = (n - 1).descFactorial l := by
  classical
  simp [TailEmbedding, card_nonBase x₀]

lemma card_freeDomain {n l : ℕ} {x₀ : Fin n} (e : TailEmbedding x₀ l) :
    Fintype.card (FreeDomain e) = n - 1 - l := by
  classical
  change Fintype.card {x : NonBase x₀ // ¬ x ∈ Set.range e} = n - 1 - l
  rw [Fintype.card_subtype_compl (fun x : NonBase x₀ => x ∈ Set.range e)]
  rw [Fintype.card_range e, Fintype.card_fin, card_nonBase x₀]

lemma card_freeDomain_of_mem_Icc {n k : ℕ} {x₀ : Fin n}
    (hk : k ∈ Finset.Icc 1 n) (e : TailEmbedding x₀ (k - 1)) :
    Fintype.card (FreeDomain e) = n - k := by
  classical
  have hbase := card_freeDomain e
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  omega

lemma card_cycleFiberData_of_mem_Icc {n k : ℕ} (x₀ : Fin n)
    (hk : k ∈ Finset.Icc 1 n) :
    Fintype.card (CycleFiberData x₀ (k - 1)) =
      (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  change Fintype.card (Sigma fun e : TailEmbedding x₀ (k - 1) => FreeDomain e → Fin n) =
      (n - 1).descFactorial (k - 1) * n ^ (n - k)
  rw [Fintype.card_sigma]
  calc
    (∑ e : TailEmbedding x₀ (k - 1), Fintype.card (FreeDomain e → Fin n)) =
        ∑ e : TailEmbedding x₀ (k - 1), n ^ (n - k) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [Fintype.card_fun]
          rw [Fintype.card_fin, card_freeDomain_of_mem_Icc hk e]
    _ = Fintype.card (TailEmbedding x₀ (k - 1)) * n ^ (n - k) := by
          simp
    _ = (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          rw [card_tailEmbedding x₀]

theorem card_firstReturnFiber {n k : ℕ} (x₀ : Fin n)
    (hk : k ∈ Finset.Icc 1 n) :
    Fintype.card
      {f : Fin n → Fin n //
        f^[k] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < k → f^[m] x₀ ≠ x₀} =
      (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  let P : (Fin n → Fin n) → Prop :=
    fun f => f^[k] x₀ = x₀ ∧
      ∀ m : ℕ, 0 < m → m < k → f^[m] x₀ ≠ x₀
  change @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
    (n - 1).descFactorial (k - 1) * n ^ (n - k)
  calc
    @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card {f : Fin n → Fin n // P f} (Subtype.fintype P) := by
          exact @Fintype.card_congr {f : Fin n → Fin n // P f} {f : Fin n → Fin n // P f}
            CategoryTheory.FinCategory.fintypeObj (Subtype.fintype P) (Equiv.refl _)
    _ = Fintype.card (CycleFiberData x₀ (k - 1)) := by
          simpa [P, hsucc] using card_firstReturnFiber_length (n := n) (l := k - 1) x₀
    _ = (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          exact card_cycleFiberData_of_mem_Icc x₀ hk

def firstReturnNat {n : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀}) : ℕ :=
  Nat.find F.2

lemma firstReturnNat_pos {n : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀}) :
    0 < firstReturnNat F := by
  exact (Nat.find_spec F.2).1

lemma firstReturnNat_return {n : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀}) :
    F.1^[firstReturnNat F] x₀ = x₀ := by
  exact (Nat.find_spec F.2).2

lemma firstReturnNat_no_early {n : ℕ} {x₀ : Fin n}
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀})
    {m : ℕ} (hmpos : 0 < m) (hmlt : m < firstReturnNat F) :
    F.1^[m] x₀ ≠ x₀ := by
  intro hm
  exact Nat.find_min F.2 hmlt ⟨hmpos, hm⟩

lemma firstReturnNat_le_card {n : ℕ} {x₀ : Fin n} (hn : 0 < n)
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀}) :
    firstReturnNat F ≤ n := by
  classical
  let k := firstReturnNat F
  have hkpos : 0 < k := firstReturnNat_pos F
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  let e : TailEmbedding x₀ (k - 1) :=
    orbitTailEmbedding F.1
      (by simpa [k, hsucc] using firstReturnNat_return F)
      (fun m hmpos hmlt hmret => by
        have hmk : m < k := by simpa [hsucc] using hmlt
        exact firstReturnNat_no_early F hmpos hmk hmret)
  have hcard := Fintype.card_le_of_embedding e
  have hsub : k - 1 ≤ n - 1 := by
    simpa [Fintype.card_fin, card_nonBase x₀] using hcard
  omega

def firstReturnIndex {n : ℕ} (x₀ : Fin n) (hn : 0 < n)
    (F : {f : Fin n → Fin n // PeriodicPoint f x₀}) :
    {k : ℕ // k ∈ Finset.Icc 1 n} :=
  ⟨firstReturnNat F, by
    exact Finset.mem_Icc.mpr ⟨firstReturnNat_pos F, firstReturnNat_le_card hn F⟩⟩

def firstReturnIndexFiberEquiv {n : ℕ} (x₀ : Fin n) (hn : 0 < n)
    (K : {k : ℕ // k ∈ Finset.Icc 1 n}) :
    {F : {f : Fin n → Fin n // PeriodicPoint f x₀} //
        firstReturnIndex x₀ hn F = K} ≃
      {f : Fin n → Fin n //
        f^[K.1] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < K.1 → f^[m] x₀ ≠ x₀} where
  toFun F := by
    have hk : firstReturnNat F.1 = K.1 := congrArg Subtype.val F.2
    refine ⟨F.1.1, ?_, ?_⟩
    · simpa [hk] using firstReturnNat_return F.1
    · intro m hmpos hmlt
      exact firstReturnNat_no_early F.1 hmpos (by simpa [hk] using hmlt)
  invFun G := by
    have hkpos : 0 < K.1 := (Finset.mem_Icc.mp K.2).1
    let P : PeriodicPoint G.1 x₀ := ⟨K.1, hkpos, G.2.1⟩
    refine ⟨⟨G.1, P⟩, ?_⟩
    apply Subtype.ext
    dsimp [firstReturnIndex]
    apply le_antisymm
    · exact Nat.find_min' P ⟨hkpos, G.2.1⟩
    · apply le_of_not_gt
      intro hlt
      have hspec := Nat.find_spec P
      exact G.2.2 (Nat.find P) hspec.1 hlt hspec.2
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv G := by
    apply Subtype.ext
    rfl

theorem card_periodicAt {n : ℕ} (x₀ : Fin n) (hn : 0 < n) :
    Fintype.card {f : Fin n → Fin n // PeriodicPoint f x₀}
      = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  let P : (Fin n → Fin n) → Prop := fun f => PeriodicPoint f x₀
  let A : Type := {f : Fin n → Fin n // P f}
  let B : Type := {k : ℕ // k ∈ Finset.Icc 1 n}
  letI : Fintype A := Subtype.fintype P
  letI : Fintype B := by
    dsimp [B]
    infer_instance
  let idx : A → B := firstReturnIndex x₀ hn
  change @Fintype.card A CategoryTheory.FinCategory.fintypeObj =
    ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k)
  calc
    @Fintype.card A CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card A (Subtype.fintype P) := by
          exact @Fintype.card_congr A A CategoryTheory.FinCategory.fintypeObj
            (Subtype.fintype P) (Equiv.refl A)
    _ = ∑ K : B, Fintype.card {F : A // idx F = K} := by
          exact ForestCountNS.Complete.card_eq_sum_fintype_fiber idx
    _ = ∑ K : B, (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1) := by
          refine Finset.sum_congr rfl ?_
          intro K _
          change Fintype.card
              {F : {f : Fin n → Fin n // PeriodicPoint f x₀} //
                firstReturnIndex x₀ hn F = K} =
            (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1)
          let Q : (Fin n → Fin n) → Prop :=
            fun f => f^[K.1] x₀ = x₀ ∧
              ∀ m : ℕ, 0 < m → m < K.1 → f^[m] x₀ ≠ x₀
          calc
            Fintype.card
                {F : {f : Fin n → Fin n // PeriodicPoint f x₀} //
                  firstReturnIndex x₀ hn F = K} =
                @Fintype.card {f : Fin n → Fin n // Q f} (Subtype.fintype Q) := by
                  exact Fintype.card_congr (firstReturnIndexFiberEquiv x₀ hn K)
            _ = @Fintype.card {f : Fin n → Fin n // Q f}
                  CategoryTheory.FinCategory.fintypeObj := by
                  exact @Fintype.card_congr {f : Fin n → Fin n // Q f}
                    {f : Fin n → Fin n // Q f} (Subtype.fintype Q)
                    CategoryTheory.FinCategory.fintypeObj (Equiv.refl _)
            _ = (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1) := by
                  simpa [Q] using card_firstReturnFiber x₀ K.2
    _ = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          let s := Finset.Icc 1 n
          simpa [B, s] using
            (Finset.sum_attach s
              (fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k)))

def periodicPairSwapEquiv (n : ℕ) :
    (Sigma fun f : Fin n → Fin n => {x : Fin n // PeriodicPoint f x}) ≃
      (Sigma fun x : Fin n => {f : Fin n → Fin n // PeriodicPoint f x}) where
  toFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  invFun P := ⟨P.2.1, ⟨P.1, P.2.2⟩⟩
  left_inv P := by
    rcases P with ⟨f, x, hx⟩
    rfl
  right_inv P := by
    rcases P with ⟨x, f, hx⟩
    rfl

lemma periodicSubtype_card_eq_finset_card {n : ℕ} (f : Fin n → Fin n) :
    Fintype.card {x : Fin n // PeriodicPoint f x} = (periodicPointsFinset f).card := by
  classical
  rw [Fintype.card_subtype]
  simp [periodicPointsFinset]

lemma sum_periodicPointsFinset_card_eq_sum_periodicAt_nat (n : ℕ) :
    (∑ f : Fin n → Fin n, (periodicPointsFinset f).card) =
      ∑ x : Fin n,
        @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
          CategoryTheory.FinCategory.fintypeObj := by
  classical
  calc
    (∑ f : Fin n → Fin n, (periodicPointsFinset f).card) =
        ∑ f : Fin n → Fin n,
          Fintype.card {x : Fin n // PeriodicPoint f x} := by
          refine Finset.sum_congr rfl ?_
          intro f _
          calc
            (periodicPointsFinset f).card =
                @Fintype.card {x : Fin n // PeriodicPoint f x}
                  CategoryTheory.FinCategory.fintypeObj := by
                  exact (periodicSubtype_card_eq_finset_card f).symm
            _ = @Fintype.card {x : Fin n // PeriodicPoint f x}
                  (Subtype.fintype (fun x : Fin n => PeriodicPoint f x)) := by
                  exact @Fintype.card_congr {x : Fin n // PeriodicPoint f x}
                    {x : Fin n // PeriodicPoint f x}
                    CategoryTheory.FinCategory.fintypeObj
                    (Subtype.fintype (fun x : Fin n => PeriodicPoint f x)) (Equiv.refl _)
    _ = Fintype.card (Sigma fun f : Fin n → Fin n =>
          {x : Fin n // PeriodicPoint f x}) := by
          exact Fintype.card_sigma.symm
    _ = Fintype.card (Sigma fun x : Fin n =>
          {f : Fin n → Fin n // PeriodicPoint f x}) := by
          exact Fintype.card_congr (periodicPairSwapEquiv n)
    _ = ∑ x : Fin n,
          @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            (Subtype.fintype (fun f : Fin n → Fin n => PeriodicPoint f x)) := by
          exact Fintype.card_sigma
    _ = ∑ x : Fin n,
          @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact @Fintype.card_congr
            {f : Fin n → Fin n // PeriodicPoint f x}
            {f : Fin n → Fin n // PeriodicPoint f x}
            (Subtype.fintype (fun f : Fin n → Fin n => PeriodicPoint f x))
            CategoryTheory.FinCategory.fintypeObj (Equiv.refl _)

lemma sum_periodicPointsFinset_card_eq_sum_periodicAt (n : ℕ) :
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) =
      ∑ x : Fin n,
        (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
          CategoryTheory.FinCategory.fintypeObj : ℝ) := by
  exact_mod_cast sum_periodicPointsFinset_card_eq_sum_periodicAt_nat n

lemma periodicAt_sum_eq_q_scaled {n : ℕ} (hn : 0 < n) :
    (((∑ k ∈ Finset.Icc 1 n,
        (n - 1).descFactorial (k - 1) * n ^ (n - k)) : ℕ) : ℝ) =
      (n : ℝ) ^ (n - 1) *
        AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
  calc
    (((∑ k ∈ Finset.Icc 1 n,
        (n - 1).descFactorial (k - 1) * n ^ (n - k)) : ℕ) : ℝ) =
        (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) := by
          rw [card_connectedMappings hn]
    _ = (n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
          exact card_connectedMappings_eq_q hn

theorem expected_cyclicPoints_eq_q {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n =
      AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
  classical
  let S : ℕ :=
    ∑ k ∈ Finset.Icc 1 n,
      (n - 1).descFactorial (k - 1) * n ^ (n - k)
  have hdouble :
      (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) =
        (n : ℝ) * (S : ℝ) := by
    rw [sum_periodicPointsFinset_card_eq_sum_periodicAt n]
    have hpoint :
        ∀ x : Fin n,
          (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj : ℝ) = (S : ℝ) := by
      intro x
      exact congrArg Nat.cast (card_periodicAt x hn)
    calc
      (∑ x : Fin n,
          (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj : ℝ)) =
          ∑ _x : Fin n, (S : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact hpoint x
      _ = (n : ℝ) * (S : ℝ) := by
            simp [Fintype.card_fin]
  have hS :
      (S : ℝ) =
        (n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
    simpa [S] using periodicAt_sum_eq_q_scaled hn
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hpow_ne : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hnne
  have hpow : (n : ℝ) ^ n = (n : ℝ) * (n : ℝ) ^ (n - 1) := by
    have hsplit : n = 1 + (n - 1) := by omega
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ (1 + (n - 1)) := by
        exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
      _ = (n : ℝ) * (n : ℝ) ^ (n - 1) := by
        rw [pow_add, pow_one]
  calc
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n =
        ((n : ℝ) * (S : ℝ)) / (n : ℝ)^n := by rw [hdouble]
    _ = ((n : ℝ) * ((n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n)) /
          ((n : ℝ) * (n : ℝ) ^ (n - 1)) := by
          rw [hS, hpow]
    _ = AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
          field_simp [hnne, hpow_ne]

theorem expected_cyclicPoints_isEquivalent :
    (fun n : ℕ => (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n:ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi * n / 2)) := by
  classical
  have hevent :
      (fun n : ℕ =>
        (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n)
        =ᶠ[atTop]
      (fun n : ℕ => AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n) := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hnge => by
      have hn : 0 < n := by omega
      exact expected_cyclicPoints_eq_q hn⟩
  exact
    (AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent).congr_left
      hevent.symm

end

end AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS
