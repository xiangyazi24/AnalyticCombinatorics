import Mathlib
import AnalyticCombinatorics.Ch2.Mappings.ForestCount
import AnalyticCombinatorics.Ch2.Mappings.ForestCountComplete
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQ
import AnalyticCombinatorics.Ch2.Mappings.RamanujanQSharp

/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here; see `HANDOFF/outbox/mapconn-reply.md`.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-- Weak connectivity of a functional graph, stated directly in terms of iterates. -/
def MappingConnected {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ x y : Fin n, ∃ i j : ℕ, f^[i] x = f^[j] y

/-- A point is periodic for `f` if a positive iterate returns to it. -/
def PeriodicPoint {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ m : ℕ, 0 < m ∧ f^[m] x = x

/-- The periodic core of a self-map on a finite decidable type. -/
def periodicPointsFinset {α : Type*} [DecidableEq α] [Fintype α] (f : α → α) :
    Finset α := by
  classical
  exact Finset.univ.filter (fun x => PeriodicPoint f x)

@[simp] lemma mem_periodicPointsFinset {α : Type*} [DecidableEq α] [Fintype α]
    {f : α → α} {x : α} :
    x ∈ periodicPointsFinset f ↔ PeriodicPoint f x := by
  simp [periodicPointsFinset]

lemma periodicPoint_of_iterate_eq {α : Type*} {f : α → α} {x : α} {i j : ℕ}
    (hij : i < j) (hij_eq : f^[i] x = f^[j] x) :
    PeriodicPoint f (f^[i] x) := by
  refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
  have hji : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hij)
  calc
    f^[j - i] (f^[i] x) = f^[j - i + i] x := by
      rw [Function.iterate_add_apply]
    _ = f^[j] x := by rw [hji]
    _ = f^[i] x := hij_eq.symm

lemma exists_periodicPoint_on_orbit {α : Type*} [Fintype α] (f : α → α) (x : α) :
    ∃ i : ℕ, PeriodicPoint f (f^[i] x) := by
  classical
  let t : Fin (Fintype.card α + 1) → α := fun i => f^[i.1] x
  have hcard : Fintype.card α < Fintype.card (Fin (Fintype.card α + 1)) := by
    simp
  obtain ⟨a, b, hab_ne, hab_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt t hcard
  have hval_ne : a.1 ≠ b.1 := by
    intro h
    exact hab_ne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval_ne with hab_lt | hba_lt
  · exact ⟨a.1, periodicPoint_of_iterate_eq hab_lt hab_eq⟩
  · exact ⟨b.1, periodicPoint_of_iterate_eq hba_lt hab_eq.symm⟩

lemma periodicPointsFinset_nonempty {α : Type*} [DecidableEq α] [Fintype α]
    [Nonempty α] (f : α → α) :
    (periodicPointsFinset f).Nonempty := by
  classical
  obtain ⟨x⟩ := ‹Nonempty α›
  rcases exists_periodicPoint_on_orbit f x with ⟨i, hi⟩
  exact ⟨f^[i] x, by simpa using hi⟩

lemma periodicPointsFinset_nonempty_fin {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n) :
    (periodicPointsFinset f).Nonempty := by
  classical
  have hnonempty : Nonempty (Fin n) := by
    exact Fintype.card_pos_iff.mp (by simpa [Fintype.card_fin] using hn)
  exact periodicPointsFinset_nonempty f

lemma PeriodicPoint.map {α : Type*} {f : α → α} {x : α}
    (hx : PeriodicPoint f x) :
    PeriodicPoint f (f x) := by
  rcases hx with ⟨m, hmpos, hm⟩
  refine ⟨m, hmpos, ?_⟩
  calc
    f^[m] (f x) = f^[m + 1] x := by
      rw [Function.iterate_succ_apply]
    _ = f (f^[m] x) := by
      rw [Function.iterate_succ_apply']
    _ = f x := by rw [hm]

lemma PeriodicPoint.iterate {α : Type*} {f : α → α} {x : α}
    (hx : PeriodicPoint f x) :
    ∀ m : ℕ, PeriodicPoint f (f^[m] x)
  | 0 => by simpa using hx
  | m + 1 => by
      simpa [Function.iterate_succ_apply'] using (hx.iterate m).map

lemma PeriodicPoint.period_mul {α : Type*} {f : α → α} {x : α}
    {m : ℕ} (_hmpos : 0 < m) (hm : f^[m] x = x) (t : ℕ) :
    f^[m * t] x = x := by
  rw [Function.iterate_mul]
  exact Function.iterate_fixed hm t

lemma PeriodicPoint.exists_preimage {α : Type*} {f : α → α} {y : α}
    (hy : PeriodicPoint f y) :
    ∃ x : α, PeriodicPoint f x ∧ f x = y := by
  rcases hy with ⟨m, hmpos, hm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  refine ⟨f^[d] y, PeriodicPoint.iterate (⟨d + 1, Nat.succ_pos d, hm⟩ :
    PeriodicPoint f y) d, ?_⟩
  simpa [Function.iterate_succ_apply'] using hm

/-- The self-map induced by `f` on its periodic core. -/
def periodicCoreStep {α : Type*} {f : α → α} :
    {x : α // PeriodicPoint f x} → {x : α // PeriodicPoint f x} :=
  fun x => ⟨f x.1, x.2.map⟩

lemma periodicCoreStep_surjective {α : Type*} {f : α → α} :
    Function.Surjective (periodicCoreStep (f := f)) := by
  intro y
  rcases y.2.exists_preimage with ⟨x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, by ext; exact hxy⟩

lemma periodicCoreStep_bijective {α : Type*} {f : α → α}
    [Finite {x : α // PeriodicPoint f x}] :
    Function.Bijective (periodicCoreStep (f := f)) := by
  exact ⟨(Finite.injective_iff_surjective).mpr periodicCoreStep_surjective,
    periodicCoreStep_surjective⟩

/-- The restriction of a finite self-map to its periodic core is a permutation. -/
def periodicCorePerm {α : Type*} (f : α → α)
    [Finite {x : α // PeriodicPoint f x}] :
    Equiv.Perm {x : α // PeriodicPoint f x} :=
  Equiv.ofBijective (periodicCoreStep (f := f)) periodicCoreStep_bijective

@[simp] lemma periodicCorePerm_apply {α : Type*} (f : α → α)
    [Finite {x : α // PeriodicPoint f x}] (x : {x : α // PeriodicPoint f x}) :
    (periodicCorePerm f x : α) = f x.1 := by
  rfl

lemma periodicCoreStep_iterate_val {α : Type*} {f : α → α}
    (a : ℕ) (x : {x : α // PeriodicPoint f x}) :
    ((periodicCoreStep (f := f))^[a] x : α) = f^[a] x.1 := by
  induction a generalizing x with
  | zero => rfl
  | succ a ih =>
      simp [Function.iterate_succ_apply', periodicCoreStep, ih]

lemma periodicPoint_of_connected {n : ℕ} {f : Fin n → Fin n}
    (hconn : MappingConnected f) {x y : Fin n}
    (_hx : PeriodicPoint f x) (hy : PeriodicPoint f y) :
    ∃ a : ℕ, f^[a] x = y := by
  rcases hconn x y with ⟨i, j, hij⟩
  rcases hy with ⟨p, hppos, hp⟩
  let t : ℕ := p * j - j
  refine ⟨i + t, ?_⟩
  have hj_le : j ≤ p * j := by
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hppos
    calc
      j = 1 * j := by rw [one_mul]
      _ ≤ p * j := Nat.mul_le_mul_right j hp1
  have ht_add : t + j = p * j := Nat.sub_add_cancel hj_le
  have hper : f^[p * j] y = y :=
    PeriodicPoint.period_mul hppos hp j
  calc
    f^[i + t] x = f^[t + i] x := by rw [Nat.add_comm]
    _ = f^[t] (f^[i] x) := by
      rw [Function.iterate_add_apply]
    _ = f^[t] (f^[j] y) := by rw [hij]
    _ = f^[t + j] y := by
      rw [Function.iterate_add_apply]
    _ = f^[p * j] y := by rw [ht_add]
    _ = y := hper

lemma periodicCore_single_orbit_of_connected {n : ℕ} {f : Fin n → Fin n}
    (hconn : MappingConnected f)
    (x y : {x : Fin n // PeriodicPoint f x}) :
    ∃ a : ℕ, (periodicCoreStep (f := f))^[a] x = y := by
  rcases periodicPoint_of_connected hconn x.2 y.2 with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa [periodicCoreStep_iterate_val] using ha

lemma reaches_periodicPoints_step_of_iterate {n : ℕ} (f : Fin n → Fin n) :
    ∀ m : ℕ, ∀ x : Fin n,
      PeriodicPoint f (f^[m] x) →
        ForestCountNS.Reaches (periodicPointsFinset f)
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) x
  | 0, x, hx => by
      exact ForestCountNS.reaches_of_mem
        (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1)
        (by simpa using hx)
  | m + 1, x, hx => by
      by_cases hxP : x ∈ periodicPointsFinset f
      · exact ForestCountNS.reaches_of_mem
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) hxP
      · have hnext : PeriodicPoint f (f^[m] (f x)) := by
          simpa [Function.iterate_succ_apply] using hx
        rcases reaches_periodicPoints_step_of_iterate f m (f x) hnext with ⟨r, hr⟩
        refine ⟨r + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        rw [ForestCountNS.step_of_notMem
          (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) hxP]
        exact hr

lemma reaches_periodicPoints_step {n : ℕ} (f : Fin n → Fin n) (x : Fin n) :
    ForestCountNS.Reaches (periodicPointsFinset f)
      (fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1) x := by
  rcases exists_periodicPoint_on_orbit f x with ⟨m, hm⟩
  exact reaches_periodicPoints_step_of_iterate f m x hm

lemma reaches_step_of_iterate_mem {n : ℕ} (P : Finset (Fin n)) (f : Fin n → Fin n) :
    ∀ m : ℕ, ∀ x : Fin n,
      f^[m] x ∈ P →
        ForestCountNS.Reaches P
          (fun y : ForestCountNS.NonRoot P => f y.1) x
  | 0, x, hx => by
      exact ForestCountNS.reaches_of_mem
        (fun y : ForestCountNS.NonRoot P => f y.1) hx
  | m + 1, x, hx => by
      by_cases hxP : x ∈ P
      · exact ForestCountNS.reaches_of_mem
          (fun y : ForestCountNS.NonRoot P => f y.1) hxP
      · have hnext : f^[m] (f x) ∈ P := by
          simpa [Function.iterate_succ_apply] using hx
        rcases reaches_step_of_iterate_mem P f m (f x) hnext with ⟨r, hr⟩
        refine ⟨r + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        rw [ForestCountNS.step_of_notMem
          (fun y : ForestCountNS.NonRoot P => f y.1) hxP]
        exact hr

/-- Every finite mapping determines a rooted forest into its periodic core. -/
def forestToPeriodicCore {n : ℕ} (f : Fin n → Fin n) :
    ForestCountNS.RootedForests (periodicPointsFinset f) :=
  ⟨(fun y : ForestCountNS.NonRoot (periodicPointsFinset f) => f y.1),
    reaches_periodicPoints_step f⟩

/-- Reconstruct a mapping from a permutation on the prescribed core and a forest rooted there. -/
def mapOfCoreForest {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P)
    (F : ForestCountNS.RootedForests P) : Fin n → Fin n :=
  fun x =>
    if hx : x ∈ P then
      (σ ⟨x, hx⟩ : Fin n)
    else
      F.1 ⟨x, hx⟩

@[simp] lemma mapOfCoreForest_of_mem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    mapOfCoreForest P σ F x = (σ ⟨x, hx⟩ : Fin n) := by
  simp [mapOfCoreForest, hx]

@[simp] lemma mapOfCoreForest_of_notMem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    mapOfCoreForest P σ F x = F.1 ⟨x, hx⟩ := by
  simp [mapOfCoreForest, hx]

lemma mapOfCoreForest_maps_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    mapOfCoreForest P σ F x ∈ P := by
  rw [mapOfCoreForest_of_mem σ F hx]
  exact (σ ⟨x, hx⟩).2

lemma mapOfCoreForest_iterate_mem_of_mem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    ∀ m : ℕ, (mapOfCoreForest P σ F)^[m] x ∈ P
  | 0 => by simpa using hx
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      exact mapOfCoreForest_maps_core σ F
        (mapOfCoreForest_iterate_mem_of_mem σ F hx m)

lemma mapOfCoreForest_iterate_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : P) :
    ∀ m : ℕ, (mapOfCoreForest P σ F)^[m] x.1 = (σ^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [mapOfCoreForest_iterate_core σ F x m]
      rw [mapOfCoreForest_of_mem σ F (σ^[m] x).2]
      rw [Function.iterate_succ_apply']

lemma periodicPoint_of_mem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∈ P) :
    PeriodicPoint (mapOfCoreForest P σ F) x := by
  classical
  let xP : P := ⟨x, hx⟩
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  calc
    (mapOfCoreForest P σ F)^[orderOf σ] x =
        (σ^[orderOf σ] xP : Fin n) := by
          simpa [xP] using mapOfCoreForest_iterate_core σ F xP (orderOf σ)
    _ = x := by
      have hpow : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
      have hfun : σ^[orderOf σ] xP = xP := by
        rw [← Equiv.Perm.coe_pow, hpow]
        rfl
      change ((σ^[orderOf σ] xP : P) : Fin n) = (xP : Fin n)
      exact congrArg Subtype.val hfun

lemma mapOfCoreForest_eq_step_of_notMem {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    mapOfCoreForest P σ F x = ForestCountNS.step P F.1 x := by
  rw [mapOfCoreForest_of_notMem σ F hx]
  rw [ForestCountNS.step_of_notMem F.1 hx]

lemma mapOfCoreForest_iterate_eq_step_before_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : Fin n) :
    ∀ m : ℕ,
      (∀ i < m, (ForestCountNS.step P F.1)^[i] x ∉ P) →
        (mapOfCoreForest P σ F)^[m] x = (ForestCountNS.step P F.1)^[m] x
  | 0, _ => rfl
  | m + 1, hbefore => by
      have hbefore_m :
          ∀ i < m, (ForestCountNS.step P F.1)^[i] x ∉ P := by
        intro i hi
        exact hbefore i (Nat.lt_trans hi (Nat.lt_succ_self m))
      have ih := mapOfCoreForest_iterate_eq_step_before_core σ F x m hbefore_m
      have hstep_not : (ForestCountNS.step P F.1)^[m] x ∉ P :=
        hbefore m (Nat.lt_succ_self m)
      calc
        (mapOfCoreForest P σ F)^[m + 1] x =
            mapOfCoreForest P σ F ((mapOfCoreForest P σ F)^[m] x) := by
              rw [Function.iterate_succ_apply']
        _ = mapOfCoreForest P σ F ((ForestCountNS.step P F.1)^[m] x) := by
              rw [ih]
        _ = ForestCountNS.step P F.1 ((ForestCountNS.step P F.1)^[m] x) := by
              exact mapOfCoreForest_eq_step_of_notMem σ F hstep_not
        _ = (ForestCountNS.step P F.1)^[m + 1] x := by
              rw [Function.iterate_succ_apply']

lemma mapOfCoreForest_eventually_mem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    (x : Fin n) :
    ∃ m : ℕ, (mapOfCoreForest P σ F)^[m] x ∈ P := by
  classical
  rcases F.2 x with ⟨m, hm⟩
  let p : ℕ → Prop := fun r => (ForestCountNS.step P F.1)^[r] x ∈ P
  have hp : ∃ r, p r := ⟨m, hm⟩
  let r := Nat.find hp
  have hbefore : ∀ i < r, (ForestCountNS.step P F.1)^[i] x ∉ P := by
    intro i hi
    exact Nat.find_min hp hi
  have hiter :
      (mapOfCoreForest P σ F)^[r] x = (ForestCountNS.step P F.1)^[r] x :=
    mapOfCoreForest_iterate_eq_step_before_core σ F x r hbefore
  refine ⟨r, ?_⟩
  simpa [hiter, p, r] using Nat.find_spec hp

lemma mapOfCoreForest_iterate_mem_of_mem_le {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} {r s : ℕ} (hr : (mapOfCoreForest P σ F)^[r] x ∈ P)
    (hrs : r ≤ s) :
    (mapOfCoreForest P σ F)^[s] x ∈ P := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  rw [Nat.add_comm]
  rw [Function.iterate_add_apply]
  exact mapOfCoreForest_iterate_mem_of_mem σ F hr d

lemma not_periodicPoint_of_notMem_core {n : ℕ} {P : Finset (Fin n)}
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P)
    {x : Fin n} (hx : x ∉ P) :
    ¬ PeriodicPoint (mapOfCoreForest P σ F) x := by
  intro hper
  rcases hper with ⟨m, hmpos, hm⟩
  rcases mapOfCoreForest_eventually_mem_core σ F x with ⟨r, hr⟩
  by_cases hr0 : r = 0
  · exact hx (by simpa [hr0] using hr)
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    have hle : r ≤ m * r := by
      have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
      calc
        r = 1 * r := by rw [one_mul]
        _ ≤ m * r := Nat.mul_le_mul_right r hm1
    have hmem_late :
        (mapOfCoreForest P σ F)^[m * r] x ∈ P :=
      mapOfCoreForest_iterate_mem_of_mem_le σ F hr hle
    have hfixed :
        (mapOfCoreForest P σ F)^[m * r] x = x :=
      PeriodicPoint.period_mul hmpos hm r
    exact hx (by simpa [hfixed] using hmem_late)

theorem periodicPoints_mapOfCoreForest {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P) :
    periodicPointsFinset (mapOfCoreForest P σ F) = P := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hxP
    exact not_periodicPoint_of_notMem_core σ F hxP (by simpa using hx)
  · intro hx
    exact (mem_periodicPointsFinset).mpr (periodicPoint_of_mem_core σ F hx)

/-- Mappings whose periodic core is exactly `P` and whose restriction to `P` is `σ`. -/
abbrev MapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) : Type :=
  {f : Fin n → Fin n //
    periodicPointsFinset f = P ∧
      ∀ x : P, f x.1 = (σ x : Fin n)}

def forestOfFixedCoreMap {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) :
    ForestCountNS.RootedForests P :=
  ⟨(fun y : ForestCountNS.NonRoot P => M.1 y.1), by
    intro x
    rcases exists_periodicPoint_on_orbit M.1 x with ⟨m, hm⟩
    have hmem : M.1^[m] x ∈ P := by
      have hmemCore : M.1^[m] x ∈ periodicPointsFinset M.1 := by
        simpa using hm
      have hprop :
          (M.1^[m] x ∈ periodicPointsFinset M.1) = (M.1^[m] x ∈ P) :=
        congrArg (fun S : Finset (Fin n) => M.1^[m] x ∈ S) M.2.1
      exact Eq.mp hprop hmemCore
    exact reaches_step_of_iterate_mem P M.1 m x hmem⟩

def fixedCoreMapOfForest {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P)
    (F : ForestCountNS.RootedForests P) :
    MapsWithFixedCore P σ :=
  ⟨mapOfCoreForest P σ F, periodicPoints_mapOfCoreForest P σ F, by
    intro x
    exact mapOfCoreForest_of_mem σ F x.2⟩

/-- Fixed-core mappings are equivalent to rooted forests with the same root set. -/
def fixedCoreForestEquiv {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    MapsWithFixedCore P σ ≃ ForestCountNS.RootedForests P where
  toFun := forestOfFixedCoreMap
  invFun := fixedCoreMapOfForest P σ
  left_inv M := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ P
    · have hrestr := M.2.2 ⟨x, hx⟩
      simp [fixedCoreMapOfForest, mapOfCoreForest_of_mem σ (forestOfFixedCoreMap M) hx, hrestr]
    · change mapOfCoreForest P σ (forestOfFixedCoreMap M) x = M.1 x
      rw [mapOfCoreForest_of_notMem σ (forestOfFixedCoreMap M) hx]
      rfl
  right_inv F := by
    apply Subtype.ext
    funext x
    change mapOfCoreForest P σ F x.1 = F.1 x
    rw [mapOfCoreForest_of_notMem σ F x.2]

theorem card_mapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Fintype.card (MapsWithFixedCore P σ) =
      @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  exact @Fintype.card_congr (MapsWithFixedCore P σ) (ForestCountNS.RootedForests P)
    inferInstance (ForestCountNS.rootedForestsFintype P) (fixedCoreForestEquiv P σ)

/-- A permutation is a single directed cycle, with the singleton case included. -/
def PermSingleCycle {α : Type*} (σ : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃ m : ℕ, σ^[m] x = y

instance instFintypePermSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype {σ : Equiv.Perm α // PermSingleCycle σ} := by
  classical
  infer_instance

lemma permSingleCycle_iff_isCycle_support_full_of_two_le {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    PermSingleCycle σ ↔ σ.IsCycle ∧ σ.support.card = Fintype.card α := by
  constructor
  · intro hσ
    have hmove : ∀ x : α, σ x ≠ x := by
      intro x hxfix
      rcases Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) x with ⟨y, hy⟩
      rcases hσ x y with ⟨m, hm⟩
      have hfixed : σ^[m] x = x := Function.iterate_fixed hxfix m
      exact hy (hm.symm.trans hfixed)
    have hsupp : σ.support = Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support, hmove x]
    refine ⟨?_, by rw [hsupp, Finset.card_univ]⟩
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    refine ⟨x, hmove x, ?_⟩
    intro y _hy
    rcases hσ x y with ⟨m, hm⟩
    refine ⟨(m : ℤ), ?_⟩
    have hpow : (σ ^ m) x = y := by
      change (⇑(σ ^ m)) x = y
      rw [Equiv.Perm.coe_pow]
      exact hm
    simpa [zpow_natCast] using hpow
  · rintro ⟨hcycle, hsupp_card⟩ x y
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hsupp_card
    have hx : σ x ≠ x := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    have hy : σ y ≠ y := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    rcases (hcycle.sameCycle hx hy).exists_nat_pow_eq with ⟨m, hm⟩
    have hiter : σ^[m] x = y := by
      change (⇑σ)^[m] x = y
      rw [← Equiv.Perm.coe_pow]
      exact hm
    exact ⟨m, hiter⟩

lemma cycleType_singleton_full_iff_permSingleCycle {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    σ.cycleType = ({Fintype.card α} : Multiset ℕ) ↔ PermSingleCycle σ := by
  constructor
  · intro htype
    have hcycle : σ.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [htype]
      simp
    have hsupp : σ.support.card = Fintype.card α := by
      have hsum := Equiv.Perm.sum_cycleType σ
      rw [htype] at hsum
      simpa using hsum.symm
    exact (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mpr
      ⟨hcycle, hsupp⟩
  · intro hsingle
    rcases (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mp hsingle with
      ⟨hcycle, hsupp⟩
    rw [hcycle.cycleType, hsupp]

theorem card_permSingleCycle_of_two_le {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  have hsub :
      Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
        ({g | g.cycleType = ({Fintype.card α} : Multiset ℕ)} :
          Finset (Equiv.Perm α)).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_full_iff_permSingleCycle (σ := g) hα]
  rw [hsub]
  rw [Equiv.Perm.card_of_cycleType_singleton hα (le_rfl : Fintype.card α ≤ Fintype.card α)]
  simp

theorem card_permSingleCycle_of_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    (hα : Fintype.card α ≤ 1) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} = 1 := by
  classical
  have hsub : ∀ x y : α, x = y := Fintype.card_le_one_iff.mp hα
  refine Fintype.card_eq_one_iff.mpr ⟨⟨1, ?_⟩, ?_⟩
  · intro x y
    exact ⟨0, hsub x y⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro x
    exact hsub _ _

theorem card_permSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  by_cases hα : 2 ≤ Fintype.card α
  · exact card_permSingleCycle_of_two_le hα
  · have hle : Fintype.card α ≤ 1 := by omega
    have hsmall : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
    rw [card_permSingleCycle_of_card_le_one hle]
    rcases hsmall with h0 | h1
    · simp [h0]
    · simp [h1]

lemma fixedCoreMap_iterate_core {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) (x : P) :
    ∀ m : ℕ, M.1^[m] x.1 = (σ^[m] x : Fin n)
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply']
      rw [fixedCoreMap_iterate_core M x m]
      have hrestr := M.2.2 (σ^[m] x)
      rw [hrestr]
      rw [Function.iterate_succ_apply']

lemma fixedCoreMap_eventually_mem_core {n : ℕ} {P : Finset (Fin n)} {σ : Equiv.Perm P}
    (M : MapsWithFixedCore P σ) (x : Fin n) :
    ∃ m : ℕ, M.1^[m] x ∈ P := by
  rcases exists_periodicPoint_on_orbit M.1 x with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hmemCore : M.1^[m] x ∈ periodicPointsFinset M.1 := by
    simpa using hm
  have hprop :
      (M.1^[m] x ∈ periodicPointsFinset M.1) = (M.1^[m] x ∈ P) :=
    congrArg (fun S : Finset (Fin n) => M.1^[m] x ∈ S) M.2.1
  exact Eq.mp hprop hmemCore

theorem fixedCoreMap_connected_iff_singleCycle {n : ℕ} {P : Finset (Fin n)}
    {σ : Equiv.Perm P} (M : MapsWithFixedCore P σ) :
    MappingConnected M.1 ↔ PermSingleCycle σ := by
  constructor
  · intro hconn x y
    have hxper : PeriodicPoint M.1 x.1 := by
      have hmem : x.1 ∈ periodicPointsFinset M.1 := by
        have hprop :
            (x.1 ∈ P) = (x.1 ∈ periodicPointsFinset M.1) :=
          congrArg (fun S : Finset (Fin n) => x.1 ∈ S) M.2.1.symm
        exact Eq.mp hprop x.2
      simpa using hmem
    have hyper : PeriodicPoint M.1 y.1 := by
      have hmem : y.1 ∈ periodicPointsFinset M.1 := by
        have hprop :
            (y.1 ∈ P) = (y.1 ∈ periodicPointsFinset M.1) :=
          congrArg (fun S : Finset (Fin n) => y.1 ∈ S) M.2.1.symm
        exact Eq.mp hprop y.2
      simpa using hmem
    rcases periodicPoint_of_connected hconn hxper hyper with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have hcore := fixedCoreMap_iterate_core M x a
    simpa [hcore] using ha
  · intro hsingle x y
    rcases fixedCoreMap_eventually_mem_core M x with ⟨i, hi⟩
    rcases fixedCoreMap_eventually_mem_core M y with ⟨j, hj⟩
    let xP : P := ⟨M.1^[i] x, hi⟩
    let yP : P := ⟨M.1^[j] y, hj⟩
    rcases hsingle xP yP with ⟨a, ha⟩
    refine ⟨i + a, j, ?_⟩
    calc
      M.1^[i + a] x = M.1^[a + i] x := by rw [Nat.add_comm]
      _ = M.1^[a] (M.1^[i] x) := by
            rw [Function.iterate_add_apply]
      _ = (σ^[a] xP : Fin n) := by
            exact fixedCoreMap_iterate_core M xP a
      _ = M.1^[j] y := by
            simpa [xP, yP] using congrArg Subtype.val ha

theorem mapOfCoreForest_connected_iff_singleCycle {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (F : ForestCountNS.RootedForests P) :
    MappingConnected (mapOfCoreForest P σ F) ↔ PermSingleCycle σ := by
  exact fixedCoreMap_connected_iff_singleCycle (fixedCoreMapOfForest P σ F)

abbrev ConnectedMapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Type :=
  {M : MapsWithFixedCore P σ // MappingConnected M.1}

@[reducible] def connectedMapsWithFixedCoreFintype {n : ℕ}
    (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Fintype (ConnectedMapsWithFixedCore P σ) := by
  classical
  exact Subtype.fintype (fun M : MapsWithFixedCore P σ => MappingConnected M.1)

def connectedMapsWithFixedCoreEquivOfSingle {n : ℕ} {P : Finset (Fin n)}
    {σ : Equiv.Perm P} (hσ : PermSingleCycle σ) :
    ConnectedMapsWithFixedCore P σ ≃ MapsWithFixedCore P σ where
  toFun M := M.1
  invFun M := ⟨M, (fixedCoreMap_connected_iff_singleCycle M).mpr hσ⟩
  left_inv M := by
    apply Subtype.ext
    rfl
  right_inv M := rfl

theorem card_connectedMapsWithFixedCore_of_single {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (hσ : PermSingleCycle σ) :
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) =
      @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  calc
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) =
        Fintype.card (MapsWithFixedCore P σ) := by
          exact @Fintype.card_congr (ConnectedMapsWithFixedCore P σ) (MapsWithFixedCore P σ)
            (connectedMapsWithFixedCoreFintype P σ) inferInstance
            (connectedMapsWithFixedCoreEquivOfSingle hσ)
    _ = @Fintype.card (ForestCountNS.RootedForests P)
          (ForestCountNS.rootedForestsFintype P) :=
          card_mapsWithFixedCore P σ

theorem card_connectedMapsWithFixedCore_of_not_single {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (hσ : ¬ PermSingleCycle σ) :
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) = 0 := by
  classical
  have hempty : IsEmpty (ConnectedMapsWithFixedCore P σ) := by
    refine ⟨fun M => ?_⟩
    exact hσ ((fixedCoreMap_connected_iff_singleCycle M.1).mp M.2)
  exact @Fintype.card_eq_zero (ConnectedMapsWithFixedCore P σ)
    (connectedMapsWithFixedCoreFintype P σ) hempty

abbrev ConnectedMap (n : ℕ) : Type :=
  {f : Fin n → Fin n // MappingConnected f}

@[reducible] def connectedMapFintype (n : ℕ) : Fintype (ConnectedMap n) := by
  classical
  exact Subtype.fintype (fun f : Fin n → Fin n => MappingConnected f)

def connectedCore {n : ℕ} (hn : 0 < n) (M : ConnectedMap n) :
    {P : Finset (Fin n) // P.Nonempty} :=
  ⟨periodicPointsFinset M.1, periodicPointsFinset_nonempty_fin hn M.1⟩

def periodicSubtypeEquivCore {n : ℕ} (P : Finset (Fin n)) {f : Fin n → Fin n}
    (hP : periodicPointsFinset f = P) :
    {x : Fin n // PeriodicPoint f x} ≃ P where
  toFun x := by
    refine ⟨x.1, ?_⟩
    have hx : x.1 ∈ periodicPointsFinset f := by
      simpa using (mem_periodicPointsFinset (f := f) (x := x.1)).mpr x.2
    simpa [hP] using hx
  invFun x := by
    refine ⟨x.1, ?_⟩
    have hx : x.1 ∈ periodicPointsFinset f := by
      simp [hP, x.2]
    simpa using (mem_periodicPointsFinset (f := f) (x := x.1)).mp hx
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def corePermOfCoreEq {n : ℕ} (P : Finset (Fin n)) {f : Fin n → Fin n}
    (hP : periodicPointsFinset f = P) : Equiv.Perm P := by
  classical
  let e := periodicSubtypeEquivCore P hP
  exact (e.symm.trans (periodicCorePerm f)).trans e

@[simp] lemma corePermOfCoreEq_apply_val {n : ℕ} (P : Finset (Fin n))
    {f : Fin n → Fin n} (hP : periodicPointsFinset f = P) (x : P) :
    (corePermOfCoreEq P (f := f) hP x : Fin n) = f x.1 := by
  classical
  simp [corePermOfCoreEq, periodicSubtypeEquivCore]

def connectedCoreFiberPerm {n : ℕ} {hn : 0 < n}
    (P : {P : Finset (Fin n) // P.Nonempty})
    (M : {M : ConnectedMap n // connectedCore hn M = P}) :
    Equiv.Perm P.1 :=
  corePermOfCoreEq P.1 (f := M.1.1) (congrArg Subtype.val M.2)

def connectedCorePermFiberEquiv {n : ℕ} {hn : 0 < n}
    (P : {P : Finset (Fin n) // P.Nonempty}) (σ : Equiv.Perm P.1) :
    {M : {M : ConnectedMap n // connectedCore hn M = P} //
        connectedCoreFiberPerm P M = σ} ≃
      ConnectedMapsWithFixedCore P.1 σ where
  toFun M := by
    let hcore : periodicPointsFinset M.1.1.1 = P.1 := congrArg Subtype.val M.1.2
    refine ⟨⟨M.1.1.1, hcore, ?_⟩, M.1.1.2⟩
    intro x
    have hperm :=
      congrArg (fun τ : Equiv.Perm P.1 => (τ x : Fin n)) M.2
    change
      (corePermOfCoreEq P.1 (f := M.1.1.1) hcore x : Fin n) = (σ x : Fin n)
        at hperm
    exact (corePermOfCoreEq_apply_val P.1 (f := M.1.1.1) hcore x).symm.trans hperm
  invFun M := by
    let hfiber : connectedCore hn ⟨M.1.1, M.2⟩ = P := by
      apply Subtype.ext
      exact M.1.2.1
    refine ⟨⟨⟨M.1.1, M.2⟩, hfiber⟩, ?_⟩
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change
      (corePermOfCoreEq P.1 (f := M.1.1) (congrArg Subtype.val hfiber) x : Fin n) =
        (σ x : Fin n)
    exact (corePermOfCoreEq_apply_val P.1 (f := M.1.1)
      (congrArg Subtype.val hfiber) x).trans (M.1.2.2 x)
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem card_connectedMappings_fiber_sum {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ P : {P : Finset (Fin n) // P.Nonempty},
        ∑ σ : Equiv.Perm P.1,
          @Fintype.card (ConnectedMapsWithFixedCore P.1 σ)
            (connectedMapsWithFixedCoreFintype P.1 σ) := by
  classical
  calc
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          @Fintype.card {M : ConnectedMap n // connectedCore hn M = P}
            (Subtype.fintype (fun M : ConnectedMap n => connectedCore hn M = P)) := by
          exact @ForestCountNS.Complete.card_eq_sum_fintype_fiber
            (ConnectedMap n) {P : Finset (Fin n) // P.Nonempty}
            (connectedMapFintype n) inferInstance inferInstance (connectedCore hn)
    _ =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          ∑ σ : Equiv.Perm P.1,
            @Fintype.card
              {M : {M : ConnectedMap n // connectedCore hn M = P} //
                connectedCoreFiberPerm P M = σ}
              (Subtype.fintype
                (fun M : {M : ConnectedMap n // connectedCore hn M = P} =>
                  connectedCoreFiberPerm P M = σ)) := by
          refine Finset.sum_congr rfl ?_
          intro P _
          exact @ForestCountNS.Complete.card_eq_sum_fintype_fiber
            {M : ConnectedMap n // connectedCore hn M = P} (Equiv.Perm P.1)
            (Subtype.fintype (fun M : ConnectedMap n => connectedCore hn M = P))
            inferInstance inferInstance (connectedCoreFiberPerm P)
    _ =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          ∑ σ : Equiv.Perm P.1,
            @Fintype.card (ConnectedMapsWithFixedCore P.1 σ)
              (connectedMapsWithFixedCoreFintype P.1 σ) := by
          refine Finset.sum_congr rfl ?_
          intro P _
          refine Finset.sum_congr rfl ?_
          intro σ _
          exact @Fintype.card_congr
            {M : {M : ConnectedMap n // connectedCore hn M = P} //
              connectedCoreFiberPerm P M = σ}
            (ConnectedMapsWithFixedCore P.1 σ) inferInstance
            (connectedMapsWithFixedCoreFintype P.1 σ)
            (connectedCorePermFiberEquiv P σ)

theorem sum_connectedMapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) :
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
      Fintype.card {σ : Equiv.Perm P // PermSingleCycle σ} *
        @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  let forestCard : ℕ :=
    @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P)
  calc
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
        ∑ σ : Equiv.Perm P, if PermSingleCycle σ then forestCard else 0 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          by_cases hσ : PermSingleCycle σ
          · simp [forestCard, hσ, card_connectedMapsWithFixedCore_of_single P σ hσ]
          · simp [forestCard, hσ, card_connectedMapsWithFixedCore_of_not_single P σ hσ]
    _ =
      Fintype.card {σ : Equiv.Perm P // PermSingleCycle σ} * forestCard := by
        rw [← Finset.sum_filter]
        simp [Fintype.card_subtype]

theorem connected_fixedCore_total_by_card {n : ℕ} (P : Finset (Fin n))
    (hPpos : 0 < P.card) :
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
      (P.card - 1).factorial *
        (if P.card = n then 1 else P.card * n ^ (n - P.card - 1)) := by
  classical
  rw [sum_connectedMapsWithFixedCore P]
  rw [card_permSingleCycle]
  simp only [Fintype.card_coe]
  by_cases hcard : P.card = n
  · rw [if_pos hcard]
    rw [ForestCountNS.card_rootedForests_all_roots_of_card P hcard]
  · rw [if_neg hcard]
    have hle : P.card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ P
    have hlt : P.card < n := by omega
    rw [ForestCountNS.Complete.card_rootedForests P rfl hPpos hlt]

theorem card_connectedMappings_by_card_sum {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ P : {P : Finset (Fin n) // P.Nonempty},
        (P.1.card - 1).factorial *
          (if P.1.card = n then 1 else P.1.card * n ^ (n - P.1.card - 1)) := by
  classical
  rw [card_connectedMappings_fiber_sum hn]
  refine Finset.sum_congr rfl ?_
  intro P _
  exact connected_fixedCore_total_by_card P.1 P.2.card_pos

theorem card_connectedMappings_range {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ i ∈ Finset.range n,
        Nat.choose n (i + 1) *
          ((i + 1 - 1).factorial *
            (if i + 1 = n then 1 else (i + 1) * n ^ (n - (i + 1) - 1))) := by
  classical
  rw [card_connectedMappings_by_card_sum hn]
  have hsum :=
    ForestCountNS.Complete.sum_nonempty_finsets_by_card
      (β := Fin n)
      (f := fun k : ℕ =>
        (k - 1).factorial * (if k = n then 1 else k * n ^ (n - k - 1)))
  simpa [Fintype.card_fin] using hsum

lemma connected_range_term_eq_desc {n i : ℕ} (hi : i ∈ Finset.range n) :
    Nat.choose n (i + 1) *
        ((i + 1 - 1).factorial *
          (if i + 1 = n then 1 else (i + 1) * n ^ (n - (i + 1) - 1))) =
      (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
  have hin : i < n := Finset.mem_range.mp hi
  by_cases hlast : i + 1 = n
  · subst n
    simp [Nat.descFactorial_self]
  · have hlt : i + 1 < n := by omega
    have hnpos : 0 < n := by omega
    have hsucc :
        n.descFactorial (i + 1) = n * (n - 1).descFactorial i := by
      have h := Nat.succ_descFactorial_succ (n - 1) i
      have hnsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      simpa [hnsucc] using h
    have hexp : n - (i + 1) = (n - (i + 1) - 1) + 1 := by omega
    rw [if_neg hlast]
    calc
      Nat.choose n (i + 1) *
          ((i + 1 - 1).factorial * ((i + 1) * n ^ (n - (i + 1) - 1))) =
          ((i + 1).factorial * Nat.choose n (i + 1)) *
            n ^ (n - (i + 1) - 1) := by
            have hsub : i + 1 - 1 = i := by omega
            rw [hsub, Nat.factorial_succ]
            ring
      _ = n.descFactorial (i + 1) * n ^ (n - (i + 1) - 1) := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ = (n * (n - 1).descFactorial i) * n ^ (n - (i + 1) - 1) := by
            rw [hsucc]
      _ = (n - 1).descFactorial i * n ^ ((n - (i + 1) - 1) + 1) := by
            rw [Nat.pow_succ]
            ring
      _ = (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
            rw [← hexp]

theorem card_connectedMappings {n : ℕ} (hn : 0 < n) :
    Fintype.card {f : Fin n → Fin n // MappingConnected f}
      = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  calc
    @Fintype.card (ConnectedMap n) CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card (ConnectedMap n) (connectedMapFintype n) := by
          exact @Fintype.card_congr (ConnectedMap n) (ConnectedMap n)
            CategoryTheory.FinCategory.fintypeObj (connectedMapFintype n)
            (Equiv.refl (ConnectedMap n))
    _ =
        ∑ i ∈ Finset.range n, (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
          rw [card_connectedMappings_range hn]
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact connected_range_term_eq_desc hi
    _ = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k))
              1 (n + 1)).symm

lemma ramanujanQTerm_eq_descFactorial_div {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    RamanujanQNS.ramanujanQTerm n k =
      ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
  classical
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  let qFactor : ℕ → ℝ :=
    fun j : ℕ => (1 : ℝ) - (((j + 1 : ℕ) : ℝ) / (n : ℝ))
  let dFactor : ℕ → ℝ :=
    fun j : ℕ => ((n - 1 - j : ℕ) : ℝ) / (n : ℝ)
  have hfactor (j : ℕ) (hj : j ∈ Finset.range k) :
      qFactor j = dFactor j := by
    have hjk : j < k := Finset.mem_range.mp hj
    have hle : j + 1 ≤ n := by omega
    have hsub : n - (j + 1) = n - 1 - j := by omega
    dsimp [qFactor, dFactor]
    rw [← hsub]
    rw [Nat.cast_sub hle]
    field_simp [hnne]
  unfold RamanujanQNS.ramanujanQTerm
  change (∏ j ∈ Finset.range k, qFactor j) =
    ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k
  calc
    (∏ j ∈ Finset.range k, qFactor j) =
        ∏ j ∈ Finset.range k, dFactor j := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact hfactor j hj
    _ =
        ∏ j ∈ Finset.range k, (((n - 1 - j : ℕ) : ℝ) / (n : ℝ)) := by
          rfl
    _ =
        (∏ j ∈ Finset.range k, ((n - 1 - j : ℕ) : ℝ)) /
          ∏ _j ∈ Finset.range k, (n : ℝ) := by
          rw [Finset.prod_div_distrib]
    _ =
        ((∏ j ∈ Finset.range k, (n - 1 - j : ℕ)) : ℝ) / (n : ℝ) ^ k := by
          rw [Finset.prod_const]
          simp only [Finset.card_range]
    _ = ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
          rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]

lemma ramanujanQTerm_scaled_eq_desc {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    (n : ℝ) ^ (n - 1) * RamanujanQNS.ramanujanQTerm n k =
      ((n - 1).descFactorial k * n ^ (n - (k + 1)) : ℕ) := by
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hpow_ne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero k hnne
  have hsplit : n - 1 = k + (n - 1 - k) := by omega
  have hexp : n - 1 - k = n - (k + 1) := by omega
  have hpow_split :
      (n : ℝ) ^ (n - 1) = (n : ℝ) ^ k * (n : ℝ) ^ (n - 1 - k) := by
    rw [hsplit, pow_add]
    have htail : k + (n - 1 - k) - k = n - 1 - k := by omega
    rw [htail]
  rw [ramanujanQTerm_eq_descFactorial_div hn hk]
  calc
    (n : ℝ) ^ (n - 1) *
        (((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k) =
        ((n : ℝ) ^ k * (n : ℝ) ^ (n - 1 - k)) *
          (((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k) := by
          rw [hpow_split]
    _ = ((n - 1).descFactorial k : ℝ) * (n : ℝ) ^ (n - 1 - k) := by
          field_simp [hpow_ne]
    _ = ((n - 1).descFactorial k * n ^ (n - (k + 1)) : ℕ) := by
          rw [hexp]
          simp

theorem card_connectedMappings_eq_q {n : ℕ} (hn : 0 < n) :
    (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) =
      (n : ℝ) ^ (n - 1) * RamanujanQNS.ramanujanQ n := by
  classical
  rw [card_connectedMappings hn]
  have hreindex :
      (∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k)) =
        ∑ i ∈ Finset.range n, (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
    simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      (Finset.sum_Ico_eq_sum_range
        (f := fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k))
        1 (n + 1))
  rw [hreindex]
  rw [Nat.cast_sum]
  rw [RamanujanQNS.ramanujanQ, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact (ramanujanQTerm_scaled_eq_desc hn (Finset.mem_range.mp hk)).symm

lemma sqrt_pi_mul_nat_div_two_div_eq {n : ℕ} (hn : 0 < n) :
    Real.sqrt (Real.pi * (n : ℝ) / 2) / (n : ℝ) =
      Real.sqrt (Real.pi / (2 * (n : ℝ))) := by
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hx : 0 ≤ Real.pi * (n : ℝ) / 2 := by positivity
  calc
    Real.sqrt (Real.pi * (n : ℝ) / 2) / (n : ℝ) =
        Real.sqrt (Real.pi * (n : ℝ) / 2) / Real.sqrt ((n : ℝ) ^ 2) := by
          rw [Real.sqrt_sq hnnonneg]
    _ = Real.sqrt ((Real.pi * (n : ℝ) / 2) / ((n : ℝ) ^ 2)) := by
          rw [Real.sqrt_div hx]
    _ = Real.sqrt (Real.pi / (2 * (n : ℝ))) := by
          congr 1
          field_simp [hnne]

theorem connectedProbability_isEquivalent :
    (fun n : ℕ => (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) / n ^ n)
      ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi / (2 * n))) := by
  classical
  let prob : ℕ → ℝ :=
    fun n : ℕ =>
      (@Fintype.card (ConnectedMap n) CategoryTheory.FinCategory.fintypeObj : ℝ) / n ^ n
  let qdiv : ℕ → ℝ := fun n : ℕ => RamanujanQNS.ramanujanQ n / (n : ℝ)
  let sqrtDiv : ℕ → ℝ :=
    fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2) / (n : ℝ)
  have hprob : prob =ᶠ[atTop] qdiv := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hnge => by
      have hn : 0 < n := by omega
      dsimp [prob, qdiv]
      rw [card_connectedMappings_eq_q hn]
      have hnne : (n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn
      have hpowne : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hnne
      have hpow : (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
        have hsplit : n = (n - 1) + 1 := by omega
        calc
          (n : ℝ) ^ n = (n : ℝ) ^ ((n - 1) + 1) := by
            exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
          _ = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
            rw [pow_add, pow_one]
      rw [hpow]
      field_simp [hnne, hpowne]
      ⟩
  have hQdiv : qdiv ~[atTop] sqrtDiv := by
    have hid : (fun n : ℕ => (n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
      IsEquivalent.refl
    simpa [qdiv, sqrtDiv] using
      (RamanujanQNS.Sharp.ramanujanQ_isEquivalent.div hid)
  have hsqrt :
      sqrtDiv =ᶠ[atTop] (fun n : ℕ => Real.sqrt (Real.pi / (2 * n))) := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hnge => by
      have hn : 0 < n := by omega
      dsimp [sqrtDiv]
      exact sqrt_pi_mul_nat_div_two_div_eq hn⟩
  change prob ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi / (2 * n)))
  exact (hQdiv.congr_left hprob.symm).congr_right hsqrt

end

end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
