import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson

/-!
# Factorial moments for fixed-length cycles

This file records unconditional finite-average identities for the genuine
`rCycleCount` random variable from `RCyclesPoisson.lean`.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS

namespace FM

/-- A nontrivial cycle on `Fin n` with support of cardinality `r`. -/
abbrev CyclesOfLength (n r : ℕ) : Type :=
  {c : Equiv.Perm (Fin n) // c.IsCycle ∧ c.support.card = r}

/-- The `r`-cycle factors of a fixed permutation. -/
abbrev CyclesOfLengthOfPerm (n r : ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  {c : σ.cycleFactorsFinset // (c : Equiv.Perm (Fin n)).support.card = r}

/-- Permutations that contain a fixed cycle as one of their cycle factors. -/
abbrev PermContainingCycle {n r : ℕ} (c : CyclesOfLength n r) : Type :=
  {σ : Equiv.Perm (Fin n) // (c : Equiv.Perm (Fin n)) ∈ σ.cycleFactorsFinset}

/-- Permutations disjoint from a fixed cycle. -/
abbrev PermDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) : Type :=
  {τ : Equiv.Perm (Fin n) // Equiv.Perm.Disjoint τ (c : Equiv.Perm (Fin n))}

instance instFintypeCyclesOfLength (n r : ℕ) : Fintype (CyclesOfLength n r) := by
  classical
  unfold CyclesOfLength
  infer_instance

instance instFintypeCyclesOfLengthOfPerm (n r : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (CyclesOfLengthOfPerm n r σ) := by
  classical
  unfold CyclesOfLengthOfPerm
  infer_instance

instance instFintypePermContainingCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype (PermContainingCycle c) := by
  classical
  unfold PermContainingCycle
  infer_instance

instance instFintypePermDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype (PermDisjointCycle c) := by
  classical
  unfold PermDisjointCycle
  infer_instance

lemma cycleType_singleton_iff {n r : ℕ} {c : Equiv.Perm (Fin n)} :
    c.cycleType = ({r} : Multiset ℕ) ↔ c.IsCycle ∧ c.support.card = r := by
  constructor
  · intro h
    have hc : c.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [h]
      simp
    refine ⟨hc, ?_⟩
    have hsum := c.sum_cycleType
    rw [h] at hsum
    simpa using hsum.symm
  · rintro ⟨hc, hcard⟩
    rw [hc.cycleType, hcard]

lemma card_cyclesOfLength {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    Fintype.card (CyclesOfLength n r) = (r - 1).factorial * n.choose r := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin n) (n := r) hr (by simpa using hrn)
  have hsub :
      Fintype.card (CyclesOfLength n r) =
        ({g | g.cycleType = ({r} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card := by
    change
      Fintype.card {c : Equiv.Perm (Fin n) // c.IsCycle ∧ c.support.card = r} =
        ({g | g.cycleType = ({r} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_iff]
  rw [hsub, hcycles]
  simp

lemma card_cyclesOfLengthOfPerm {n r : ℕ} (σ : Equiv.Perm (Fin n)) :
    Fintype.card (CyclesOfLengthOfPerm n r σ) = σ.cycleType.count r := by
  classical
  rw [Equiv.Perm.CycleType.count_def (σ := σ) r]
  rfl

lemma rCycleCount_eq_card_cyclesOfLengthOfPerm {n r : ℕ} (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin n)) :
    rCycleCount n r σ = Fintype.card (CyclesOfLengthOfPerm n r σ) := by
  rw [card_cyclesOfLengthOfPerm]
  exact rCycleCount_eq_cycleType_count_of_ne_one (by omega : r ≠ 1) σ

/-- Removing a contained cycle leaves a permutation disjoint from that cycle. -/
def permContainingCycleEquivDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    PermContainingCycle c ≃ PermDisjointCycle c where
  toFun σ :=
    ⟨σ.1 * (c : Equiv.Perm (Fin n))⁻¹,
      Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset σ.2⟩
  invFun τ :=
    ⟨τ.1 * (c : Equiv.Perm (Fin n)), by
      have hc_mem :
          (c : Equiv.Perm (Fin n)) ∈
            (c : Equiv.Perm (Fin n)).cycleFactorsFinset := by
        rw [(c.prop.1).cycleFactorsFinset_eq_singleton]
        simp
      have hcycles :
          (τ.1 * (c : Equiv.Perm (Fin n))).cycleFactorsFinset =
            τ.1.cycleFactorsFinset ∪ (c : Equiv.Perm (Fin n)).cycleFactorsFinset :=
        τ.2.cycleFactorsFinset_mul_eq_union
      rw [hcycles]
      exact Finset.mem_union_right _ hc_mem⟩
  left_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv τ := by
    apply Subtype.ext
    simp [mul_assoc]

def permDisjointCycleEquivComplement {n r : ℕ} (c : CyclesOfLength n r) :
    Equiv.Perm {x : Fin n // x ∉ (c : Equiv.Perm (Fin n)).support} ≃
      PermDisjointCycle c :=
  (Equiv.Perm.subtypeEquivSubtypePerm
      (fun x : Fin n => x ∉ (c : Equiv.Perm (Fin n)).support)).trans
    { toFun := fun τ =>
        ⟨τ.1, by
          intro x
          by_cases hx : x ∈ (c : Equiv.Perm (Fin n)).support
          · exact Or.inl (τ.2 x (by simpa using hx))
          · exact Or.inr (Equiv.Perm.notMem_support.mp hx)⟩
      invFun := fun τ =>
        ⟨τ.1, by
          intro x hx
          rcases τ.2 x with hτ | hc
          · exact hτ
          · have hxmem : x ∈ (c : Equiv.Perm (Fin n)).support := by simpa using hx
            exact False.elim ((Equiv.Perm.mem_support.mp hxmem) hc)⟩
      left_inv := by
        rintro ⟨τ, hτ⟩
        rfl
      right_inv := by
        rintro ⟨τ, hτ⟩
        rfl }

lemma card_complement_cycle_support {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card {x : Fin n // x ∉ (c : Equiv.Perm (Fin n)).support} = n - r := by
  classical
  rw [Fintype.card_subtype_compl (fun x : Fin n => x ∈ (c : Equiv.Perm (Fin n)).support)]
  rw [Fintype.card_fin, Fintype.card_coe, c.prop.2]

lemma card_permDisjointCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card (PermDisjointCycle c) = (n - r).factorial := by
  classical
  rw [← Fintype.card_congr (permDisjointCycleEquivComplement c)]
  rw [Fintype.card_perm, card_complement_cycle_support c]

lemma card_permContainingCycle {n r : ℕ} (c : CyclesOfLength n r) :
    Fintype.card (PermContainingCycle c) = (n - r).factorial := by
  classical
  rw [Fintype.card_congr (permContainingCycleEquivDisjointCycle c)]
  exact card_permDisjointCycle c

/-- Count the same incidence relation first by ambient permutation. -/
abbrev CycleByPerm (n r : ℕ) : Type :=
  Σ σ : Equiv.Perm (Fin n), CyclesOfLengthOfPerm n r σ

/-- Count the same incidence relation first by the distinguished cycle. -/
abbrev CycleByCycle (n r : ℕ) : Type :=
  Σ c : CyclesOfLength n r, PermContainingCycle c

def cycleByPermEquivCycleByCycle (n r : ℕ) :
    CycleByPerm n r ≃ CycleByCycle n r where
  toFun x :=
    ⟨⟨x.2.1, (Equiv.Perm.mem_cycleFactorsFinset_iff.mp x.2.1.prop).1, x.2.2⟩,
      ⟨x.1, x.2.1.prop⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨⟨x.1.1, x.2.2⟩, x.1.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, c, hcard⟩
    rfl
  right_inv := by
    rintro ⟨c, σ, hmem⟩
    rfl

theorem rCycleCount_sum_eq {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ) =
      (r - 1).factorial * n.choose r * (n - r).factorial := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ)
        = ∑ σ : Equiv.Perm (Fin n),
            Fintype.card (CyclesOfLengthOfPerm n r σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _hσ
          exact rCycleCount_eq_card_cyclesOfLengthOfPerm hr σ
    _ = Fintype.card (CycleByPerm n r) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card (CycleByCycle n r) := by
          exact Fintype.card_congr (cycleByPermEquivCycleByCycle n r)
    _ = ∑ c : CyclesOfLength n r, Fintype.card (PermContainingCycle c) := by
          rw [Fintype.card_sigma]
    _ = ∑ _c : CyclesOfLength n r, (n - r).factorial := by
          refine Finset.sum_congr rfl ?_
          intro c _hc
          exact card_permContainingCycle c
    _ = Fintype.card (CyclesOfLength n r) * (n - r).factorial := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = (r - 1).factorial * n.choose r * (n - r).factorial := by
          rw [card_cyclesOfLength hr hrn]

lemma r_mul_rCycleCount_sum_eq_factorial {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    r * (∑ σ : Equiv.Perm (Fin n), rCycleCount n r σ) = n.factorial := by
  classical
  rw [rCycleCount_sum_eq hr hrn]
  have hr0 : r ≠ 0 := by omega
  have hfac : r.factorial = (r - 1).factorial * r := by
    rw [Nat.mul_comm, Nat.mul_factorial_pred hr0]
  calc
    r * ((r - 1).factorial * n.choose r * (n - r).factorial)
        = n.choose r * r.factorial * (n - r).factorial := by
          rw [hfac]
          ring
    _ = n.factorial := by
          exact Nat.choose_mul_factorial_mul_factorial hrn

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A nontrivial cycle of length `r` in an arbitrary finite type. -/
abbrev CyclesOfLengthIn (r : ℕ) : Type u :=
  {c : Equiv.Perm α // c.IsCycle ∧ c.support.card = r}

/-- The `r`-cycle factors of a fixed permutation of an arbitrary finite type. -/
abbrev CyclesOfLengthOfPermIn (r : ℕ) (σ : Equiv.Perm α) : Type u :=
  {c : σ.cycleFactorsFinset // (c : Equiv.Perm α).support.card = r}

/-- Permutations that contain a fixed cycle as one of their cycle factors. -/
abbrev PermContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) : Type u :=
  {σ : Equiv.Perm α // (c : Equiv.Perm α) ∈ σ.cycleFactorsFinset}

/-- Permutations disjoint from a fixed cycle. -/
abbrev PermDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) : Type u :=
  {τ : Equiv.Perm α // Equiv.Perm.Disjoint τ (c : Equiv.Perm α)}

instance instFintypeCyclesOfLengthIn (r : ℕ) :
    Fintype (CyclesOfLengthIn (α := α) r) := by
  classical
  unfold CyclesOfLengthIn
  infer_instance

instance instFintypeCyclesOfLengthOfPermIn (r : ℕ) (σ : Equiv.Perm α) :
    Fintype (CyclesOfLengthOfPermIn (α := α) r σ) := by
  classical
  unfold CyclesOfLengthOfPermIn
  infer_instance

instance instFintypePermContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype (PermContainingCycleIn c) := by
  classical
  unfold PermContainingCycleIn
  infer_instance

instance instFintypePermDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype (PermDisjointCycleIn c) := by
  classical
  unfold PermDisjointCycleIn
  infer_instance

lemma cycleType_singleton_iff_in {r : ℕ} {c : Equiv.Perm α} :
    c.cycleType = ({r} : Multiset ℕ) ↔ c.IsCycle ∧ c.support.card = r := by
  constructor
  · intro h
    have hc : c.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [h]
      simp
    refine ⟨hc, ?_⟩
    have hsum := c.sum_cycleType
    rw [h] at hsum
    simpa using hsum.symm
  · rintro ⟨hc, hcard⟩
    rw [hc.cycleType, hcard]

lemma card_cyclesOfLengthIn {r : ℕ} (hr : 2 ≤ r) (hrα : r ≤ Fintype.card α) :
    Fintype.card (CyclesOfLengthIn (α := α) r) =
      (r - 1).factorial * (Fintype.card α).choose r := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := α) (n := r) hr hrα
  have hsub :
      Fintype.card (CyclesOfLengthIn (α := α) r) =
        ({g | g.cycleType = ({r} : Multiset ℕ)} : Finset (Equiv.Perm α)).card := by
    change Fintype.card {c : Equiv.Perm α // c.IsCycle ∧ c.support.card = r} =
      ({g | g.cycleType = ({r} : Multiset ℕ)} : Finset (Equiv.Perm α)).card
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_iff_in]
  rw [hsub, hcycles]

lemma card_cyclesOfLengthOfPermIn {r : ℕ} (σ : Equiv.Perm α) :
    Fintype.card (CyclesOfLengthOfPermIn (α := α) r σ) = σ.cycleType.count r := by
  classical
  rw [Equiv.Perm.CycleType.count_def (σ := σ) r]
  rfl

def permContainingCycleEquivDisjointCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    PermContainingCycleIn c ≃ PermDisjointCycleIn c where
  toFun σ :=
    ⟨σ.1 * (c : Equiv.Perm α)⁻¹,
      Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset σ.2⟩
  invFun τ :=
    ⟨τ.1 * (c : Equiv.Perm α), by
      have hc_mem : (c : Equiv.Perm α) ∈ (c : Equiv.Perm α).cycleFactorsFinset := by
        rw [(c.prop.1).cycleFactorsFinset_eq_singleton]
        simp
      have hcycles :
          (τ.1 * (c : Equiv.Perm α)).cycleFactorsFinset =
            τ.1.cycleFactorsFinset ∪ (c : Equiv.Perm α).cycleFactorsFinset :=
        τ.2.cycleFactorsFinset_mul_eq_union
      rw [hcycles]
      exact Finset.mem_union_right _ hc_mem⟩
  left_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv τ := by
    apply Subtype.ext
    simp [mul_assoc]

def permDisjointCycleEquivComplementIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} ≃ PermDisjointCycleIn c :=
  (Equiv.Perm.subtypeEquivSubtypePerm
      (fun x : α => x ∉ (c : Equiv.Perm α).support)).trans
    { toFun := fun τ =>
        ⟨τ.1, by
          intro x
          by_cases hx : x ∈ (c : Equiv.Perm α).support
          · exact Or.inl (τ.2 x (by simpa using hx))
          · exact Or.inr (Equiv.Perm.notMem_support.mp hx)⟩
      invFun := fun τ =>
        ⟨τ.1, by
          intro x hx
          rcases τ.2 x with hτ | hc
          · exact hτ
          · have hxmem : x ∈ (c : Equiv.Perm α).support := by simpa using hx
            exact False.elim ((Equiv.Perm.mem_support.mp hxmem) hc)⟩
      left_inv := by
        rintro ⟨τ, hτ⟩
        rfl
      right_inv := by
        rintro ⟨τ, hτ⟩
        rfl }

def permComplementEquivContainingCycleIn {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} ≃ PermContainingCycleIn c :=
  (permDisjointCycleEquivComplementIn c).trans
    (permContainingCycleEquivDisjointCycleIn c).symm

lemma card_complement_cycle_support_in {r : ℕ} (c : CyclesOfLengthIn (α := α) r) :
    Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
      Fintype.card α - r := by
  classical
  rw [Fintype.card_subtype_compl (fun x : α => x ∈ (c : Equiv.Perm α).support)]
  rw [Fintype.card_coe, c.prop.2]

lemma cycleType_count_containing_from_complement {r k : ℕ}
    (c : CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    ((((permComplementEquivContainingCycleIn c) τ).1.cycleType.count r - 1).descFactorial k) =
      (τ.cycleType.count r).descFactorial k := by
  classical
  dsimp [permComplementEquivContainingCycleIn, permDisjointCycleEquivComplementIn,
    permContainingCycleEquivDisjointCycleIn]
  have hctype : (c : Equiv.Perm α).cycleType = ({r} : Multiset ℕ) :=
    cycleType_singleton_iff_in.mpr c.prop
  have hdisj :
      Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype τ) (c : Equiv.Perm α) := by
    intro x
    by_cases hx : x ∈ (c : Equiv.Perm α).support
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx))
    · exact Or.inr (Equiv.Perm.notMem_support.mp hx)
  have hcount :
      ((Equiv.Perm.ofSubtype τ * (c : Equiv.Perm α)).cycleType.count r - 1) =
        τ.cycleType.count r := by
    rw [hdisj.cycleType_mul, hctype, Equiv.Perm.cycleType_ofSubtype]
    simp
  rw [hcount]

lemma descFactorial_succ_eq_mul_pred (m k : ℕ) :
    m.descFactorial (k + 1) = m * (m - 1).descFactorial k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.descFactorial_succ, ih, Nat.descFactorial_succ]
      have hsub : m - (k + 1) = m - 1 - k := by omega
      rw [hsub]
      ring

abbrev CycleByPermIn (r : ℕ) : Type u :=
  Σ σ : Equiv.Perm α, CyclesOfLengthOfPermIn (α := α) r σ

abbrev CycleByCycleIn (r : ℕ) : Type u :=
  Σ c : CyclesOfLengthIn (α := α) r, PermContainingCycleIn c

def cycleByPermEquivCycleByCycleIn (r : ℕ) :
    CycleByPermIn (α := α) r ≃ CycleByCycleIn (α := α) r where
  toFun x :=
    ⟨⟨x.2.1, (Equiv.Perm.mem_cycleFactorsFinset_iff.mp x.2.1.prop).1, x.2.2⟩,
      ⟨x.1, x.2.1.prop⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨⟨x.1.1, x.2.2⟩, x.1.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, c, hcard⟩
    rfl
  right_inv := by
    rintro ⟨c, σ, hmem⟩
    rfl

theorem cycleType_count_factorialMoment_sum_in {r k : ℕ}
    (hr : 2 ≤ r) (h : r * k ≤ Fintype.card α) :
    r ^ k * (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial k) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction k with
  | zero =>
      intro α _ _
      simp [Fintype.card_perm]
  | succ k ih =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (k + 1) := Nat.mul_le_mul_left r (Nat.succ_pos k)
          _ ≤ Fintype.card α := h
      have hrec_card :
          r * k ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * k + r = r * (k + 1) := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial (k + 1)) =
            ∑ c : CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k := by
        calc
          (∑ σ : Equiv.Perm α, (σ.cycleType.count r).descFactorial (k + 1))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (CyclesOfLengthOfPermIn (α := α) r σ) *
                    ((σ.cycleType.count r - 1).descFactorial k) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [descFactorial_succ_eq_mul_pred]
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : CyclesOfLengthOfPermIn (α := α) r σ,
                    ((σ.cycleType.count r - 1).descFactorial k) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : CycleByPermIn (α := α) r,
                  ((x.1.cycleType.count r - 1).descFactorial k) := by
                exact (Fintype.sum_sigma'
                  (fun σ (c : CyclesOfLengthOfPermIn (α := α) r σ) =>
                    ((σ.cycleType.count r - 1).descFactorial k))).symm
          _ = ∑ x : CycleByCycleIn (α := α) r,
                  ((x.2.1.cycleType.count r - 1).descFactorial k) := by
                exact Fintype.sum_equiv (cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : CycleByPermIn (α := α) r =>
                    ((x.1.cycleType.count r - 1).descFactorial k))
                  (fun x : CycleByCycleIn (α := α) r =>
                    ((x.2.1.cycleType.count r - 1).descFactorial k))
                  (by intro x; rfl)
          _ = ∑ c : CyclesOfLengthIn (α := α) r,
                  ∑ σ : PermContainingCycleIn c,
                    ((σ.1.cycleType.count r - 1).descFactorial k) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial k := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial k)
                  (fun σ : PermContainingCycleIn c =>
                    ((σ.1.cycleType.count r - 1).descFactorial k))
                  (by
                    intro τ
                    exact (cycleType_count_containing_from_complement (k := k) c τ).symm)).symm
      have hinner :
          ∀ c : CyclesOfLengthIn (α := α) r,
            r ^ k *
              (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          card_complement_cycle_support_in c
        have hrec :
            r ^ k *
              (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          ih (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (k + 1) *
            (∑ c : CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial k)
            = r * (∑ c : CyclesOfLengthIn (α := α) r,
                r ^ k *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial k)) := by
              rw [pow_succ, ← Finset.mul_sum]
              ring
        _ = r * (∑ _c : CyclesOfLengthIn (α := α) r, (Fintype.card α - r).factorial) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro c _hc
              exact hinner c
        _ = r * (Fintype.card (CyclesOfLengthIn (α := α) r) * (Fintype.card α - r).factorial) := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              rw [card_cyclesOfLengthIn (α := α) hr hrα]
              have hr0 : r ≠ 0 := by omega
              have hfac : r.factorial = (r - 1).factorial * r := by
                rw [Nat.mul_comm, Nat.mul_factorial_pred hr0]
              calc
                r * (((r - 1).factorial * (Fintype.card α).choose r) *
                    (Fintype.card α - r).factorial)
                    = (Fintype.card α).choose r * r.factorial *
                        (Fintype.card α - r).factorial := by
                      rw [hfac]
                      ring
                _ = (Fintype.card α).factorial := by
                      exact Nat.choose_mul_factorial_mul_factorial hrα

end GeneralFinite

end FM

theorem rCycle_mean_eq_inv {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => (rCycleCount n r σ : ℝ)) =
        (r : ℝ) ^ (-1 : ℤ) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · simpa [rCycleCount, FixedPointsPoissonNS.uniformPermExpectation] using
      FixedPointsPoissonNS.fixedPoint_factorialMoment_eq_one (n := n) (k := 1) hrn
  · have hr2 : 2 ≤ r := by omega
    unfold FixedPointsPoissonNS.uniformPermExpectation
    have hsumNat := FM.r_mul_rCycleCount_sum_eq_factorial (n := n) (r := r) hr2 hrn
    have hsumReal :
        (r : ℝ) *
          (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ : ℝ)) =
            (n.factorial : ℝ) := by
      exact_mod_cast hsumNat
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ : ℝ)) / (n.factorial : ℝ)
          = ((n.factorial : ℝ) / (r : ℝ)) / (n.factorial : ℝ) := by
            rw [← hsumReal]
            field_simp [hrR]
      _ = (r : ℝ)⁻¹ := by
            field_simp [hrR, hnfacR]
      _ = (r : ℝ) ^ (-1 : ℤ) := by
            simp

/-- Exact factorial moment identity for the number of `r`-cycles in a uniform
permutation, stated as the finite average over `Equiv.Perm (Fin n)`.

This is the unconditional Goncharov factorial-moment identity
`E[(C_{n,r})_k] = r^{-k}` whenever `r * k ≤ n`. -/
theorem factorialMoment_rCycle {n r k : ℕ} (hr : 0 < r) (h : r * k ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => ((rCycleCount n r σ).descFactorial k : ℝ)) =
        (r : ℝ) ^ (-(k : ℤ)) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hkn : k ≤ n := by simpa using h
    simpa [rCycleCount, FixedPointsPoissonNS.uniformPermExpectation] using
      FixedPointsPoissonNS.fixedPoint_factorialMoment_eq_one (n := n) (k := k) hkn
  · have hr2 : 2 ≤ r := by omega
    unfold FixedPointsPoissonNS.uniformPermExpectation
    have hsum_eq :
        (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ).descFactorial k) =
          ∑ σ : Equiv.Perm (Fin n), (σ.cycleType.count r).descFactorial k := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    have hsumNat :
        r ^ k * (∑ σ : Equiv.Perm (Fin n), (rCycleCount n r σ).descFactorial k) =
          n.factorial := by
      rw [hsum_eq]
      simpa [Fintype.card_fin] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := Fin n) (r := r) (k := k) hr2 (by simpa [Fintype.card_fin] using h)
    have hsumReal :
        (r : ℝ) ^ k *
            (∑ σ : Equiv.Perm (Fin n), ((rCycleCount n r σ).descFactorial k : ℝ)) =
          (n.factorial : ℝ) := by
      exact_mod_cast hsumNat
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    have hpowR : (r : ℝ) ^ k ≠ 0 := pow_ne_zero k hrR
    have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      (∑ σ : Equiv.Perm (Fin n), ((rCycleCount n r σ).descFactorial k : ℝ)) /
          (n.factorial : ℝ)
          = ((n.factorial : ℝ) / (r : ℝ) ^ k) / (n.factorial : ℝ) := by
            rw [← hsumReal]
            field_simp [hpowR]
      _ = ((r : ℝ) ^ k)⁻¹ := by
            field_simp [hpowR, hnfacR]
      _ = (r : ℝ) ^ (-(k : ℤ)) := by
            simp [zpow_neg, zpow_natCast]

theorem factorialMoment_rCycle_one {n r : ℕ} (hr : 0 < r) (h : r * 1 ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) => ((rCycleCount n r σ).descFactorial 1 : ℝ)) =
        (r : ℝ) ^ (-(1 : ℤ)) := by
  simpa using factorialMoment_rCycle (n := n) (r := r) (k := 1) hr h

end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
