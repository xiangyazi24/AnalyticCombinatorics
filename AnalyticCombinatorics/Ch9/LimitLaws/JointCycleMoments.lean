import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment

/-!
# Joint factorial moments for cycle counts

This file starts the mixed factorial-moment theory for cycle counts of
distinct lengths.  The banked result is the exact two-length identity for
nontrivial lengths.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace JointCycleMomentsNS

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_containing_from_complement_ne {r s : ℕ} (hsr : s ≠ r)
    (c : FM.CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    ((FM.permComplementEquivContainingCycleIn c τ).1.cycleType.count s) =
      τ.cycleType.count s := by
  classical
  dsimp [FM.permComplementEquivContainingCycleIn, FM.permDisjointCycleEquivComplementIn,
    FM.permContainingCycleEquivDisjointCycleIn]
  have hctype : (c : Equiv.Perm α).cycleType = ({r} : Multiset ℕ) :=
    FM.cycleType_singleton_iff_in.mpr c.prop
  have hdisj :
      Equiv.Perm.Disjoint (Equiv.Perm.ofSubtype τ) (c : Equiv.Perm α) := by
    intro x
    by_cases hx : x ∈ (c : Equiv.Perm α).support
    · exact Or.inl (Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx))
    · exact Or.inr (Equiv.Perm.notMem_support.mp hx)
  rw [hdisj.cycleType_mul, hctype, Equiv.Perm.cycleType_ofSubtype]
  simp [hsr]

/-- Exact mixed factorial-moment counting identity for two distinct nontrivial
cycle lengths on an arbitrary finite type. -/
theorem cycleType_count_two_factorialMoment_sum_in {r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ Fintype.card α) :
    r ^ a * s ^ b *
        (∑ σ : Equiv.Perm α,
          (σ.cycleType.count r).descFactorial a *
            (σ.cycleType.count s).descFactorial b) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hsb : s * b ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := α) (r := s) (k := b) hs hsb
  | succ a ih =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (a + 1) := Nat.mul_le_mul_left r (Nat.succ_pos a)
          _ ≤ Fintype.card α := by omega
      have hrec_card : r * a + s * b ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * a + s * b + r = r * (a + 1) + s * b := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b) =
            ∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  (τ.cycleType.count s).descFactorial b := by
        calc
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b)
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FM.CyclesOfLengthOfPermIn (α := α) r σ) *
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [FM.card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : FM.CyclesOfLengthOfPermIn (α := α) r σ,
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : FM.CycleByPermIn (α := α) r,
                  ((x.1.cycleType.count r - 1).descFactorial a *
                    (x.1.cycleType.count s).descFactorial b) := by
                exact (Fintype.sum_sigma'
                  (fun σ (c : FM.CyclesOfLengthOfPermIn (α := α) r σ) =>
                    ((σ.cycleType.count r - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b))).symm
          _ = ∑ x : FM.CycleByCycleIn (α := α) r,
                  ((x.2.1.cycleType.count r - 1).descFactorial a *
                    (x.2.1.cycleType.count s).descFactorial b) := by
                exact Fintype.sum_equiv (FM.cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : FM.CycleByPermIn (α := α) r =>
                    ((x.1.cycleType.count r - 1).descFactorial a *
                      (x.1.cycleType.count s).descFactorial b))
                  (fun x : FM.CycleByCycleIn (α := α) r =>
                    ((x.2.1.cycleType.count r - 1).descFactorial a *
                      (x.2.1.cycleType.count s).descFactorial b))
                  (by intro x; rfl)
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ σ : FM.PermContainingCycleIn c,
                    ((σ.1.cycleType.count r - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (FM.permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)
                  (fun σ : FM.PermContainingCycleIn c =>
                    ((σ.1.cycleType.count r - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b))
                  (by
                    intro τ
                    change
                      (τ.cycleType.count r).descFactorial a *
                          (τ.cycleType.count s).descFactorial b =
                        ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count r -
                            1).descFactorial a *
                          (((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count s).descFactorial b)
                    rw [← FM.cycleType_count_containing_from_complement (k := a) c τ]
                    rw [← cycleType_count_containing_from_complement_ne (α := α)
                      (s := s) (r := r) (Ne.symm hrs) c τ])).symm
      have hinner :
          ∀ c : FM.CyclesOfLengthIn (α := α) r,
            r ^ a * s ^ b *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          FM.card_complement_cycle_support_in c
        have hrec :
            r ^ a * s ^ b *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          ih (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (a + 1) * s ^ b *
            (∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  (τ.cycleType.count s).descFactorial b)
            = r * (∑ c : FM.CyclesOfLengthIn (α := α) r,
                r ^ a * s ^ b *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)) := by
              rw [pow_succ, ← Finset.mul_sum]
              ring
        _ = r * (∑ _c : FM.CyclesOfLengthIn (α := α) r,
              (Fintype.card α - r).factorial) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro c _hc
              exact hinner c
        _ = r * (Fintype.card (FM.CyclesOfLengthIn (α := α) r) *
              (Fintype.card α - r).factorial) := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              rw [FM.card_cyclesOfLengthIn (α := α) hr hrα]
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

/-- Fixed points of a permutation on an arbitrary finite type. -/
abbrev FixedPointsOfPermIn (σ : Equiv.Perm α) : Type u :=
  Function.fixedPoints σ

/-- Fixed-point count on an arbitrary finite type. -/
def fixedPointCountIn (σ : Equiv.Perm α) : ℕ :=
  Fintype.card (FixedPointsOfPermIn (α := α) σ)

/-- Permutations fixing a distinguished point. -/
abbrev PermFixingPointIn (x : α) : Type u :=
  {σ : Equiv.Perm α // σ x = x}

instance instFintypePermFixingPointIn (x : α) : Fintype (PermFixingPointIn (α := α) x) := by
  classical
  unfold PermFixingPointIn
  infer_instance

/-- Count the same fixed-point incidence relation first by permutations. -/
abbrev FixedPointByPermIn : Type u :=
  Σ σ : Equiv.Perm α, FixedPointsOfPermIn (α := α) σ

/-- Count the same fixed-point incidence relation first by the distinguished
fixed point. -/
abbrev FixedPointByPointIn : Type u :=
  Σ x : α, PermFixingPointIn (α := α) x

def fixedPointByPermEquivByPointIn :
    FixedPointByPermIn (α := α) ≃ FixedPointByPointIn (α := α) where
  toFun x :=
    ⟨x.2.1, ⟨x.1, Function.mem_fixedPoints_iff.mp x.2.2⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨x.1, Function.mem_fixedPoints_iff.mpr x.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, x, hx⟩
    rfl
  right_inv := by
    rintro ⟨x, σ, hx⟩
    rfl

def permComplementEquivFixingPointIn (x : α) :
    Equiv.Perm {y : α // y ≠ x} ≃ PermFixingPointIn (α := α) x :=
  (Equiv.Perm.subtypeEquivSubtypePerm (fun y : α => y ≠ x)).trans
    { toFun := fun σ => ⟨σ.1, σ.2 x (by simp)⟩
      invFun := fun σ =>
        ⟨σ.1, by
          intro y hy
          have hyx : y = x := not_not.mp hy
          rw [hyx]
          exact σ.2⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        rfl
      right_inv := by
        rintro ⟨σ, hσ⟩
        rfl }

lemma card_complement_point (x : α) :
    Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 := by
  rw [Fintype.card_subtype_compl (fun y : α => y = x)]
  rw [Fintype.card_subtype_eq]

lemma cycleType_count_fixingPoint_from_complement {s : ℕ} (x : α)
    (τ : Equiv.Perm {y : α // y ≠ x}) :
    ((permComplementEquivFixingPointIn x τ).1.cycleType.count s) =
      τ.cycleType.count s := by
  dsimp [permComplementEquivFixingPointIn]
  rw [Equiv.Perm.cycleType_ofSubtype]

lemma fixedPointCount_fixingPoint_from_complement_desc {a : ℕ} (x : α)
    (τ : Equiv.Perm {y : α // y ≠ x}) :
    ((fixedPointCountIn ((permComplementEquivFixingPointIn x τ).1) - 1).descFactorial a) =
      (fixedPointCountIn τ).descFactorial a := by
  dsimp [fixedPointCountIn, FixedPointsOfPermIn, permComplementEquivFixingPointIn]
  rw [Equiv.Perm.card_fixedPoints]
  rw [Equiv.Perm.card_fixedPoints]
  rw [Equiv.Perm.cycleType_ofSubtype]
  rw [card_complement_point (α := α) x]
  congr 1
  omega

/-- Exact mixed factorial-moment counting identity for fixed points and one
nontrivial cycle length on an arbitrary finite type. -/
theorem fixedPoint_cycleType_count_factorialMoment_sum_in {s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ Fintype.card α) :
    s ^ b *
        (∑ σ : Equiv.Perm α,
          (fixedPointCountIn σ).descFactorial a *
            (σ.cycleType.count s).descFactorial b) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hsb : s * b ≤ Fintype.card α := by simpa using h
      simpa [fixedPointCountIn, mul_assoc] using
        FM.cycleType_count_factorialMoment_sum_in
          (α := α) (r := s) (k := b) hs hsb
  | succ a ih =>
      intro α _ _ h
      have hcard0 : Fintype.card α ≠ 0 := by omega
      have hrec_card : a + s * b ≤ Fintype.card α - 1 := by
        apply Nat.le_sub_of_add_le
        calc
          a + s * b + 1 = a + 1 + s * b := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (fixedPointCountIn σ).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b) =
            ∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (fixedPointCountIn τ).descFactorial a *
                  (τ.cycleType.count s).descFactorial b := by
        calc
          (∑ σ : Equiv.Perm α,
            (fixedPointCountIn σ).descFactorial (a + 1) *
              (σ.cycleType.count s).descFactorial b)
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FixedPointsOfPermIn (α := α) σ) *
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [fixedPointCountIn]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _x : FixedPointsOfPermIn (α := α) σ,
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ z : FixedPointByPermIn (α := α),
                  ((fixedPointCountIn z.1 - 1).descFactorial a *
                    (z.1.cycleType.count s).descFactorial b) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_x : FixedPointsOfPermIn (α := α) σ) =>
                    ((fixedPointCountIn σ - 1).descFactorial a *
                      (σ.cycleType.count s).descFactorial b))).symm
          _ = ∑ z : FixedPointByPointIn (α := α),
                  ((fixedPointCountIn z.2.1 - 1).descFactorial a *
                    (z.2.1.cycleType.count s).descFactorial b) := by
                exact Fintype.sum_equiv (fixedPointByPermEquivByPointIn (α := α))
                  (fun z : FixedPointByPermIn (α := α) =>
                    ((fixedPointCountIn z.1 - 1).descFactorial a *
                      (z.1.cycleType.count s).descFactorial b))
                  (fun z : FixedPointByPointIn (α := α) =>
                    ((fixedPointCountIn z.2.1 - 1).descFactorial a *
                      (z.2.1.cycleType.count s).descFactorial b))
                  (by intro z; rfl)
          _ = ∑ x : α,
                  ∑ σ : PermFixingPointIn (α := α) x,
                    ((fixedPointCountIn σ.1 - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b) := by
                rw [Fintype.sum_sigma]
          _ = ∑ x : α,
                  ∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                exact (Fintype.sum_equiv (permComplementEquivFixingPointIn x)
                  (fun τ : Equiv.Perm {y : α // y ≠ x} =>
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b)
                  (fun σ : PermFixingPointIn (α := α) x =>
                    ((fixedPointCountIn σ.1 - 1).descFactorial a *
                      (σ.1.cycleType.count s).descFactorial b))
                  (by
                    intro τ
                    change
                      (fixedPointCountIn τ).descFactorial a *
                          (τ.cycleType.count s).descFactorial b =
                        ((fixedPointCountIn ((permComplementEquivFixingPointIn x) τ).1 -
                            1).descFactorial a *
                          (((permComplementEquivFixingPointIn x) τ).1.cycleType.count s).descFactorial b)
                    rw [← fixedPointCount_fixingPoint_from_complement_desc (α := α) x τ]
                    rw [← cycleType_count_fixingPoint_from_complement (α := α)
                      (s := s) x τ])).symm
      have hinner :
          ∀ x : α,
            s ^ b *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (fixedPointCountIn τ).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card α - 1).factorial := by
        intro x
        have hc_card :
            Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 :=
          card_complement_point x
        have hrec :
            s ^ b *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (fixedPointCountIn τ).descFactorial a *
                    (τ.cycleType.count s).descFactorial b) =
              (Fintype.card {y : α // y ≠ x}).factorial :=
          ih (α := {y : α // y ≠ x}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        s ^ b *
            (∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (fixedPointCountIn τ).descFactorial a *
                  (τ.cycleType.count s).descFactorial b)
            = ∑ x : α,
                s ^ b *
                  (∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (fixedPointCountIn τ).descFactorial a *
                      (τ.cycleType.count s).descFactorial b) := by
              rw [Finset.mul_sum]
        _ = ∑ _x : α, (Fintype.card α - 1).factorial := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hinner x
        _ = Fintype.card α * (Fintype.card α - 1).factorial := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              exact Nat.mul_factorial_pred hcard0

end GeneralFinite

/-- Exact mixed factorial-moment counting identity for two distinct nontrivial
cycle lengths in permutations of `Fin n`, stated using the genuine
`rCycleCount` variables. -/
theorem rCycleCount_two_factorialMoment_sum {n r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    r ^ a * s ^ b *
        (∑ σ : Equiv.Perm (Fin n),
          (rCycleCount n r σ).descFactorial a *
            (rCycleCount n s σ).descFactorial b) =
      n.factorial := by
  classical
  have hrne : r ≠ 1 := by omega
  have hsne : s ≠ 1 := by omega
  have hsum_eq :
      (∑ σ : Equiv.Perm (Fin n),
        (rCycleCount n r σ).descFactorial a *
          (rCycleCount n s σ).descFactorial b) =
        ∑ σ : Equiv.Perm (Fin n),
          (σ.cycleType.count r).descFactorial a *
            (σ.cycleType.count s).descFactorial b := by
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
  rw [hsum_eq]
  simpa [Fintype.card_fin] using
    cycleType_count_two_factorialMoment_sum_in
      (α := Fin n) (r := r) (s := s) (a := a) (b := b)
      hr hs hrs (by simpa [Fintype.card_fin] using h)

lemma fixedPointCountIn_fin (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    fixedPointCountIn σ = FixedPointsPoissonNS.fixedPointCount n σ := by
  classical
  unfold fixedPointCountIn FixedPointsOfPermIn FixedPointsPoissonNS.fixedPointCount
  exact Fintype.card_congr
    { toFun := fun x => ⟨x.1, Function.mem_fixedPoints_iff.mp x.2⟩
      invFun := fun x => ⟨x.1, Function.mem_fixedPoints_iff.mpr x.2⟩
      left_inv := by
        rintro ⟨x, hx⟩
        rfl
      right_inv := by
        rintro ⟨x, hx⟩
        rfl }

/-- Exact mixed factorial-moment counting identity for fixed points and one
nontrivial cycle length, stated using `rCycleCount n 1` and `rCycleCount n s`. -/
theorem rCycleCount_one_two_factorialMoment_sum {n s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ n) :
    s ^ b *
        (∑ σ : Equiv.Perm (Fin n),
          (rCycleCount n 1 σ).descFactorial a *
            (rCycleCount n s σ).descFactorial b) =
      n.factorial := by
  classical
  have hsne : s ≠ 1 := by omega
  have hsum_eq :
      (∑ σ : Equiv.Perm (Fin n),
        (rCycleCount n 1 σ).descFactorial a *
          (rCycleCount n s σ).descFactorial b) =
        ∑ σ : Equiv.Perm (Fin n),
          (fixedPointCountIn σ).descFactorial a *
            (σ.cycleType.count s).descFactorial b := by
    refine Finset.sum_congr rfl ?_
    intro σ _hσ
    rw [rCycleCount_one]
    rw [rCycleCount_eq_cycleType_count_of_ne_one hsne σ]
    rw [fixedPointCountIn_fin n σ]
  rw [hsum_eq]
  simpa [Fintype.card_fin] using
    fixedPoint_cycleType_count_factorialMoment_sum_in
      (α := Fin n) (s := s) (a := a) (b := b) hs
      (by simpa [Fintype.card_fin] using h)

/-- Exact mixed factorial moment for two distinct nontrivial cycle lengths. -/
theorem factorialMoment_two_rCycle {n r s a b : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_two_factorialMoment_sum
      (n := n) (r := r) (s := s) (a := a) (b := b) hr hs hrs h
  have hsumReal :
      (r : ℝ) ^ a * (s : ℝ) ^ b *
          (∑ σ : Equiv.Perm (Fin n),
            ((rCycleCount n r σ).descFactorial a : ℝ) *
              ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < r))
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < s))
  have hpowR : (r : ℝ) ^ a * (s : ℝ) ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero a hrR) (pow_ne_zero b hsR)
  have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ((rCycleCount n r σ).descFactorial a : ℝ) *
            ((rCycleCount n s σ).descFactorial b : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / ((r : ℝ) ^ a * (s : ℝ) ^ b)) /
            (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hpowR]
    _ = (((r : ℝ) ^ a * (s : ℝ) ^ b)⁻¹) := by
          field_simp [hpowR, hnfacR]
    _ = (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
          simp [zpow_neg, zpow_natCast, mul_comm]

/-- The classical uncorrelated-count identity for two distinct nontrivial
cycle lengths. -/
theorem rCycleCount_mul_mean_eq_inv_mul_inv {n r s : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : r ≠ s)
    (h : r * 1 + s * 1 ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        (rCycleCount n r σ : ℝ) * (rCycleCount n s σ : ℝ)) =
        (r : ℝ) ^ (-(1 : ℤ)) * (s : ℝ) ^ (-(1 : ℤ)) := by
  simpa using
    factorialMoment_two_rCycle
      (n := n) (r := r) (s := s) (a := 1) (b := 1) hr hs hrs h

/-- Exact mixed factorial moment for fixed points and one nontrivial cycle
length, stated using the genuine `rCycleCount` variables. -/
theorem factorialMoment_one_and_rCycle {n s a b : ℕ}
    (hs : 2 ≤ s) (h : a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n 1 σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (1 : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_one_two_factorialMoment_sum
      (n := n) (s := s) (a := a) (b := b) hs h
  have hsumReal :
      (s : ℝ) ^ b *
          (∑ σ : Equiv.Perm (Fin n),
            ((rCycleCount n 1 σ).descFactorial a : ℝ) *
              ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < s))
  have hpowR : (s : ℝ) ^ b ≠ 0 := pow_ne_zero b hsR
  have hnfacR : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ((rCycleCount n 1 σ).descFactorial a : ℝ) *
            ((rCycleCount n s σ).descFactorial b : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / (s : ℝ) ^ b) / (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hpowR]
    _ = ((s : ℝ) ^ b)⁻¹ := by
          field_simp [hpowR, hnfacR]
    _ = (1 : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
          simp [zpow_neg, zpow_natCast]

/-- Unified exact mixed factorial moment for two distinct positive cycle
lengths.  This combines the nontrivial/nontrivial case with the fixed-point
branch for length `1`. -/
theorem factorialMoment_two_rCycle_of_pos {n r s a b : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s)
    (h : r * a + s * b ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ((rCycleCount n r σ).descFactorial a : ℝ) *
          ((rCycleCount n s σ).descFactorial b : ℝ)) =
        (r : ℝ) ^ (-(a : ℤ)) * (s : ℝ) ^ (-(b : ℤ)) := by
  classical
  rcases eq_or_ne r 1 with rfl | hrne
  · have hs2 : 2 ≤ s := by omega
    simpa using
      factorialMoment_one_and_rCycle
        (n := n) (s := s) (a := a) (b := b) hs2 (by simpa using h)
  · have hr2 : 2 ≤ r := by omega
    rcases eq_or_ne s 1 with rfl | hsne
    · have h' : b + r * a ≤ n := by omega
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        factorialMoment_one_and_rCycle
          (n := n) (s := r) (a := b) (b := a) hr2 h'
    · have hs2 : 2 ≤ s := by omega
      exact factorialMoment_two_rCycle
        (n := n) (r := r) (s := s) (a := a) (b := b) hr2 hs2 hrs h

end JointCycleMomentsNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
