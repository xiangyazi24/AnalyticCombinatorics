import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesFactorialMoment
import AnalyticCombinatorics.Ch9.LimitLaws.JointCycleMoments

/-!
# General joint factorial moments for permutation cycle counts

This file extends the fixed-length and two-length factorial-moment identities
to arbitrary finite families of distinct positive lengths.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace JointCycleMomentsGeneralNS

section GeneralFiniteNontrivial

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_prod_containing_from_complement_ne {r : ℕ} (T : Finset ℕ)
    (k : ℕ → ℕ) (hrT : r ∉ T)
    (c : FM.CyclesOfLengthIn (α := α) r)
    (τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support}) :
    (∏ s ∈ T,
        (((FM.permComplementEquivContainingCycleIn c τ).1.cycleType.count s).descFactorial
          (k s))) =
      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro s hs
  have hsr : s ≠ r := by
    intro hsr
    exact hrT (by simpa [hsr] using hs)
  rw [JointCycleMomentsNS.cycleType_count_containing_from_complement_ne
    (α := α) (s := s) (r := r) hsr c τ]

theorem cycleType_count_factorialMoment_sum_insert_in {r : ℕ} {T : Finset ℕ}
    (k : ℕ → ℕ) (hrT : r ∉ T) (hr : 2 ≤ r)
    (ihT :
      ∀ {β : Type u} [Fintype β] [DecidableEq β],
        (∑ s ∈ T, s * k s ≤ Fintype.card β) →
          (∏ s ∈ T, s ^ k s) *
              (∑ σ : Equiv.Perm β,
                ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            (Fintype.card β).factorial)
    {a : ℕ} (h : r * a + ∑ s ∈ T, s * k s ≤ Fintype.card α) :
    r ^ a * (∏ s ∈ T, s ^ k s) *
        (∑ σ : Equiv.Perm α,
          (σ.cycleType.count r).descFactorial a *
            ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hT : ∑ s ∈ T, s * k s ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using ihT (β := α) hT
  | succ a iha =>
      intro α _ _ h
      have hrα : r ≤ Fintype.card α := by
        calc
          r = r * 1 := by simp
          _ ≤ r * (a + 1) := Nat.mul_le_mul_left r (Nat.succ_pos a)
          _ ≤ Fintype.card α := by omega
      have hrec_card :
          r * a + ∑ s ∈ T, s * k s ≤ Fintype.card α - r := by
        apply Nat.le_sub_of_add_le
        calc
          r * a + ∑ s ∈ T, s * k s + r =
              r * (a + 1) + ∑ s ∈ T, s * k s := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            ∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
        calc
          (∑ σ : Equiv.Perm α,
            (σ.cycleType.count r).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (FM.CyclesOfLengthOfPermIn (α := α) r σ) *
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [FM.card_cyclesOfLengthOfPermIn (α := α) (r := r) σ]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _c : FM.CyclesOfLengthOfPermIn (α := α) r σ,
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ x : FM.CycleByPermIn (α := α) r,
                  (((x.1.cycleType.count r - 1).descFactorial a) *
                    ∏ s ∈ T, (x.1.cycleType.count s).descFactorial (k s)) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_c : FM.CyclesOfLengthOfPermIn (α := α) r σ) =>
                    (((σ.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)))).symm
          _ = ∑ x : FM.CycleByCycleIn (α := α) r,
                  (((x.2.1.cycleType.count r - 1).descFactorial a) *
                    ∏ s ∈ T, (x.2.1.cycleType.count s).descFactorial (k s)) := by
                exact Fintype.sum_equiv (FM.cycleByPermEquivCycleByCycleIn (α := α) r)
                  (fun x : FM.CycleByPermIn (α := α) r =>
                    (((x.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (x.1.cycleType.count s).descFactorial (k s)))
                  (fun x : FM.CycleByCycleIn (α := α) r =>
                    (((x.2.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (x.2.1.cycleType.count s).descFactorial (k s)))
                  (by intro x; rfl)
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ σ : FM.PermContainingCycleIn c,
                    (((σ.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)) := by
                rw [Fintype.sum_sigma]
          _ = ∑ c : FM.CyclesOfLengthIn (α := α) r,
                  ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
                refine Finset.sum_congr rfl ?_
                intro c _hc
                exact (Fintype.sum_equiv (FM.permComplementEquivContainingCycleIn c)
                  (fun τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support} =>
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
                  (fun σ : FM.PermContainingCycleIn c =>
                    (((σ.1.cycleType.count r - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)))
                  (by
                    intro τ
                    change
                      (τ.cycleType.count r).descFactorial a *
                          (∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
                        ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count r -
                            1).descFactorial a *
                          ∏ s ∈ T,
                            ((((FM.permComplementEquivContainingCycleIn c) τ).1.cycleType.count s).descFactorial
                              (k s)))
                    rw [← FM.cycleType_count_containing_from_complement (k := a) c τ]
                    rw [← cycleType_count_prod_containing_from_complement_ne
                      (α := α) (r := r) T k hrT c τ])).symm
      have hinner :
          ∀ c : FM.CyclesOfLengthIn (α := α) r,
            r ^ a * (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card α - r).factorial := by
        intro c
        have hc_card :
            Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support} =
              Fintype.card α - r :=
          FM.card_complement_cycle_support_in c
        have hrec :
            r ^ a * (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                  (τ.cycleType.count r).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card {x : α // x ∉ (c : Equiv.Perm α).support}).factorial :=
          iha (α := {x : α // x ∉ (c : Equiv.Perm α).support}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        r ^ (a + 1) * (∏ s ∈ T, s ^ k s) *
            (∑ c : FM.CyclesOfLengthIn (α := α) r,
              ∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                (τ.cycleType.count r).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
            = r * (∑ c : FM.CyclesOfLengthIn (α := α) r,
                r ^ a * (∏ s ∈ T, s ^ k s) *
                  (∑ τ : Equiv.Perm {x : α // x ∉ (c : Equiv.Perm α).support},
                    (τ.cycleType.count r).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))) := by
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

theorem cycleType_count_factorialMoment_sum_finset_in (S : Finset ℕ) :
    ∀ {α : Type u} [Fintype α] [DecidableEq α] (k : ℕ → ℕ),
      (∀ r ∈ S, 2 ≤ r) →
      (∑ r ∈ S, r * k r ≤ Fintype.card α) →
      (∏ r ∈ S, r ^ k r) *
          (∑ σ : Equiv.Perm α,
            ∏ r ∈ S, (σ.cycleType.count r).descFactorial (k r)) =
      (Fintype.card α).factorial := by
  classical
  intro α _ _ k hpos h
  induction S using Finset.induction generalizing α k with
  | empty =>
    simp [Fintype.card_perm]
  | insert r T hrT ih =>
    have hr : 2 ≤ r := hpos r (Finset.mem_insert_self r T)
    have hTpos : ∀ s ∈ T, 2 ≤ s := by
      intro s hs
      exact hpos s (Finset.mem_insert_of_mem hs)
    have ihT :
        ∀ {β : Type u} [Fintype β] [DecidableEq β],
          (∑ s ∈ T, s * k s ≤ Fintype.card β) →
            (∏ s ∈ T, s ^ k s) *
                (∑ σ : Equiv.Perm β,
                  ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card β).factorial := by
      intro β _ _ hb
      exact ih (α := β) (k := k) hTpos hb
    have h' : r * k r + ∑ s ∈ T, s * k s ≤ Fintype.card α := by
      simpa [Finset.sum_insert, hrT] using h
    have hmain :=
      cycleType_count_factorialMoment_sum_insert_in
        (α := α) (r := r) (T := T) (k := k) hrT hr ihT (a := k r) h'
    simpa [Finset.prod_insert, hrT, mul_assoc] using hmain

end GeneralFiniteNontrivial

section GeneralFiniteWithFixedPoints

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

lemma cycleType_count_prod_fixingPoint_from_complement (T : Finset ℕ)
    (k : ℕ → ℕ) (x : α) (τ : Equiv.Perm {y : α // y ≠ x}) :
    (∏ s ∈ T, (((JointCycleMomentsNS.permComplementEquivFixingPointIn
        (α := α) x τ).1.cycleType.count s).descFactorial (k s))) =
      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro s _hs
  rw [JointCycleMomentsNS.cycleType_count_fixingPoint_from_complement
    (α := α) (s := s) x τ]

theorem fixedPoint_cycleType_count_factorialMoment_sum_finset_in (T : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ s ∈ T, 2 ≤ s) {a : ℕ}
    (h : a + ∑ s ∈ T, s * k s ≤ Fintype.card α) :
    (∏ s ∈ T, s ^ k s) *
        (∑ σ : Equiv.Perm α,
          (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial a *
            ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
      (Fintype.card α).factorial := by
  classical
  revert α
  induction a with
  | zero =>
      intro α _ _ h
      have hT : ∑ s ∈ T, s * k s ≤ Fintype.card α := by simpa using h
      simpa [mul_assoc] using
        cycleType_count_factorialMoment_sum_finset_in
          (S := T) (α := α) k hpos hT
  | succ a iha =>
      intro α _ _ h
      have hcard0 : Fintype.card α ≠ 0 := by omega
      have hrec_card :
          a + ∑ s ∈ T, s * k s ≤ Fintype.card α - 1 := by
        apply Nat.le_sub_of_add_le
        calc
          a + ∑ s ∈ T, s * k s + 1 =
              a + 1 + ∑ s ∈ T, s * k s := by ring
          _ ≤ Fintype.card α := h
      have hstep :
          (∑ σ : Equiv.Perm α,
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) =
            ∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
        calc
          (∑ σ : Equiv.Perm α,
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (a + 1) *
              ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s))
              = ∑ σ : Equiv.Perm α,
                  Fintype.card (JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ) *
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [JointCycleMomentsNS.fixedPointCountIn]
                rw [FM.descFactorial_succ_eq_mul_pred]
                ring
          _ = ∑ σ : Equiv.Perm α,
                  ∑ _x : JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ,
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)) := by
                refine Finset.sum_congr rfl ?_
                intro σ _hσ
                rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
          _ = ∑ z : JointCycleMomentsNS.FixedPointByPermIn (α := α),
                  (((JointCycleMomentsNS.fixedPointCountIn z.1 - 1).descFactorial a) *
                    ∏ s ∈ T, (z.1.cycleType.count s).descFactorial (k s)) := by
                exact (Fintype.sum_sigma'
                  (fun σ (_x : JointCycleMomentsNS.FixedPointsOfPermIn (α := α) σ) =>
                    (((JointCycleMomentsNS.fixedPointCountIn σ - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.cycleType.count s).descFactorial (k s)))).symm
          _ = ∑ z : JointCycleMomentsNS.FixedPointByPointIn (α := α),
                  (((JointCycleMomentsNS.fixedPointCountIn z.2.1 - 1).descFactorial a) *
                    ∏ s ∈ T, (z.2.1.cycleType.count s).descFactorial (k s)) := by
                exact Fintype.sum_equiv
                  (JointCycleMomentsNS.fixedPointByPermEquivByPointIn (α := α))
                  (fun z : JointCycleMomentsNS.FixedPointByPermIn (α := α) =>
                    (((JointCycleMomentsNS.fixedPointCountIn z.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (z.1.cycleType.count s).descFactorial (k s)))
                  (fun z : JointCycleMomentsNS.FixedPointByPointIn (α := α) =>
                    (((JointCycleMomentsNS.fixedPointCountIn z.2.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (z.2.1.cycleType.count s).descFactorial (k s)))
                  (by intro z; rfl)
          _ = ∑ x : α,
                  ∑ σ : JointCycleMomentsNS.PermFixingPointIn (α := α) x,
                    (((JointCycleMomentsNS.fixedPointCountIn σ.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)) := by
                rw [Fintype.sum_sigma]
          _ = ∑ x : α,
                  ∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s) := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                exact (Fintype.sum_equiv
                  (JointCycleMomentsNS.permComplementEquivFixingPointIn (α := α) x)
                  (fun τ : Equiv.Perm {y : α // y ≠ x} =>
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
                  (fun σ : JointCycleMomentsNS.PermFixingPointIn (α := α) x =>
                    (((JointCycleMomentsNS.fixedPointCountIn σ.1 - 1).descFactorial a) *
                      ∏ s ∈ T, (σ.1.cycleType.count s).descFactorial (k s)))
                  (by
                    intro τ
                    change
                      (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                          (∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
                        ((JointCycleMomentsNS.fixedPointCountIn
                            ((JointCycleMomentsNS.permComplementEquivFixingPointIn
                              (α := α) x) τ).1 - 1).descFactorial a *
                          ∏ s ∈ T,
                            ((((JointCycleMomentsNS.permComplementEquivFixingPointIn
                              (α := α) x) τ).1.cycleType.count s).descFactorial (k s)))
                    rw [← JointCycleMomentsNS.fixedPointCount_fixingPoint_from_complement_desc
                      (α := α) x τ]
                    rw [← cycleType_count_prod_fixingPoint_from_complement
                      (α := α) T k x τ])).symm
      have hinner :
          ∀ x : α,
            (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card α - 1).factorial := by
        intro x
        have hc_card :
            Fintype.card {y : α // y ≠ x} = Fintype.card α - 1 :=
          JointCycleMomentsNS.card_complement_point x
        have hrec :
            (∏ s ∈ T, s ^ k s) *
                (∑ τ : Equiv.Perm {y : α // y ≠ x},
                  (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                    ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) =
              (Fintype.card {y : α // y ≠ x}).factorial :=
          iha (α := {y : α // y ≠ x}) (by
            rw [hc_card]
            exact hrec_card)
        rwa [hc_card] at hrec
      rw [hstep]
      calc
        (∏ s ∈ T, s ^ k s) *
            (∑ x : α,
              ∑ τ : Equiv.Perm {y : α // y ≠ x},
                (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                  ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s))
            = ∑ x : α,
                (∏ s ∈ T, s ^ k s) *
                  (∑ τ : Equiv.Perm {y : α // y ≠ x},
                    (JointCycleMomentsNS.fixedPointCountIn τ).descFactorial a *
                      ∏ s ∈ T, (τ.cycleType.count s).descFactorial (k s)) := by
              rw [Finset.mul_sum]
        _ = ∑ _x : α, (Fintype.card α - 1).factorial := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hinner x
        _ = Fintype.card α * (Fintype.card α - 1).factorial := by
              rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = (Fintype.card α).factorial := by
              exact Nat.mul_factorial_pred hcard0

end GeneralFiniteWithFixedPoints

section FinCycleCounts

theorem rCycleCount_factorialMoment_sum_finset {n : ℕ} (S : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ r ∈ S, 0 < r)
    (h : ∑ r ∈ S, r * k r ≤ n) :
    (∏ r ∈ S, r ^ k r) *
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, (rCycleCount n r σ).descFactorial (k r)) =
      n.factorial := by
  classical
  by_cases h1 : 1 ∈ S
  · have hSinsert : insert 1 (S.erase 1) = S := Finset.insert_erase h1
    have hTpos : ∀ r ∈ S.erase 1, 2 ≤ r := by
      intro r hr
      have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
      have hrS : r ∈ S := (Finset.mem_erase.mp hr).2
      have hrpos : 0 < r := hpos r hrS
      omega
    have hbound : k 1 + ∑ r ∈ S.erase 1, r * k r ≤ n := by
      have h' : ∑ r ∈ insert 1 (S.erase 1), r * k r ≤ n := by
        simpa [hSinsert] using h
      simpa [Finset.sum_insert, one_mul] using h'
    have hfixed :
        (∏ r ∈ S.erase 1, r ^ k r) *
            (∑ σ : Equiv.Perm (Fin n),
              (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (k 1) *
                ∏ r ∈ S.erase 1, (σ.cycleType.count r).descFactorial (k r)) =
          n.factorial := by
      simpa [Fintype.card_fin] using
        fixedPoint_cycleType_count_factorialMoment_sum_finset_in
          (α := Fin n) (T := S.erase 1) (k := k) hTpos (a := k 1)
          (by simpa [Fintype.card_fin] using hbound)
    have hpow :
        (∏ r ∈ insert 1 (S.erase 1), r ^ k r) =
          ∏ r ∈ S.erase 1, r ^ k r := by
      rw [Finset.prod_insert (by simp)]
      simp
    have hsum :
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ insert 1 (S.erase 1), (rCycleCount n r σ).descFactorial (k r)) =
          ∑ σ : Equiv.Perm (Fin n),
            (JointCycleMomentsNS.fixedPointCountIn σ).descFactorial (k 1) *
              ∏ r ∈ S.erase 1, (σ.cycleType.count r).descFactorial (k r) := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      rw [Finset.prod_insert (by simp)]
      rw [rCycleCount_one]
      rw [← JointCycleMomentsNS.fixedPointCountIn_fin n σ]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro r hr
      have hrne : r ≠ 1 := (Finset.mem_erase.mp hr).1
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [← hSinsert, hpow, hsum]
    exact hfixed
  · have hnontriv : ∀ r ∈ S, 2 ≤ r := by
      intro r hr
      have hrpos : 0 < r := hpos r hr
      have hrne : r ≠ 1 := by
        intro hr1
        exact h1 (by simpa [hr1] using hr)
      omega
    have hsum :
        (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, (rCycleCount n r σ).descFactorial (k r)) =
          ∑ σ : Equiv.Perm (Fin n),
            ∏ r ∈ S, (σ.cycleType.count r).descFactorial (k r) := by
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      refine Finset.prod_congr rfl ?_
      intro r hr
      have hrne : r ≠ 1 := by
        intro hr1
        exact h1 (by simpa [hr1] using hr)
      rw [rCycleCount_eq_cycleType_count_of_ne_one hrne σ]
    rw [hsum]
    simpa [Fintype.card_fin] using
      cycleType_count_factorialMoment_sum_finset_in
        (S := S) (α := Fin n) k hnontriv (by simpa [Fintype.card_fin] using h)

theorem factorialMoment_rCycle_finset {n : ℕ} (S : Finset ℕ)
    (k : ℕ → ℕ) (hpos : ∀ r ∈ S, 0 < r)
    (h : ∑ r ∈ S, r * k r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
      ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := by
  classical
  unfold FixedPointsPoissonNS.uniformPermExpectation
  have hsumNat :=
    rCycleCount_factorialMoment_sum_finset (n := n) (S := S) (k := k) hpos h
  have hsumReal :
      (∏ r ∈ S, (r : ℝ) ^ k r) *
          (∑ σ : Equiv.Perm (Fin n),
            ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hsumNat
  have hprod_pos : 0 < ∏ r ∈ S, (r : ℝ) ^ k r := by
    refine Finset.prod_pos ?_
    intro r hr
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hpos r hr
    exact pow_pos hrR (k r)
  have hprod_ne : (∏ r ∈ S, (r : ℝ) ^ k r) ≠ 0 := ne_of_gt hprod_pos
  have hnfac_ne : (n.factorial : ℝ) ≠ 0 := by positivity
  calc
    (∑ σ : Equiv.Perm (Fin n),
          ∏ r ∈ S, ((rCycleCount n r σ).descFactorial (k r) : ℝ)) /
        (n.factorial : ℝ)
        = ((n.factorial : ℝ) / (∏ r ∈ S, (r : ℝ) ^ k r)) /
            (n.factorial : ℝ) := by
          rw [← hsumReal]
          field_simp [hprod_ne]
    _ = (∏ r ∈ S, (r : ℝ) ^ k r)⁻¹ := by
          field_simp [hprod_ne, hnfac_ne]
    _ = ∏ r ∈ S, (r : ℝ) ^ (-(k r : ℤ)) := by
          rw [← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl ?_
          intro r _hr
          simp [zpow_neg, zpow_natCast]

theorem rCycleCount_prod_mean_eq_prod_inv {n : ℕ} (S : Finset ℕ)
    (hpos : ∀ r ∈ S, 0 < r) (h : ∑ r ∈ S, r ≤ n) :
    FixedPointsPoissonNS.uniformPermExpectation n
      (fun σ : Equiv.Perm (Fin n) =>
        ∏ r ∈ S, (rCycleCount n r σ : ℝ)) =
      ∏ r ∈ S, (r : ℝ)⁻¹ := by
  simpa [Nat.descFactorial_one, zpow_neg_one, one_mul] using
    factorialMoment_rCycle_finset
      (n := n) (S := S) (k := fun _ => 1) hpos
      (by simpa [one_mul] using h)

end FinCycleCounts

end JointCycleMomentsGeneralNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics
