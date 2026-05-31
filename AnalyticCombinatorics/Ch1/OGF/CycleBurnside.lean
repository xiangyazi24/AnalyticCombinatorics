import AnalyticCombinatorics.Ch1.OGF.CycleModel

/-!
# Ch1 §I.2 — Cycle Burnside layer

This file assembles the per-length Burnside count and groups rotations by
their gcd with the cycle length.
-/

namespace AnalyticCombinatorics.Ch1

open scoped BigOperators

lemma burnside_necklaces_k
    (C : CombClass) (n k : ℕ) [NeZero k] :
    k * Fintype.card (necklaces_k C n k) =
      ∑ a : ZMod k, Fintype.card (AddAction.fixedBy (Word C n k) a) := by
  classical
  have h :=
    AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
      (ZMod k) (Word C n k)
  rw [ZMod.card] at h
  rw [mul_comm]
  exact h.symm

lemma sum_zmod_by_gcd
    (k : ℕ) [NeZero k] (F : ℕ → ℕ) :
    (∑ a : ZMod k, F (k.gcd a.val)) =
      ∑ g ∈ k.divisors, Nat.totient (k / g) * F g := by
  classical
  have hzmod_fin :
      (∑ a : ZMod k, F (k.gcd a.val)) =
        ∑ i : Fin k, F (k.gcd i.val) := by
    cases k with
    | zero =>
        exact (NeZero.ne 0 rfl).elim
    | succ _ =>
        rfl
  have hfin_range :
      (∑ i : Fin k, F (k.gcd i.val)) =
        ∑ i ∈ Finset.range k, F (k.gcd i) := by
    refine
      (Finset.sum_fin_eq_sum_range
        (fun i : Fin k => F (k.gcd i.val))).trans ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  have hmaps : ∀ i ∈ Finset.range k, k.gcd i ∈ k.divisors := by
    intro i _hi
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left k i, NeZero.ne k⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := Finset.range k) (t := k.divisors)
      (g := fun i : ℕ => k.gcd i) hmaps
      (fun i : ℕ => F (k.gcd i))
  calc
    (∑ a : ZMod k, F (k.gcd a.val)) =
        ∑ i ∈ Finset.range k, F (k.gcd i) :=
      hzmod_fin.trans hfin_range
    _ = ∑ g ∈ k.divisors, Nat.totient (k / g) * F g := by
      rw [← hfiber]
      refine Finset.sum_congr rfl ?_
      intro g hg
      calc
        (∑ i ∈ Finset.range k with k.gcd i = g, F (k.gcd i)) =
            ∑ i ∈ Finset.range k with k.gcd i = g, F g := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact congrArg F (Finset.mem_filter.mp hi).2
        _ = (Finset.filter (fun i => k.gcd i = g) (Finset.range k)).card * F g := by
          simp
        _ = Nat.totient (k / g) * F g := by
          rw [← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hg)]

lemma counts_necklaces_k
    (C : CombClass) (n k : ℕ) [NeZero k] :
    k * Fintype.card (necklaces_k C n k) =
      ∑ g ∈ k.divisors,
        if k / g ∣ n then
          Nat.totient (k / g) *
            Fintype.card (BlockWord C (n / (k / g)) g)
        else 0 := by
  classical
  let F : ℕ → ℕ := fun g =>
    if k / g ∣ n then
      Fintype.card (BlockWord C (n / (k / g)) g)
    else 0
  calc
    k * Fintype.card (necklaces_k C n k) =
        ∑ a : ZMod k, Fintype.card (AddAction.fixedBy (Word C n k) a) :=
      burnside_necklaces_k C n k
    _ = ∑ a : ZMod k, F (k.gcd a.val) := by
      refine Finset.sum_congr rfl ?_
      intro a _ha
      simp [F, card_fixedBy_rotation, addOrderOf_eq_k_div_gcd_val]
    _ = ∑ g ∈ k.divisors,
        if k / g ∣ n then
          Nat.totient (k / g) *
            Fintype.card (BlockWord C (n / (k / g)) g)
        else 0 := by
      simpa [F, mul_ite] using (sum_zmod_by_gcd k F)

end AnalyticCombinatorics.Ch1
