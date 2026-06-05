import Mathlib
import AnalyticCombinatorics.Ch1.Polya.Enumeration

/-!
# Binary necklaces, totient form

This file converts the gcd-form Burnside sum for binary necklaces into the
classical Euler-totient form.
-/

namespace AnalyticCombinatorics.Ch1.Polya.NecklacePhi

open scoped BigOperators

attribute [local instance] arrowAction

noncomputable local instance orbitRelDecidableRel {G X : Type*} [Group G] [MulAction G X] :
    DecidableRel (MulAction.orbitRel G X).r :=
  Classical.decRel _

noncomputable local instance orbitQuotientFintype (n : ℕ) [NeZero n] :
    Fintype
      (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) :=
  Quotient.fintype (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → Bool))

/-- Regroup a sum over `ZMod n` by the value of `gcd n a.val`. -/
lemma sum_zmod_by_gcd
    (n : ℕ) [NeZero n] (F : ℕ → ℕ) :
    (∑ a : ZMod n, F (n.gcd a.val)) =
      ∑ d ∈ n.divisors, Nat.totient (n / d) * F d := by
  classical
  have hzmod_fin :
      (∑ a : ZMod n, F (n.gcd a.val)) =
        ∑ i : Fin n, F (n.gcd i.val) := by
    cases n with
    | zero =>
        exact (NeZero.ne 0 rfl).elim
    | succ _ =>
        rfl
  have hfin_range :
      (∑ i : Fin n, F (n.gcd i.val)) =
        ∑ i ∈ Finset.range n, F (n.gcd i) := by
    refine
      (Finset.sum_fin_eq_sum_range
        (fun i : Fin n => F (n.gcd i.val))).trans ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  have hmaps : ∀ i ∈ Finset.range n, n.gcd i ∈ n.divisors := by
    intro i _hi
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n i, NeZero.ne n⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := Finset.range n) (t := n.divisors)
      (g := fun i : ℕ => n.gcd i) hmaps
      (fun i : ℕ => F (n.gcd i))
  calc
    (∑ a : ZMod n, F (n.gcd a.val)) =
        ∑ i ∈ Finset.range n, F (n.gcd i) :=
      hzmod_fin.trans hfin_range
    _ = ∑ d ∈ n.divisors, Nat.totient (n / d) * F d := by
      rw [← hfiber]
      refine Finset.sum_congr rfl ?_
      intro d hd
      calc
        (∑ i ∈ Finset.range n with n.gcd i = d, F (n.gcd i)) =
            ∑ i ∈ Finset.range n with n.gcd i = d, F d := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact congrArg F (Finset.mem_filter.mp hi).2
        _ = (Finset.filter (fun i => n.gcd i = d) (Finset.range n)).card * F d := by
          simp
        _ = Nat.totient (n / d) * F d := by
          rw [← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- The gcd-form Burnside sum for binary necklaces, regrouped by gcd fibers. -/
theorem binary_necklace_gcd_sum_eq_totient_sum
    (n : ℕ) [NeZero n] :
    (∑ k : ZMod n, 2 ^ Nat.gcd n k.val) =
      ∑ d ∈ n.divisors, Nat.totient (n / d) * 2 ^ d := by
  simpa using sum_zmod_by_gcd n (fun d => 2 ^ d)

/-- The two classical divisor-indexed totient forms agree by the involution `d ↦ n / d`. -/
theorem binary_necklace_totient_sum_eq_divisor_involution (n : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient (n / d) * 2 ^ d) =
      ∑ d ∈ n.divisors, Nat.totient d * 2 ^ (n / d) := by
  by_cases hn : n = 0
  · simp [hn]
  rw [← Nat.sum_div_divisors n (fun d => Nat.totient d * 2 ^ (n / d))]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn]

/-- Binary necklaces in the classical Euler-totient form. -/
theorem card_binary_necklaces_phi (n : ℕ) (hn : 0 < n) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    Fintype.card
        (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) * n =
      ∑ d ∈ n.divisors, Nat.totient (n / d) * 2 ^ d := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  calc
    Fintype.card
          (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) * n =
        ∑ k : ZMod n, 2 ^ Nat.gcd n k.val :=
      AnalyticCombinatorics.Ch1.Polya.card_binary_necklaces n hn
    _ = ∑ d ∈ n.divisors, Nat.totient (n / d) * 2 ^ d :=
      binary_necklace_gcd_sum_eq_totient_sum n

/-- Binary necklaces in the equivalent `φ d * 2 ^ (n / d)` divisor form. -/
theorem card_binary_necklaces_phi_standard (n : ℕ) (hn : 0 < n) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    Fintype.card
        (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) * n =
      ∑ d ∈ n.divisors, Nat.totient d * 2 ^ (n / d) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  calc
    Fintype.card
          (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → Bool)) * n =
        ∑ d ∈ n.divisors, Nat.totient (n / d) * 2 ^ d :=
      card_binary_necklaces_phi n hn
    _ = ∑ d ∈ n.divisors, Nat.totient d * 2 ^ (n / d) :=
      binary_necklace_totient_sum_eq_divisor_involution n

end AnalyticCombinatorics.Ch1.Polya.NecklacePhi
