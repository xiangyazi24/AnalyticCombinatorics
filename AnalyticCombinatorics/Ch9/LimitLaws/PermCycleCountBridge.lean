import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.PermutationCycles
import AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoisson
import AnalyticCombinatorics.Ch9.LimitLaws.ExpectedCycles

/-!
# Towards the Feller → uniform-permutation cycle-count bridge

The Gaussian cycle CLT proved in `PermutationCycles.lean`
(`permutationCycles_tendstoInDistribution_gaussian`) is stated for the **Feller
coupling** `cycleP n = Measure.pi (Bernoulli(1/(k+1)))`, NOT for the genuine
uniform permutation measure `uniformPermMeasure n`.  To upgrade the result to a
*faithful* statement about uniform random permutations one needs the
**equidistribution bridge**: the total cycle count of a uniform random
permutation of `Fin n` has the same law (on `ℕ`) as `∑_{k=1}^n Bern(1/k)`.

Both laws have the same probability generating function

  `E[x^{Ncyc}] = ∏_{k=1}^n (x + k - 1)/k = x^{(n)} / n!`   (rising factorial / n!),

so equality of laws follows from the **rising-factorial cycle-count identity**

  `∑_{σ : Perm (Fin n)} x^{Ncyc(σ)} = ∏_{k=0}^{n-1} (x + k)`.

This file banks the *verified foundation* for that identity: the behaviour of the
number-of-cycles statistic `numC` under the `Equiv.Perm.decomposeOption`
bijection `Perm (Option α) ≃ Option α × Perm α`, which is the inductive engine of
the rising-factorial identity.  The "none-fixed" half of the recursion is proved
here in full (clean-3).  The remaining "splice/merge" half — and the assembly
into the generating identity, the char-function computation, and the
`IdentDistrib` transport of the Gaussian CLT — is documented as the open content
in `HANDOFF/AUDIT-FIX-ch9.md`.

`numC σ` is the genuine number of orbits (cycles, including fixed points) of `σ`:
`numC σ = (#α - #support σ) + (#nontrivial cycles of σ)`
        = (number of fixed points) + (number of nontrivial cycles).
-/

noncomputable section

open Equiv Equiv.Perm

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace PermCycleCountBridge

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `α` is equivalent to the non-`none` elements of `Option α`, via `some`. -/
def someSub (α : Type*) : α ≃ {o : Option α // o ≠ none} where
  toFun a := ⟨some a, by simp⟩
  invFun o := o.1.get (Option.ne_none_iff_isSome.mp o.2)
  left_inv a := by simp
  right_inv := by rintro ⟨(_ | a), h⟩ <;> simp at h ⊢

/-- `optionCongr` (extend a permutation of `α` to `Option α` fixing `none`)
is exactly the `extendDomain` along the `some`-subtype embedding.  This lets us
reuse Mathlib's `cycleType`/`support` lemmas for `extendDomain`. -/
lemma optionCongr_eq_extendDomain (σ : Perm α) :
    σ.optionCongr = σ.extendDomain (someSub α) := by
  ext o
  cases o with
  | none => simp [Equiv.Perm.extendDomain_apply_not_subtype]
  | some a =>
      rw [Equiv.Perm.extendDomain_apply_subtype σ (someSub α) (by simp)]
      simp [someSub]

/-- Extending a permutation to `Option α` (fixing `none`) preserves the cycle
type: no new nontrivial cycle is created. -/
lemma cycleType_optionCongr (σ : Perm α) :
    Equiv.Perm.cycleType (α := Option α) σ.optionCongr = σ.cycleType := by
  rw [optionCongr_eq_extendDomain, Equiv.Perm.cycleType_extendDomain]

/-- Extending a permutation to `Option α` (fixing `none`) preserves the support
cardinality. -/
lemma support_card_optionCongr (σ : Perm α) :
    (Equiv.Perm.support (α := Option α) σ.optionCongr).card = σ.support.card := by
  rw [optionCongr_eq_extendDomain]
  exact Equiv.Perm.card_support_extend_domain _

/-- The number of orbits (cycles, including fixed points) of `σ`:
`#fixed points + #nontrivial cycles = (#α - #support) + #cycleType`. -/
def numC (σ : Perm α) : ℕ :=
  (Fintype.card α - σ.support.card) + Multiset.card σ.cycleType

private lemma support_card_le (σ : Perm α) : σ.support.card ≤ Fintype.card α := by
  exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)

/-- **None-fixed half of the cycle-count recursion.**
Extending `σ` to `Option α` by adjoining `none` as a new fixed point creates
exactly one new cycle (the singleton `{none}`):
`numC (σ.optionCongr) = numC σ + 1`.

This is the `x`-coefficient half of the rising-factorial recursion
`∑_{Perm (Option α)} x^{numC} = (x + #α) · ∑_{Perm α} x^{numC}`
(the `+1` cycle multiplies the generating sum by the leading `x`). -/
theorem numC_optionCongr (σ : Perm α) :
    numC (σ.optionCongr : Perm (Option α)) = numC σ + 1 := by
  unfold numC
  rw [support_card_optionCongr]
  have hc : Fintype.card (Option α) = Fintype.card α + 1 := by simp
  rw [hc, cycleType_optionCongr]
  have hle := support_card_le σ
  omega

/-- **Splice/merge, fixed-point subcase.**
If `z` and `y` are *both* fixed points of `τ` (`z ≠ y`), then `swap z y` is
disjoint from `τ`, so `swap z y * τ` replaces the two singleton cycles `{z}, {y}`
by a single transposition: `cycleType (swap z y * τ) = {2} + τ.cycleType`.

In the cycle-count recursion this is the subcase where the inserted element `none`
lands on a *fixed point* `some a` of `optionCongr σ` (i.e. `σ a = a`): the two
fixed points `none`, `some a` merge into one 2-cycle, so the orbit count is
unchanged.  This half of the splice is fully proved (clean-3). -/
theorem cycleType_swap_mul_of_both_fixed (τ : Perm α) {z y : α}
    (hz : τ z = z) (hy : τ y = y) (hzy : z ≠ y) :
    (swap z y * τ).cycleType = {2} + τ.cycleType := by
  have hdis : Disjoint (swap z y) τ := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro w
    by_cases hw : w = z
    · subst hw; right; exact hz
    · by_cases hw2 : w = y
      · subst hw2; right; exact hy
      · left; rw [Equiv.swap_apply_of_ne_of_ne hw hw2]
  rw [hdis.cycleType_mul, Equiv.Perm.IsCycle.cycleType (Equiv.Perm.isCycle_swap hzy),
    Equiv.Perm.card_support_swap hzy]

end PermCycleCountBridge
end LimitLaws
end Ch9
end AnalyticCombinatorics

-- Axiom audit (inline; clean-3 [propext, Classical.choice, Quot.sound])
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.cycleType_optionCongr
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.support_card_optionCongr
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.numC_optionCongr
#print axioms AnalyticCombinatorics.Ch9.LimitLaws.PermCycleCountBridge.cycleType_swap_mul_of_both_fixed
