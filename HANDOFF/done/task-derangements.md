# Task — Derangements example

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (new). Add to root.

**Goal:** Define the class of derangements (fixed-point-free permutations) and prove its count equals Mathlib's `Nat.numDerangements`.

```lean
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Perm

open CombinatorialClass

/-- A derangement of size n is a fixed-point-free permutation of `Fin n`. -/
def derangementClass : CombinatorialClass where
  Obj := Σ n : ℕ, { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ :
      Set { σ : Equiv.Perm (Fin n) // ∀ i, σ i ≠ i }) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, σ⟩ hkσ
    simp only [Set.mem_setOf_eq] at hkσ
    subst hkσ
    exact ⟨σ, Set.mem_univ _, rfl⟩

/-- Count of derangements of size n equals Mathlib's `numDerangements n`. -/
theorem derangementClass_count_eq_numDerangements (n : ℕ) :
    derangementClass.count n = Nat.numDerangements n := by
  sorry  -- Bijection: derangementClass.level n ≃ derangements (Fin n)
         -- where derangements is Mathlib's set / Finset of fixed-point-free perms.
         -- Pattern from permClass.count_eq_factorial.
         -- Mathlib has `Fintype.card_derangements : Fintype.card (derangements α) = numDerangements (Fintype.card α)`
         -- (or similar — check Mathlib).
```

## Strategy

Mirror `permClass.count_eq_factorial`:
1. Express `derangementClass.level n` as the image of `(Finset.univ : Finset {σ // ∀ i, σ i ≠ i})` under `Sigma.mk n`.
2. `Finset.card_image_of_injective` + `Sigma.mk` injectivity.
3. Connect to Mathlib's `Nat.numDerangements n` via Mathlib's API for fixed-point-free perms.

If Mathlib's API is `Fintype.card (derangements (Fin n)) = Nat.numDerangements n`, chain it.

If the Mathlib bridge is hard, alternative: prove via the recurrence `Nat.numDerangements_add_two` matched against an inductive argument on derangementClass.

## Hard constraints

- Build green
- No new sorrys
- Add new file to AnalyticCombinatorics.lean root imports
- Reply at HANDOFF/outbox/task-derangements-reply.md
