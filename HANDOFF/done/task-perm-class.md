# Task — `permClass` with `count_eq_factorial`

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append after `coeff_exp_sq_eq_pow_div_factorial`)

**Goal:** Define a CombinatorialClass for permutations with size-n object = `Equiv.Perm (Fin n)`, and prove its count is `n!`.

## Required code

```lean
-- Need extra import:
import Mathlib.Data.Fintype.Perm

/-- The class of permutations: at size n, the objects are bijections of `Fin n`. -/
def permClass : CombinatorialClass where
  Obj := Σ n : ℕ, Equiv.Perm (Fin n)
  size := Sigma.fst
  finite_level n := by
    have hfin : Set.Finite (Set.univ : Set (Equiv.Perm (Fin n))) := Set.toFinite _
    apply Set.Finite.subset (hfin.image (Sigma.mk n))
    rintro ⟨k, σ⟩ hkσ
    simp only [Set.mem_setOf_eq] at hkσ
    subst hkσ
    exact ⟨σ, Set.mem_univ _, rfl⟩

/-- Count of permutations of size n equals n!. -/
theorem permClass_count_eq_factorial (n : ℕ) : permClass.count n = n.factorial := by
  sorry  -- this is the hard part
```

## Why this needs you

Zinan (Opus 4.7) tried 4 versions and kept getting stuck on `Σ k, Equiv.Perm (Fin k)` membership unfolding:
- Sigma type's first projection (`Sigma.fst`) doesn't reduce through `permClass.size` automatically when it's the structure projection in `level_mem_iff`.
- `▸` transport along `s.fst = n` triggers application type mismatch when the source `s.snd : Perm (Fin s.fst)` isn't unifying with `Perm (Fin n)`.
- `Finset.mem_image` rewrites failed pattern matching on `Sigma.mk n` images.

**You need to make this proof go through.** Approach options:

1. **Direct Fintype/card route** — show `(permClass.level n).card = Fintype.card (Equiv.Perm (Fin n))` via a Finset bijection, then chain `Fintype.card_perm` + `Fintype.card_fin`.

2. **Image equality** — show `permClass.level n = (Finset.univ : Finset (Perm (Fin n))).image (Sigma.mk n)` then `Finset.card_image_of_injective`. Sigma.mk with fixed first index is injective.

3. **Explicit Equiv** — build `Equiv` between `permClass.level n` (as a subtype) and `Equiv.Perm (Fin n)`, then transport card.

Pick whichever you can land cleanly. Target: lake build green.

## Hard constraints

- Don't use `axiom`. Don't replace with `True`. Don't replace `Sigma` with a different structure.
- Don't modify `CombinatorialClass.lean` core (the `level_mem_iff` is public; you may use it).
- Two real attempts; if both fail, file a blocker in `HANDOFF/outbox/task-perm-class-reply.md` documenting where exactly the typeclass synthesis or unification breaks.

## Lake commands

```bash
cd ~/repos/AnalyticCombinatorics
PATH="/Users/huangx/.elan/bin:$PATH" lake build 2>&1 | grep -E "^error|sorry|completed" | tail -10
```

Build is currently green (2763 jobs, 0 sorrys). Don't break the existing file.

## Report

Reply to `HANDOFF/outbox/task-perm-class-reply.md` with diff summary + `Codex: idle — task done` (or blocker).
