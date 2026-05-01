# Task — labelSetCount Atom n = 1

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Prove that the labelled SET of `Atom` (the size-1 atomic class with `count 1 = 1`) has `labelSetCount n = 1` for every `n`. Equivalently, "every size-n labelled set built from size-1 atoms = exactly the unique partition into singletons".

This is the labelled-SET analogue of `singletonClass.count_eq_one` and gives another route to `(labelSet Atom).egf = exp(z)`.

## Required code

```lean
/-- Atom has no size-0 element. -/
theorem Atom_count_zero : Atom.count 0 = 0 := by
  show (Atom.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have := (CombinatorialClass.level_mem_iff (C := Atom) x).mp hx
  change (1 : ℕ) = 0 at this
  exact one_ne_zero this

/-- Iterated labelled product of Atom: count is k! · δ_{k,n}. -/
theorem labelPow_Atom_count (k n : ℕ) :
    (CombinatorialClass.labelPow Atom k).count n = if n = k then n.factorial else 0 := by
  sorry  -- by induction on k:
         --  k = 0: labelPow Atom 0 = Epsilon, count is δ_{n,0}.
         --         n = k = 0 case: 1 = 0.factorial. else 0.
         --  k+1: labelPow Atom (k+1) = Atom.labelProd (labelPow Atom k).
         --       Use labelProd_count_eq_labelProdCount + Atom_count formula
         --       (Atom.count i = δ_{i,1}) + IH on labelPow Atom k.
         --       Sum collapses: (n choose 1) · k! when n = k+1, else 0.
         --       (n choose 1) · k! = n · k! = (k+1)! when n = k+1. ✓

/-- The labelled SET of Atom has constant count 1 at every size. -/
theorem labelSetCount_Atom (n : ℕ) :
    CombinatorialClass.labelSetCount Atom n = 1 := by
  sorry  -- unfold labelSetCount = ∑ k ∈ range (n+1), (labelPow Atom k).count n / k!
         -- by labelPow_Atom_count, only k = n contributes:
         -- = (labelPow Atom n).count n / n!
         -- = n! / n! = 1.
```

## Dependencies (already in scope)

- `CombinatorialClass.labelPow`, `labelPow_egf`
- `CombinatorialClass.labelSetCount`
- `CombinatorialClass.labelProd_count_eq_labelProdCount`
- `Atom.count` formula via `level_mem_iff`
- `CombinatorialClass.labelProdCount`, `Epsilon_count_zero`, `Epsilon_count_pos`
- `Nat.choose_one_right`, `Nat.factorial_succ`

## Hard constraints

- `lake build` green; current 2768 jobs.
- No new sorrys when delivered.
- Must call Write tool for `HANDOFF/outbox/task-labelset-atom-reply.md`.
- Two real attempts; if blocker, file the reply with detailed failure point.
