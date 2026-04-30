# Task 3a Reply — `seqClass.finite_level` DONE

**Status:** done — `finite_level` proved, `lake build` green (2697 jobs, 0 errors).

## Changes made

**File:** `AnalyticCombinatorics/PartA/Ch1/Sequences.lean`

1. **Option A applied:** `seqClass` now takes `(hB : B.count 0 = 0)` as a parameter.

2. **`finite_level` sorry replaced** with a ~45-line proof.

3. **`seqClass_ogf_eq` updated:** call site changed from `seqClass B` to `seqClass B h`.
   Body still has `sorry` (task 3b, deferred).

## Proof sketch for `finite_level`

Four helpers, then the main bound:

1. **`mem_level`** — inline replacement for private `level_mem_iff`:
   `x ∈ B.level m ↔ B.size x = m` via `Set.Finite.mem_toFinset`.

2. **`hpos`** — `hB : B.count 0 = 0` rules out size-0 objects, so `∀ b, 1 ≤ B.size b`.

3. **`hlen_bound`** — by induction: `ys.length ≤ ys.foldr (B.size + ·) 0`
   (each element contributes ≥ 1).

4. **`helem_le`** — by induction: for `b ∈ ys`, `B.size b ≤ ys.foldr ... 0`
   (individual sizes cannot exceed the total).

5. **Cover:** `S : Set B.Obj := ⋃ k : Fin (n+1), ↑(B.level k.val)` is finite
   by `Set.finite_iUnion` + `Finset.finite_toSet`.

6. **Main:** `{xs | size xs = n} ⊆ List.map Subtype.val '' {xs : List ↑S | xs.length ≤ n}`.
   Lift `xs` to `xs.attachWith (· ∈ S) _` using `List.attachWith_map_subtype_val`.
   Finiteness from `List.finite_length_le` (needs `[Finite ↑S]` from `hSfin.to_subtype`).

## Blockers encountered (and resolved)

- `level_mem_iff` is `private` in `CombinatorialClass` — worked around via `change` +
  `Set.Finite.mem_toFinset` inline.
- `Finset.biUnion` needs `DecidableEq B.Obj` — avoided by using `Set.finite_iUnion`
  with `Fin (n+1)` index instead.
- `simp only [Set.mem_setOf_eq] at hxs` was "no progress" (Lean already simplified the
  hypothesis on intro) — removed, used `have hxs' := hxs` instead.
