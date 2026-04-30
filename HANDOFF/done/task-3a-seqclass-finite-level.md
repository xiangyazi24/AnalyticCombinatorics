# Task 3a — `seqClass.finite_level` ONLY (split from task 3)

**File:** `AnalyticCombinatorics/PartA/Ch1/Sequences.lean:20`

This is the smaller half of task 3. Just prove `finite_level` for `seqClass`. Skip the OGF identity for now — that's deferred to task 3b.

## Required refactor

Change the def to take a hypothesis (option A from task 3):

```lean
def seqClass (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where
  Obj := List B.Obj
  size := fun xs => xs.foldr (fun b acc => B.size b + acc) 0
  finite_level n := by
    -- prove this
```

Then update `seqClass_ogf_eq`'s call site: it currently has `seqClass B`; change to `seqClass B h` (using its existing `h : B.count 0 = 0` hypothesis). Leave the **`sorry` in `seqClass_ogf_eq` body** — that's task 3b, not your problem.

## Recipe for `finite_level`

The set `{xs : List B.Obj | xs.foldr (fun b acc => B.size b + acc) 0 = n}` is finite when `B.count 0 = 0`.

Key insight: with `hB`, every element `b` of `B` has `B.size b ≥ 1`. So a list of total-size n has length `≤ n`. Hence:

```
{xs | size xs = n}  ⊆  ⋃_{ℓ = 0}^{n}  {xs | xs.length = ℓ ∧ size xs = n}
                    ⊆  ⋃_{ℓ = 0}^{n}  (List.replicate ℓ ?)
```

Better: bound the set by lists of length ≤ n with elements drawn from a finite cover.

Mathlib helpers likely useful:
- `Set.Finite.subset` — to bound by a known-finite set
- `List.finite_lengthLE` or `List.length_finite_of_finite` — lists of bounded length over a finite set are finite
- `Finset.list_le` / similar
- `Set.Finite.iUnion` over a `Finset` index

**Proof sketch:**

1. Fix n. Define `B_le_n := ⋃_{k ≤ n} B.level k` (finite, union of finitely-many finite sets).
2. Show every list xs with `size xs = n` has every element drawn from `B_le_n` (since each element's size is ≤ n, hence in some `B.level k` with k ≤ n).
3. Show such a list has length ≤ n (using `hB : B.count 0 = 0`, every element has size ≥ 1, so length ≤ total size = n).
4. Conclude xs is in `{xs : List B_le_n | xs.length ≤ n}`, which is finite (`List.finite_length_le`).

## Hard constraints

- **Stay under 50 lines of proof** for the `finite_level` body. If the proof keeps blowing up, file a blocker — DO NOT keep extending. Output budget is finite.
- Update the `seqClass B` reference in `seqClass_ogf_eq` to `seqClass B h` so the file still compiles (its body remains `sorry`, that's fine).
- No axiom escape, no `decide`, no replacing things with `True`.

## Acceptance

- `finite_level` is proven (no `sorry` on that field).
- `seqClass_ogf_eq` body still has `sorry` (deferred — task 3b).
- `lake build` returns 0 errors.
- Reply with diff summary in `HANDOFF/outbox/task-3a-seqclass-finite-level-reply.md`.
