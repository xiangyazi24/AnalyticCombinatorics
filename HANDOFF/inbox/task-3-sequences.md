# Task 3 — `seqClass.finite_level` + `seqClass_ogf_eq`

**File:** `AnalyticCombinatorics/PartA/Ch1/Sequences.lean:20` and `:30`

**Pick this up only after tasks 1 and 2 are merged.**

```lean
def seqClass (B : CombinatorialClass) : CombinatorialClass where
  Obj := List B.Obj
  size := fun xs => xs.foldr (fun b acc => B.size b + acc) 0
  finite_level n := by
    sorry -- finite level sets: bounded-length sequences with bounded total size

theorem seqClass_ogf_eq (B : CombinatorialClass) (h : B.count 0 = 0) :
    (1 - ogfZ B) * ogfZ (seqClass B) = 1 := by
  sorry
```

## Subtask 3a — `finite_level`

Sequences of total size n: each element of B contributes ≥ 0 to the size. The set of lists xs : List B.Obj with `foldr (fun b acc => B.size b + acc) 0 xs = n` is finite.

**Caveat:** if `B.count 0 ≠ 0` (i.e. B has objects of size 0), then sequences can be arbitrarily long — finite_level FAILS. Decide:

- Option A: add hypothesis `(h : B.count 0 = 0)` to `seqClass` itself. Cleaner but breaks the `seqClass B` API.
- Option B: prove finite_level only when B has no size-0 objects, otherwise use a placeholder. **Don't take this — it leaves a quiet wrong claim in the codebase.**
- Option C: refactor `seqClass` to be `partial` or carry the hypothesis as a field. Likely the right move.

**Default to option A.** Refactor:

```lean
def seqClass (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where ...
```

and update `seqClass_ogf_eq`'s argument to match (it already takes `h`).

If you prefer a different design, file a blocker before changing.

## Subtask 3b — `seqClass_ogf_eq`

After `ext n`, this reduces to a coefficient identity in `PowerSeries ℤ`. The key recursion:

```
(seqClass B)(z) = 1 + B(z) · (seqClass B)(z)
```

Why: a sequence is empty (1 of size 0) or `head :: tail` where `head ∈ B` and `tail ∈ seqClass B`. Coefficient-wise this is `(seqClass B).count n = δ_{n,0} + ∑_{k=1}^{n} B.count k · (seqClass B).count (n-k)`.

Rearrange: `(seqClass B)(z) - B(z)·(seqClass B)(z) = 1`, i.e. `(1 - B(z))·(seqClass B)(z) = 1`. ← target.

Likely you need a coefficient-level helper:
```lean
lemma seqClass_count_succ (n : ℕ) :
    (seqClass B).count (n + 1) = ∑ k ∈ Finset.range (n + 2), B.count k * (seqClass B).count (n + 1 - k)
```
(Plus the n=0 base.) Building this requires bijecting List B.Obj of size n+1 with `(b, tail)` where `b ∈ B, |tail| = (n+1) - |b|`, and the empty list when n+1 = 0 (vacuous).

This task is bigger than 1+2. **If after one real attempt at 3a or 3b you're stuck, file a blocker** and I'll either refactor the scaffold or take it over. Don't loop.

## Acceptance

- Both sorrys gone, file compiles, build green.
- Reply with diff summary.

## Hard constraints

Same as before — no axiom escape, no editing core scaffold.
