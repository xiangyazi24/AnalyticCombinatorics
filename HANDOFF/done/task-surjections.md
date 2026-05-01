# Task — Surjections example file

**File:** `AnalyticCombinatorics/Examples/Surjections.lean` (NEW)

A "surjection" of size `n` is a labelled object: a surjective function from `Fin n` onto its image. Equivalently, it's an ordered set partition of `[n]` (= a sequence of disjoint nonempty blocks whose union is `[n]`). The count is `Fubini(n) = ∑_{k} k! · S(n,k)` (the Fubini / ordered-Bell numbers, OEIS A000670: `1, 1, 3, 13, 75, 541, 4683, ...`).

We already have:
- `labelSeq_posIntClass_count_eq_fubini` — count of `labelSeq posIntClass` equals Fubini.
- `posIntClass_egf_eq_exp_sub_one`
- `labelSeq_posIntClass_egf_mul_two_sub_exp = 1`

These already capture the EGF identity. What's missing is **a class explicitly named "surjections"** that exposes this content as an `Examples/` entry.

## What to build

1. `surjectionClass : CombinatorialClass` defined as `labelSeq posIntClass _h0` (where `_h0 : posIntClass.count 0 = 0` already exists in the file). This is just an alias.
2. `surjectionClass_count_eq_fubini (n) : surjectionClass.count n = Nat.fubini n` — restate via the existing labelSeq lemma. (If `Nat.fubini` doesn't exist in Mathlib, look for whatever name the existing lemma uses; possibly `fubini` is defined locally.)
3. Sanity examples for `n = 0..6` matching `1, 1, 3, 13, 75, 541, 4683`. Use `decide`/`native_decide`.
4. Add to `AnalyticCombinatorics.lean` import list.

## Hard constraints

- Build green.
- No new sorrys.
- Read `Examples/SetPartitions.lean` first to find the exact `fubini` connection name.
- Reply at HANDOFF/outbox/task-surjections-reply.md.
- This file should mostly be a re-export — don't duplicate proofs.
