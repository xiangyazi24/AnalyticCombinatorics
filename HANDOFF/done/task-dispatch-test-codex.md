# Task — Dispatch test (codex side)

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append at end of namespace)

**Goal:** Add a small structural identity to verify the new non-interactive dispatch pipeline works end-to-end. This is a one-line proof.

```lean
/-- The OGF of `Atom + Atom` is `2 · X`. Two atoms of size 1, OGF doubles. -/
theorem Atom_disjSum_Atom_ogf : (Atom.disjSum Atom).ogf = 2 * PowerSeries.X := by
  rw [disjSum_ogf, Atom_ogf, two_mul]
```

If `two_mul` doesn't quite normalize — e.g. you may need `← two_mul`, or
`ring_nf` instead — adapt as needed. One short proof.

## Acceptance

- `lake build` green; current 2768 jobs.
- The reply file at `HANDOFF/outbox/task-dispatch-test-codex-reply.md` lands on disk.

This task primarily validates that `codex exec --full-auto` ends with a real Write call, not a phantom one.
