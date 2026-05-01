# Task — Tetranacci and Padovan recurrence theorems

Two appendings, both following the same pattern just landed in `Examples/Tribonacci.lean` (`tribClass_count_recurrence`):

## File 1: `AnalyticCombinatorics/Examples/Tetranacci.lean` (append)

```lean
theorem tetraClass_count_recurrence (n : ℕ) :
    tetraClass.count (n + 4)
      = tetraClass.count (n + 3) + tetraClass.count (n + 2)
        + tetraClass.count (n + 1) + tetraClass.count n := by
  sorry
```

## File 2: `AnalyticCombinatorics/Examples/Padovan.lean` (append)

```lean
theorem padovanClass_count_recurrence (n : ℕ) :
    padovanClass.count (n + 3) = padovanClass.count (n + 1) + padovanClass.count n := by
  sorry
```

## Suggested approach

Mirror what `tribClass_count_recurrence` did (just landed in commit `1fe1add`). Read that lemma's proof for the pattern.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-tetra-padovan-rec-reply.md.
- Do both files in this single dispatch.
- Don't introduce axioms; document a blocker if either route fails.
