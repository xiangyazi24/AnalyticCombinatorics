# Task — Tribonacci recurrence as a real theorem

**File:** `AnalyticCombinatorics/Examples/Tribonacci.lean` (append)

The file builds `tribClass` (compositions of `n` into parts in `{1, 2, 3}`) and verifies sanity values. Add the **recurrence** as a real theorem:

```lean
theorem tribClass_count_recurrence (n : ℕ) :
    tribClass.count (n + 3) = tribClass.count (n + 2) + tribClass.count (n + 1) + tribClass.count n := by
  sorry
```

## Suggested approach

The recurrence drops out of the OGF identity already in the file. Specifically, `tribClass.ogfZ * (1 - X - X^2 - X^3) = 1` implies the coefficient relation: for `n ≥ 3`, `coeff (X^n) tribClass.ogfZ = coeff(n-1) + coeff(n-2) + coeff(n-3)`.

Routes:

(A) Coefficient comparison from the OGF identity (preferred).
(B) Combinatorial: split a composition of `n+3` by its first part (1, 2, or 3) → bijection with three smaller-composition classes. (More work.)

Pick whichever lands. (A) should be a few lines if the existing OGF infrastructure exposes coefficient extraction cleanly.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-trib-recurrence-reply.md.
- If the OGF coefficient-extraction route turns out to be heavier than expected (because `ogfZ` uses `ℚ` and `count` is `ℕ`, so coefficient comparison passes through `ℚ`), still try — the cast should be routine.
- Do NOT introduce axioms. Document blocker if needed.
