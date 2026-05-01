# Task — Motzkin recurrence

**File:** `AnalyticCombinatorics/Examples/MotzkinTrees.lean` (append)

The Motzkin recurrence: `M(n+2) = M(n+1) + ∑_{k=0}^{n} M(k) · M(n-k)`. Or equivalently the OGF satisfies `M(z) = 1 + z M(z) + z² M(z)²`.

Try one of the following:

(A) Find Mathlib's `Nat.motzkinNumber` (if it exists) and expose its recurrence.

(B) Prove the recurrence directly on the existing `motzClass.count` from this file:

```lean
theorem motzClass_count_recurrence (n : ℕ) :
    motzClass.count (n + 2) = motzClass.count (n + 1) +
      ∑ k ∈ Finset.range (n + 1), motzClass.count k * motzClass.count (n - k) := by
  sorry
```

(For our `MotzTree` size convention with leaf=0, see what the recurrence shape should be by running small cases. If our convention is `leaf` size 0, then `count(0)=1, count(1)=1, count(2)=2, count(3)=4, count(4)=9, count(5)=21`. Verify the recurrence shape with one numerical check before proving.)

(C) If both are stubborn, document the blocker.

Note: the Mathlib `Nat.motzkinNumber` may not exist. If not, only attempt (B) if the file's existing count_succ structure makes the bijection clean.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-motzkin-rec-reply.md.
- Document which option (A/B/blocker) you took.
- Do NOT introduce axioms.
