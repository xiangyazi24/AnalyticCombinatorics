# Task — Narayana numbers via labelled product

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append) or new file.

**Goal:** Add Narayana numbers connection if Mathlib has them; otherwise file a small note about Catalan / Narayana relation.

Narayana number N(n, k) = (1/n) C(n, k) C(n, k-1) for 1 ≤ k ≤ n. Sum over k of N(n,k) = catalan n.

```lean
-- If Mathlib has Nat.narayana or stirlingFirst, connect; else skip.
```

If Mathlib doesn't have Narayana directly, file blocker; the task is exploratory.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-narayana-reply.md
