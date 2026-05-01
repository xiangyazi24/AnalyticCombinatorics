# Task — labelSetCount boolClass = 2^n

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append at end)

**Goal:** Derive a beautiful corollary: the labelled SET of `boolClass` (binary alphabet) has count `2^n`. This is the labelled-SET analogue of `stringClass.count = 2^n`.

```lean
/-- (labelPow boolClass k).count n = 2^k · k! when n = k, else 0.
    A labelled k-tuple of binary atoms has 2^k label choices and k! orderings. -/
theorem labelPow_boolClass_count (k n : ℕ) :
    (CombinatorialClass.labelPow boolClass k).count n =
      if n = k then 2 ^ k * k.factorial else 0 := by
  sorry  -- Induction on k:
         --   k = 0: Epsilon, count is δ_{n, 0}, matches 2^0·0! = 1 at n = 0.
         --   k+1: labelProd boolClass (labelPow boolClass k).
         --     count(n+1) via labelProdCount (skipping k=0 since boolClass.count 0 = 0):
         --     = (n+1 choose 1) · 2 · (labelPow ... ).count n  (only boolClass.count 1 = 2 contributes)
         --     = (n+1) · 2 · (2^k · k!) when n = k
         --     = 2^{k+1} · (k+1)!  when n+1 = k+1.

/-- labelSetCount boolClass n = 2^n. -/
theorem labelSetCount_boolClass (n : ℕ) :
    CombinatorialClass.labelSetCount boolClass n = 2 ^ n := by
  sorry  -- ∑ k ≤ n, (labelPow boolClass k).count n / k!
         -- only k = n contributes: (2^n · n!) / n! = 2^n.
```

## Hard constraints

- Build green
- No new sorrys when delivered
- Reply at HANDOFF/outbox/task-labelset-bool-reply.md
- If the proof is hard, file blocker with where exactly the induction breaks
