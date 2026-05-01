# Task — Strings OGF closed form

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append at end)

**Goal:** Prove `stringClass.ogfZ · (1 - 2 X) = 1` over ℤ[[z]] — analogue of compositions, but for strings.

```lean
theorem stringClass_ogfZ_mul_one_sub_two_X :
    ogfZ stringClass * (1 - 2 * PowerSeries.X) = 1 := by
  sorry  -- coefficient comparison: stringClass.count n = 2^n
         -- pattern from compositionClass_ogfZ_mul_one_sub_two_X but cleaner because
         -- count is 2^n for all n (no n=0 vs n+1 split)
```

## Strategy

Coefficient comparison at n. Use `stringClass_count_eq_pow` (already have it).

```
coeff n (stringClass.ogfZ · (1 - 2X)) = coeff n (1)
  ↔ stringClass.count n − 2 · stringClass.count (n−1) = δ_{n,0}
  ↔ 2^n − 2 · 2^{n−1} = δ_{n,0}  (for n ≥ 1, both sides are 0; for n = 0, LHS = 1 - 0 = 1)
```

For n = 0: stringClass.count 0 = 1. coeff 0 of (1 - 2X) = 1. So coeff 0 (LHS) = 1 · 1 = 1.
For n ≥ 1: coeff n via Cauchy product = stringClass.count n · 1 + stringClass.count (n−1) · (−2) = 2^n − 2·2^(n−1) = 0. ✓

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-strings-ogf-reply.md
