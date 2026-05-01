# Task — string · string disjSum count = 2 · 2^n

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

**Goal:** Apply `disjSum_count` and `cartProd_count` to stringClass.

```lean
/-- The disjoint sum of two stringClasses doubles the count: 2 · 2^n = 2^(n+1). -/
example (n : ℕ) :
    (stringClass.disjSum stringClass).count n = 2 ^ (n + 1) := by
  rw [CombinatorialClass.disjSum_count, stringClass_count_eq_pow]
  rw [pow_succ]
  ring

/-- The cartesian product convolution: ∑ p ∈ antidiag n, 2^p.1 · 2^p.2 = (n+1) · 2^n. -/
theorem stringClass_cartProd_count (n : ℕ) :
    (stringClass.cartProd stringClass).count n = (n + 1) * 2 ^ n := by
  rw [CombinatorialClass.cartProd_count]
  -- ∑ p ∈ antidiag n, 2^p.1 · 2^p.2 = ∑ p, 2^(p.1+p.2) = ∑ p, 2^n = (n+1) · 2^n
  rw [show ∑ p ∈ Finset.antidiagonal n, stringClass.count p.1 * stringClass.count p.2
        = ∑ p ∈ Finset.antidiagonal n, 2 ^ n from ?_]
  · simp [Finset.sum_const, Finset.Nat.card_antidiagonal]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [stringClass_count_eq_pow, stringClass_count_eq_pow]
    rw [← pow_add, hp]
```

Adapt as needed for `Finset.Nat.card_antidiagonal` (might be a different name).

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-string-disjsum-reply.md
