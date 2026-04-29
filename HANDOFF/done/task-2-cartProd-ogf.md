# Task 2 — `cartProd_ogf`

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean:129`

```lean
theorem cartProd_ogf : (A.cartProd B).ogf = A.ogf * B.ogf := by sorry
```

**Pick this up only after task 1 is done and merged.** I'll move task 1 to `HANDOFF/done/` and ping you.

## Already in scope

- `coeff_ogf : coeff n A.ogf = A.count n` (line 38).
- `level_mem_iff` (private, line 56).
- `disjSum_ogf` (you just proved it).
- `cartProd.Obj = A.Obj × B.Obj`, `cartProd.size ⟨a,b⟩ = A.size a + B.size b` (line 113–126).

## Recipe sketch — Cauchy convolution

Goal after `ext n`, `coeff_ogf`, `coeff_mul`, `coeff_ogf`, `coeff_ogf`:

```
(A.cartProd B).count n = ∑ p ∈ Finset.Nat.antidiagonal n, A.count p.1 * B.count p.2
```

Strategy: build a Finset bijection between `(A.cartProd B).level n` and the disjoint union (`Σ` / sigma) over `(k, n-k)` of `A.level k ×ˢ B.level (n-k)`. Then:

```
((A.cartProd B).level n).card
  = ∑ k ∈ Finset.range (n+1), (A.level k).card * (B.level (n - k)).card
  = ∑ p ∈ Finset.Nat.antidiagonal n, A.count p.1 * B.count p.2
```

Mathlib lemmas likely useful:
- `PowerSeries.coeff_mul` — gives the antidiagonal sum.
- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` — switch between range and antidiagonal forms.
- `Finset.card_product` — `(s ×ˢ t).card = s.card * t.card`.
- `Finset.card_biUnion` (disjoint version) — sum of cards over a disjoint family.

If you find a cleaner angle (e.g. `PowerSeries.coeff_mul_of_finite`), use it.

## Acceptance

- File compiles, this `sorry` is gone, no new sorrys introduced.
- `lake build` returns 0 errors. Sorry warnings on other sites are fine.
- Reply with diff summary in `HANDOFF/outbox/task-2-cartProd-ogf-reply.md`.

## Hard constraints

- Same as task 1 — no axiom escape, no editing scaffold definitions.
- Two failed attempts → blocker.
