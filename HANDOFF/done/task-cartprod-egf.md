# Task — cartProd EGF identity (it does NOT match A.egf · B.egf)

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append at end of namespace)

**Goal:** Document the relationship between cartProd and EGF/labelProd. Specifically: cartProd is OGF-multiplicative but NOT EGF-multiplicative. Make this explicit with a deliberate non-identity.

```lean
/-- Note: `cartProd` is OGF-natural (cartProd_ogf gives mul) but its EGF is
    NOT the product of EGFs in general — that role belongs to `labelProd`.
    Concretely: `cartProd_count A B n = ∑ p A.count p.1 · B.count p.2`
    while `labelProdCount A B n = ∑ p (n choose p.1) · A.count p.1 · B.count p.2`.
    They differ by the binomial coefficient. -/
example (A B : CombinatorialClass) (n : ℕ) :
    (A.cartProd B).count n = ∑ p ∈ Finset.antidiagonal n, A.count p.1 * B.count p.2 :=
  cartProd_count A B n

example (A B : CombinatorialClass) (n : ℕ) :
    labelProdCount A B n = ∑ p ∈ Finset.antidiagonal n,
      n.choose p.1 * (A.count p.1 * B.count p.2) := rfl
```

These two examples document the algebraic distinction. No new theorem needed.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-cartprod-egf-reply.md
