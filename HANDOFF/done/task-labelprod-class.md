# Task — Define `labelProd` as a `CombinatorialClass` (Obj-level)

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Construct the labelled product as a genuine `CombinatorialClass` (not just a count formula), and prove its `count` equals the existing `labelProdCount`.

## Context

Currently in this file we have:
- `labelProdCount A B n := ∑ p ∈ antidiag n, n.choose p.1 · A_p.1 · B_p.2` — abstract count formula.
- `labelProdCount_div_factorial_eq_coeff_mul_egf`: Theorem II.1 at the EGF level.

What's missing: an actual `CombinatorialClass` whose objects are "labelled pair (a, b)" so we can talk about `(A.labelProd B).level n`, prove associativity, define `seqClass_labelled`, etc.

## The Obj-level construction (F&S §II.2)

In F&S, the labelled product `A ⋆ B` consists of triples `(a, b, β)` where:
- `a : A.Obj`, `b : B.Obj`
- `β` is an "order-consistent relabelling" — equivalently, an ordered partition of `{1, ..., |a| + |b|}` into a "left block" of size `|a|` and a "right block" of size `|b|`.

A clean Lean encoding (one of several options):
```lean
def labelProd (A B : CombinatorialClass) : CombinatorialClass where
  Obj := Σ a : A.Obj, Σ b : B.Obj,
           { S : Finset (Fin (A.size a + B.size b)) // S.card = A.size a }
  size := fun ⟨a, b, _⟩ => A.size a + B.size b
  finite_level n := ...
```

For each `(a, b)` with `|a| + |b| = n`, the number of valid `S` is `n.choose |a|`. Summing over `(a, b)`:
```
(labelProd A B).count n = ∑ p ∈ antidiag n, n.choose p.1 · A.count p.1 · B.count p.2
                       = labelProdCount A B n
```

## Required theorems

1. `def labelProd : CombinatorialClass → CombinatorialClass → CombinatorialClass`
2. `theorem labelProd_count_eq_labelProdCount (A B) (n) : (A.labelProd B).count n = labelProdCount A B n`
3. (Bonus, if cheap) `(A.labelProd B).egf = A.egf * B.egf` — direct corollary via Theorem II.1.

## Hard constraints

- `lake build` green at the end. Currently 2764 jobs.
- No new sorrys. No `axiom`. No `True` placeholders.
- Two real attempts on the count theorem; if blocked, file `HANDOFF/outbox/task-labelprod-class-reply.md` documenting where exactly the bijection or finiteness breaks.
- The Obj type design is yours — pick whatever encoding makes the count proof tractable. Subset-with-card is one option; explicit injection is another (`(Fin (A.size a) ↪ Fin (A.size a + B.size b))`); a sigma-with-equiv is a third.

## Useful Mathlib

- `Finset.powersetCard n s : Finset (Finset α)` — subsets of fixed cardinality.
- `Fintype.card_filter_powersetCard`, `Nat.choose_eq_card_powersetCard` — `(Finset.univ : Finset (Fin n)).powersetCard k`'s card is `n.choose k`.
- `Finset.card_sigma`, `Finset.card_product`, `Finset.card_bij'`.
- For finite_level: `Set.toFinite` + `Set.Finite.subset`, modeled on the existing `permClass.finite_level` proof.

## Reply format

`HANDOFF/outbox/task-labelprod-class-reply.md` with diff summary + `Codex: idle — task done` (or blocker with the exact failing tactic/term).
