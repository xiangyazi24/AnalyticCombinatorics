# Task — Labelled SEQ class and EGF geometric-series identity

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Define the labelled sequence construction `labelSeq B` (lists of labelled B-objects) and prove its EGF satisfies `(1 - B.egf) · labelSeq.egf = 1` when `B.count 0 = 0`.

This is the labelled analogue of `seqClass` (which is OGF-natural). EGF identity:
```
labelSeq(B)(z) = 1 + B(z) + B(z)² + ⋯ = 1 / (1 - B(z))
```
provided `B(z)` has no constant term.

## Required code

```lean
/-- Labelled sequence construction. Objects are sequences of B-objects with
    a labelling on the merged atoms. Equivalent to a sigma over k of `labelPow B k`. -/
noncomputable def labelSeq (B : CombinatorialClass) (hB : B.count 0 = 0) : CombinatorialClass where
  Obj := Σ k : ℕ, (labelPow B k).Obj
  size := fun ⟨k, x⟩ => (labelPow B k).size x
  finite_level n := by
    -- Only k ∈ Finset.range (n+1) contributes since each labelPow term has size ≥ k (when B has no size-0 element).
    -- Bound the level set by ⋃ k : Fin (n+1), (labelPow B k).level n.
    sorry

namespace labelSeq

/-- Count of labelSeq is the sum of labelPow counts. -/
theorem count_eq (B : CombinatorialClass) (hB : B.count 0 = 0) (n : ℕ) :
    (labelSeq B hB).count n = ∑ k ∈ Finset.range (n + 1), (labelPow B k).count n := by
  sorry  -- bijection: level n of labelSeq = disjoint union over k ≤ n of labelPow B k . level n

end labelSeq

/-- The EGF of labelSeq satisfies `(1 - B.egf) * labelSeq.egf = 1` over ℚ. -/
theorem labelSeq_egf_mul_one_sub_egf (B : CombinatorialClass) (hB : B.count 0 = 0) :
    (1 - B.egf) * (labelSeq B hB).egf = 1 := by
  sorry  -- coefficient comparison + finite geometric series identity
```

## Recipe for `labelSeq.finite_level`

Since `B.count 0 = 0`, every B-object has size ≥ 1. Therefore each element of `labelPow B k` has size ≥ k. So `labelPow B k . level n = ∅` for k > n.

Thus the sigma at level n is `⋃ k ≤ n, (labelPow B k).level n`. Bound by `Set.finite_iUnion` over `Fin (n+1)`.

## Recipe for `count_eq`

Bijection between `(labelSeq B hB).level n` and `(Finset.range (n+1)).sigma (fun k => (labelPow B k).level n)`. Use `Finset.card_bij'` with forward `⟨k, x⟩ ↦ ⟨k, x⟩` and backward by re-packaging.

Care: when k > n, `(labelPow B k).level n = ∅`, so terms vanish naturally.

## Recipe for `labelSeq_egf_mul_one_sub_egf`

Coefficient comparison at `n`. RHS: `[zⁿ] 1 = δ_{n,0}`. LHS coefficient: 

```
coeff n ((1 - B.egf) * labelSeq.egf)
  = ∑_{p+q=n} coeff p (1 - B.egf) · coeff q labelSeq.egf
```

Substituting `coeff q labelSeq.egf = (labelSeq.count q : ℚ) / q! = ∑_{k≤q} ((labelPow B k).count q / q!)
 = ∑_{k≤q} coeff q (B.egf^k)`:

```
= coeff n labelSeq.egf - ∑_{p+q=n, p≥1} coeff p B.egf · coeff q labelSeq.egf
```

Use the identity `B.egf · labelSeq.egf = labelSeq.egf - 1` (which is the EGF version of "appending one more block to a labelled sequence").

Actually a cleaner approach: prove first `B.egf * labelSeq.egf = labelSeq.egf - 1` (over ℚ, using the recursion `labelSeq B = Epsilon ⊕ labelProd B (labelSeq B)`), then rearrange.

The recursion at the count level: `labelSeq.count n = δ_{n,0} + labelProdCount B labelSeq n`. This follows from how labelPow decomposes: labelPow B 0 = Epsilon, labelPow B (k+1) = labelProd B (labelPow B k).

## Hard constraints

- `lake build` green; current 2764 jobs.
- No new sorrys (main deliverables = no sorry; proof-internal `sorry` only as scratch).
- Two real attempts on each theorem; if blocked file `HANDOFF/outbox/task-labelseq-reply.md` documenting the exact failure.
- Skip `labelSeq.finite_level` to a `sorry` only if you can't finish — but try to land it.

## Reply format

`HANDOFF/outbox/task-labelseq-reply.md` with diff summary + `Codex: idle — task done`.
