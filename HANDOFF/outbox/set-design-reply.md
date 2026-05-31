# Labelled SET design verdict

## 1. Model

Verdict: the model is essentially right, but write the dependent decoration over the
subtype of parts, not as a two-argument membership function.

Recommended shape:

```lean
noncomputable def CombClass.set (C : CombClass) : CombClass where
  Obj n := Σ π : Finpartition (Finset.univ : Finset (Fin n)),
    (B : π.parts) → C.Obj B.1.card
  finObj _ := by classical infer_instance
```

This is faithful to the repository's skeletonized labelled-class convention. A
`C`-structure on a label block `B` is represented by an element of `C.Obj B.card`,
just as `LabelledProduct.lean` represents an `A`-structure on a chosen `k`-subset by
`A.Obj k`, not by a species functor on that exact finite set.

No double counting: `Finpartition` stores unordered, nonempty, disjoint blocks
covering `univ`; `π.parts` is a `Finset`, so each block occurs exactly once; the
decoration function is indexed by the subtype `B : π.parts`, so there is no ordering
of blocks to quotient out.

Fintype is fine. At the pinned mathlib rev, `Finpartition s` has a `Fintype`
instance for finsets, and finite dependent products over `π.parts` infer from
`C.finObj`.

Avoid this shape:

```lean
Π B in π.parts, C.Obj B.card
```

It is not conceptually wrong, since `Finset (Fin n)` is finite, but it expands to
functions over all candidate subsets plus membership proofs. `Fintype.card_pi`
then sees many outside-of-`π.parts` trivial factors, and proof irrelevance/membership
arguments add avoidable noise. The subtype version gives the intended product
directly:

```lean
Fintype.card ((B : π.parts) → C.Obj B.1.card)
  = ∏ B : π.parts, C.counts B.1.card
```

Then rewrite to `∏ B in π.parts, C.counts B.card` with the usual attach/subtype
product lemmas.

The hypothesis `C.counts 0 = 0` is still necessary for the combinatorial
construction `SET(C)` as arbitrary finite sets of components. `Finpartition` itself
has no empty blocks, so if `C₀ ≠ 0` this model silently omits zero-size components
instead of representing the infinite zero-size SET behavior. For `C₀ = 0`, this is
exactly the intended finite labelled SET. For `n = 0`, the unique empty partition
and empty dependent product give one object, matching the constant term of
`exp(C(z))`.

Counts layer should be immediate:

```lean
lemma CombClass.counts_set (C : CombClass) (n : ℕ) :
    C.set.counts n =
      ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
        ∏ B : π.parts, C.counts B.1.card := by
  classical
  change Fintype.card
    (Σ π : Finpartition (Finset.univ : Finset (Fin n)),
      (B : π.parts) → C.Obj B.1.card) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.card_pi]
  rfl
```

## 2. R1 vs R2

Strong recommendation: if forced to choose, use R1, not R2. But do not make either
one the main proof spine if the differential route is acceptable.

R2 is the heaviest route. With `PowerSeries.coeff_subst'`, the RHS reduces to

```lean
finsum k, coeff k (PowerSeries.exp ℚ) • coeff n (C.egf ^ k)
```

and then `coeff_pow` expands into ordered weak compositions of `n`. To identify
this with

```lean
(1 / n!) * ∑ π, ∏ B ∈ π.parts, C.counts B.card
```

you must prove the labelled exponential formula / Bell polynomial identity:
unordered decorated set partitions are ordered block decompositions divided by
`k!`, with the multinomial factor `n! / ∏ |B|!`. Mathlib's
`Combinatorics.Enumerative.Bell` is numerical and even says the set-partition
counting theorem is TODO; it does not provide the EGF exponential formula. So R2
means building the genuine Bell-polynomial machinery from scratch.

R1 isolates the same mathematics more cleanly:

1. define fixed-cardinality `SET_[k](C)` as decorated `Finpartition`s with
   `π.parts.card = k`;
2. relate ordered `k`-block decompositions to the `k`-fold labelled product using
   the existing `egf_lprod` theorem by induction;
3. prove unordered = ordered / `k!` by exhibiting the `Fin k ≃ π.parts` choices.

This still requires a serious ordered/unordered-block lemma, but that lemma is
reusable and local. R2 buries the same quotient inside coefficient algebra,
factorials, multinomials, `finsuppAntidiag`, and `coeff_pow`.

## 3. Single hardest sub-problem

Hardest sub-problem: not the `Fintype` model, and not `PowerSeries.exp`; it is the
Lean bridge between an unordered `Finpartition` object and an ordered/pointed
decomposition of labels.

If using the differential route, the key lemma is the pointed-block recurrence:

```lean
(C.set.counts (n + 1) : ℚ)
  = ∑ k : Fin (n + 1),
      (Nat.choose n k : ℚ) * C.counts (k + 1) * C.set.counts (n - k)
```

equivalently, coefficientwise,

```lean
d⁄dX ℚ C.set.egf = d⁄dX ℚ C.egf * C.set.egf
```

Tactic-level strategy:

1. Define an auxiliary object over an arbitrary finite label set:

   ```lean
   def SetObjOn (C : CombClass) {α} [DecidableEq α] (s : Finset α) :=
     Σ π : Finpartition s, (B : π.parts) → C.Obj B.1.card
   ```

2. Prove transport invariance:

   ```lean
   Fintype.card (SetObjOn C s) = C.set.counts s.card
   ```

   Use an equivalence between `s` and `Fin s.card`, map finsets through the induced
   finset order isomorphism, and use `Finpartition.map`. This keeps all block-card
   equalities behind the transport lemma.

3. For a decorated partition of `univ : Finset (Fin (n+1))`, take the distinguished
   label `0`. Use `π.part 0` for the block containing it, and `π.avoid (π.part 0)`
   or an equivalent `ofExistsUnique` construction for the remaining partition.
   The chosen block is `insert 0 S`, where `S` is a `k`-subset of the other `n`
   labels. The remaining labels have cardinality `n - k`.

4. Build the inverse by extending a partition of the complement with the new block.
   The useful mathlib names here are `Finpartition.part`, `part_mem`,
   `mem_part_self`, `avoid`, `mem_avoid`, `ofExistsUnique`, `biUnion_parts`,
   `existsUnique_mem`, and `sum_card_parts`.

5. Once the bijection is in place, the count proof should be routine:
   `Fintype.card_sigma`, `Fintype.card_prod`, `Fintype.card_finset_len`, and the
   transport-invariance lemma for the complement SET object.

This is smaller than proving the full Bell-polynomial coefficient identity, but it
is still the place where most Lean time will go.

## 4. Final recommendation

Do the counts layer first. It is cheap, validates the model, and gives a useful
theorem independent of the eventual EGF proof.

For the EGF layer, use `PowerSeries.subst C.egf (PowerSeries.exp ℚ)` as the formal
meaning of `exp(C(z))`, but prove equality by the differential equation, not by
expanding coefficients of `subst`.

Spine:

1. from `C.counts 0 = 0`, prove `PowerSeries.constantCoeff C.egf = 0`;
2. get `PowerSeries.HasSubst C.egf` from
   `PowerSeries.HasSubst.of_constantCoeff_zero'`;
3. prove the recurrence/pointing theorem:

   ```lean
   d⁄dX ℚ C.set.egf = d⁄dX ℚ C.egf * C.set.egf
   ```

4. prove the RHS satisfies the same equation using existing API:

   ```lean
   PowerSeries.derivative_subst hsubst
   PowerSeries.derivative_exp
   PowerSeries.subst_mul hsubst
   ```

   giving

   ```lean
   d⁄dX ℚ ((PowerSeries.exp ℚ).subst C.egf)
     = d⁄dX ℚ C.egf * (PowerSeries.exp ℚ).subst C.egf
   ```

   up to commutativity.

5. prove uniqueness of solutions to `F' = C' * F` with fixed constant term by
   coefficient induction on the difference. This is short over `ℚ`: if
   `H' = C' * H` and `constantCoeff H = 0`, then coefficient `n+1` is forced by
   coefficients `≤ n`, already zero.

This avoids `PowerSeries.log`, avoids a global `tsum_k C^k/k!` theorem, and avoids
building Bell polynomials. It still states the result as `SET(C)(z) = exp(C(z))`
via substitution, which is the right formal target in current Mathlib.
