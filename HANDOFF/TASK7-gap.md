# TASK #7 gap: `KhatRes` occupation is not the normalized `Umat` occupation

This is a new blocker, distinct from the TASK6 soft-tail-vs-hard-increment issue.  The truncation route
can address the support/tail hypothesis for the free conditioned residual kernel, but it does not by
itself identify that kernel's occupation with the conditioned unmatched mass consumed by
`CoalesceBridge`.

## Exact point of failure

The current coupling definitions are in `AnalyticCombinatorics/Ch8/Partitions/ITERCoupling.lean`:

- `Kres` is substochastic:
  `Kres x y a b = KhatRes x y a b * (1 - cmass x y)` on rows with `cmass x y < 1`.
- `Umat` evolves by `Kres`, not by `KhatRes`:
  ```lean
  Umat (t + 1) a b = ∑ x, ∑ y, Umat t x y * Kres x y a b
  ```
- `umass t = ∑ x, ∑ y, Umat t x y`.

Therefore the normalized surviving distribution
```lean
Û_t(x,y) = Umat t x y / umass t
```
does not generally satisfy the homogeneous Markov recursion
```lean
Û_{t+1}(a,b) = ∑ x, ∑ y, Û_t(x,y) * KhatRes x y a b.
```
The actual algebra is the Feynman-Kac / survival-tilted recursion
```lean
Û_{t+1}(a,b)
  = (umass t / umass (t+1)) *
      ∑ x, ∑ y, Û_t(x,y) * (1 - cmass x y) * KhatRes x y a b
```
when the denominators are nonzero.

Equivalently, paths are weighted by the product of survival factors
`∏s (1 - cmass X_s)`.  This biases the surviving law away from high-coalescence states.  Thus the free
occupation
```lean
∑ t < M, ∑ z, distPow KhatRes (pairDelta i j) t z * 1_{GoodHi z}
```
is not the same sequence as
```lean
g t =
  (∑ x, ∑ y, if GoodHi x y then Umat t x y else 0) / umass t
```
required by `CoalesceBridge.lean`.

## Why this blocks the requested assembly

`GoodHiRecursion.lean` and `CoalesceBridge.lean` require unbounded cumulative occupation of the
survival-conditioned unmatched mass fraction `g`.  The planned theorem in `/tmp/hr_spec7.md` and
`HANDOFF/TASK6-gap.md` proves occupation for `distPow KhatRes`.  Without an additional theorem
transferring free `KhatRes` occupation to the survival-tilted `Û_t` occupation, the input to
`umass_lt_of_occupation_unbounded` is not available.

This is independent of the soft-tail obstruction: even if a truncated kernel `Kb` proves hard bounded
increments and transfers back to the free `KhatRes` kernel, the survival tilt remains.

## Minimal missing theorem

One of the following is needed:

1. A proof that the survival-tilted process `Û_t` itself has unbounded `GoodHi` occupation, carrying the
   survival factors through the localized Tanaka/Paley-Zygmund argument.
2. A comparison theorem bounding the survival-tilted `GoodHi` occupation from below by the free
   `KhatRes` (or truncated `Kb`) occupation up to a negligible error.
3. A different coalescence bridge that consumes free `KhatRes` occupation directly without requiring
   `g = goodMass / umass`.

Without one of these, identifying `distPow KhatRes` with the `CoalesceBridge` input would silently assume
the false homogeneous normalized-`Umat` recursion.
