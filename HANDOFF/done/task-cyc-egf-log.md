# Task — cyclicPermutationCount EGF = log(1/(1-X))

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

The labelled cyclic permutation count satisfies:

`(labelCycCount Atom n).cast / n! = 1/n` for `n ≥ 1`, and `0` for `n = 0`.

So the EGF is `∑_{n ≥ 1} z^n / n = -log(1 - z) = log(1/(1-z))`.

## Try to prove

State and prove a lemma like:

```lean
theorem labelCycCount_Atom_egf :
    (PowerSeries.mk fun n => (labelCycCount Atom n : ℚ) / n.factorial)
      = -PowerSeries.log (1 - PowerSeries.X) := by
  sorry
```

(Adjust to whatever EGF accessor / `log` API the codebase already uses; check Mathlib's `PowerSeries.log` or `Polynomial.log` definitions.)

If Mathlib's `PowerSeries.log` has the right power-series shape, this should reduce to coefficient-wise equality: coefficient of `X^n` on the left is `1/n` (for `n ≥ 1`); on the right, `PowerSeries.log` of `1 - X` is `-∑_{n≥1} X^n / n`.

## Hard constraints

- Build green.
- No new sorrys when delivered (or document a clean blocker).
- Reply at HANDOFF/outbox/task-cyc-egf-log-reply.md.
- If Mathlib's `PowerSeries.log` doesn't match the convention or the proof needs heavy machinery, **fall back** to: prove `coeff n (egf) = 1/n` for `n ≥ 1` and `= 0` for `n = 0`, leave the `log` connection as a TODO.
- Do NOT introduce new `axiom`s. Stop and document if it gets that bad.
