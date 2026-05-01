# Task — Derangement EGF closed form

**File:** `AnalyticCombinatorics/Examples/Derangements.lean` (append)

The classical closed form: `D(z) = exp(-z) / (1 - z)`. The file already proves:
- `derangementClass_egf_mul_exp_eq_permClass_egf` (i.e. `D(z) · exp(z) = 1/(1-z)`)
- `one_sub_X_mul_derangementClass_egf` (i.e. `(1-z) · D(z) = exp(-z)` or similar)

Try to expose the **explicit closed form**:

```lean
theorem derangementClass_egf_eq_exp_neg_div_one_sub :
    derangementClass.egf * (1 - PowerSeries.X) = PowerSeries.exp ℚ - PowerSeries.X * PowerSeries.exp ℚ := by
  sorry
```

Or whatever exact statement matches the existing API. The clean form might use `PowerSeries.eval (-X) (PowerSeries.exp ℚ)` or `PowerSeries.exp ℚ.subst (-X)` if those APIs exist.

If a clean closed form is awkward to state, just **rephrase** the existing two facts as a single combined identity (e.g. `D(z) · exp(z) · (1-z) = 1` or similar) and ship.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-derange-egf-closed-reply.md.
- If the negation/composition API isn't there, document what's missing and ship the cleanest available form.
- Do NOT introduce axioms.
