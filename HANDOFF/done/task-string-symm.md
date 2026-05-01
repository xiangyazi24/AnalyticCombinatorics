# Task — Pascal symmetry for stringNumTrue

**File:** `AnalyticCombinatorics/Examples/Strings.lean` (append)

The bivariate count `stringClass.jointCount stringNumTrue n k` should equal `Nat.choose n k`. The Pascal-row sanity values already match.

## Try one of:

(A) **Symmetry**: prove `stringClass.jointCount stringNumTrue n k = stringClass.jointCount stringNumTrue n (n - k)` for `k ≤ n`. (Bijection: complement each bit.)

(B) **Closed form**: prove `stringClass.jointCount stringNumTrue n k = Nat.choose n k` for `k ≤ n` (and `0` otherwise).

Either is meaningful F&S content. (B) is more useful long-term but harder; (A) is a single bijection. Pick whichever you can land cleanly. If both are stubborn, do at least the symmetry sanity at small `n` (e.g. `n = 5, 6, 7`) as `decide`/`native_decide` examples without proving the general lemma.

## Hard constraints

- Build green.
- No new sorrys.
- Reply at HANDOFF/outbox/task-string-symm-reply.md.
- Document which option (A/B/sanity) you took and why.
- If the bijection is too painful, fall back to per-`n` sanity. Don't paper over.
