# Task: Rational Generating Functions (Part B Ch4)

## Goal

Create `AnalyticCombinatorics/PartB/Ch4/RationalGF.lean` with basics of rational generating functions and their coefficient asymptotics.

## What to formalize

From F&S Chapter IV: A rational GF f(z) = P(z)/Q(z) with deg P < deg Q has coefficients determined by partial fractions. In particular:

- `1/(1-az)` has coefficients `a^n`
- `1/(1-az)^k` has coefficients `C(n+k-1,k-1) * a^n`

### Required:

1. Define and verify geometric series coefficients:
   ```lean
   theorem geom_coeff (a : ℕ) (n : ℕ) :
       coeff n (PowerSeries.invOneMinusXPow a 1) = a ^ n
   ```
   
   Or simpler: just verify for `PowerSeries.mk (fun n => a ^ n)` that it satisfies the right functional equation.

2. **Linear recurrence characterization:** Define
   ```lean
   def isLinearRecurrence (seq : ℕ → ℕ) (coeffs : List ℕ) : Prop :=
       ∀ n ≥ coeffs.length,
         seq n = ∑ i ∈ Finset.range coeffs.length,
           coeffs[i]! * seq (n - 1 - i)
   ```

3. Verify Fibonacci satisfies `isLinearRecurrence Nat.fib [1, 1]` for n ≤ 20 via native_decide.

4. **Companion matrix approach** (optional, skip if hard): characteristic polynomial connection.

5. Simple dominance: for sequences with `seq n ≤ C * r^n`, verify growth bound for small cases.

Keep this file lightweight — just definitions + native_decide sanity. No complex algebra proofs.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch4.RationalGF`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on definitions that compile + native_decide checks

## Output

Write file, verify build, report.
