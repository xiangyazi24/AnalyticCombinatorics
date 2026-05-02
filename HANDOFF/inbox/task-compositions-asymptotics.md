# Task: Compositions Asymptotics (Ch V / rational)

## Goal

Create `AnalyticCombinatorics/PartB/Ch5/CompositionsAsymptotics.lean`.

## What to formalize

From F&S Chapter V: Compositions are sequences of positive integers summing to n. Their GF is rational: `1/(1 - z/(1-z)) = (1-z)/(1-2z)`, giving 2^{n-1} compositions of n.

1. **compositionCount (n : ℕ) : ℕ** — number of compositions of n (into positive parts)
   - compositionCount 0 = 1
   - compositionCount (n+1) = 2^n
   - Verify for n=0..10 via native_decide

2. **Compositions with parts in a restricted set S:**
   - `restrictedCompCount (S : Finset ℕ) (n : ℕ) : ℕ`
   - For S = {1,2}: Fibonacci! restrictedCompCount {1,2} n = Nat.fib (n+1)
   - Verify for n=0..10

3. **Number of parts in a composition:**
   - Average number of parts in a composition of n is (n+1)/2
   - Total parts across all compositions of n:
   - Verify: `totalParts n * 2 = (n + 1) * 2^n` for n=1..8 (Euler-style calculation)
   - Use multiplied integer form.

4. **Growth rate:**
   - compositionCount is exponential with rate 2
   - Verify: compositionCount n < 2^n for n≥1 (since 2^{n-1} < 2^n)
   - Verify: compositionCount n > 0 for all n

## Imports

```lean
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartB.Ch5.CompositionsAsymptotics`
- No sorry, no axiom
- native_decide for all verifications
- Create directory if needed: `AnalyticCombinatorics/PartB/Ch5/`

## Output

Write file, verify build, report.
