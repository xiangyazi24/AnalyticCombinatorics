# Task: Words Avoiding Patterns (Ch V / applications)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/WordPatterns.lean`.

## What to formalize

Words over {0,1} avoiding certain patterns, with transfer to linear recurrences.

1. **Words avoiding "000" (no three consecutive zeros):**
   - `noTripleZeroCount : ℕ → ℕ` — binary words of length n with no "000"
   - Recursion: a(n) = a(n-1) + a(n-2) + a(n-3) (tribonacci-like with different init)
   - a(0) = 1, a(1) = 2, a(2) = 4
   - a(3) = 7, a(4) = 13, a(5) = 24, a(6) = 44

2. **Words avoiding "01" (non-decreasing binary words):**
   - `noZeroOneCount : ℕ → ℕ` = n + 1 (all-zeros up to position k, then all-ones)
   - Verify for n = 0..10

3. **Words avoiding "010":**
   - `noZeroOneZeroCount : ℕ → ℕ`
   - Recursion from automaton: more complex
   - Values: 1, 2, 4, 7, 11, 16, 22, ... (n(n+1)/2 + 1? No...)
   - Actually: 2^0=1, 2^1=2, 2^2=4, then 7, 12, 20, 33...
   
   Skip this if recursion is unclear. Focus on (1) and (2).

4. **Connection to Fibonacci:** Words avoiding "11" = Fibonacci (already in StringsTheory). Cross-reference.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.WordPatterns`
- No sorry, no axiom
- Delete anything that doesn't compile
- Focus on (1) and (2), skip (3) if unclear
- native_decide for all verification

## Output

Write file, verify build, report.
