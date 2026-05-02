# Task: Strings and Regular Languages — Part A Ch I §3

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/StringsTheory.lean` formalizing the OGF theory of strings over a finite alphabet.

## What to formalize

F&S Chapter I §3: Strings over alphabet of size k.

### Key results:

1. **k-letter alphabet as a CombinatorialClass:**
   ```lean
   def alphabetClass (k : ℕ) : CombinatorialClass where
     Obj := Fin k
     size _ := 1
   ```
   Count: `alphabetClass.count 1 = k`, count n = 0 for n ≠ 1.

2. **Strings = SEQ(alphabet):** The class of strings over k letters is `seqClass (alphabetClass k) _`.
   - OGF satisfies `(1 - kz) · S(z) = 1`
   - count n = k^n (prove this!)

3. **Theorem: string count equals k^n:**
   ```lean
   theorem stringCount_eq_pow (k : ℕ) (hk : 0 < k) (n : ℕ) :
       (seqClass (alphabetClass k) _).count n = k ^ n
   ```

4. **Strings avoiding a pattern (transfer matrix method):**
   For the simplest case: strings over {0,1} avoiding "11" (no two consecutive ones).
   - Count = Fibonacci(n+2)
   - Prove: `stringsNoConsecOnes_count n = fib (n + 2)`

5. **OGF of strings avoiding "11":**
   - OGF = 1/(1 - z - z²) — the golden ratio OGF
   - Alternatively prove the recursion: count(n+2) = count(n+1) + count(n)

6. **Sanity checks:**
   - Binary strings: count 0 = 1, count 1 = 2, count 2 = 4, count 3 = 8
   - Ternary strings: count 0 = 1, count 1 = 3, count 2 = 9
   - No-11 strings: count 0 = 1, count 1 = 2, count 2 = 3, count 3 = 5, count 4 = 8

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Fib.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Sequences
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.StringsTheory` must pass
- The key theorem `stringCount_eq_pow` should be proved by induction using `seqClass.count_succ`.
- For the no-11 case, define the restricted class directly (as lists of Fin 2 with the constraint) rather than using the transfer matrix.

## Output

Write the complete file and report what you proved.
