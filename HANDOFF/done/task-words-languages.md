# Task: Words and Regular Languages (Ch I)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/WordsLanguages.lean`.

## What to formalize

Counting words and regular language connections from Chapter I.

1. **Words over alphabet of size r:**
   Total words of length n = r^n.
   ```lean
   def wordCount (r n : ℕ) : ℕ := r ^ n
   ```
   Verify: wordCount 2 5 = 32, wordCount 3 4 = 81, wordCount 26 2 = 676

2. **Binary strings avoiding pattern "11":**
   These are counted by Fibonacci: a(n) = fib(n+2).
   ```lean
   def noConsecOnes (n : ℕ) : ℕ := Nat.fib (n + 2)
   ```
   Verify: noConsecOnes 0 = 1, noConsecOnes 1 = 2, noConsecOnes 2 = 3,
   noConsecOnes 3 = 5, noConsecOnes 4 = 8, noConsecOnes 5 = 13

3. **Dyck words (balanced parentheses):**
   Number of Dyck words of semilength n = Catalan(n).
   ```lean
   def dyckWordCount (n : ℕ) : ℕ := Nat.choose (2*n) n / (n + 1)
   ```
   Verify values match Catalan for n=0..10.

4. **Smirnov words (no adjacent equal letters):**
   On r-letter alphabet: s(n) = r * (r-1)^(n-1) for n≥1, s(0) = 1.
   ```lean
   def smirnovCount (r n : ℕ) : ℕ :=
     if n = 0 then 1 else r * (r - 1) ^ (n - 1)
   ```
   Verify: smirnovCount 2 n gives 1, 2, 2, 2, 2, ... (binary alternating)
   smirnovCount 3 n gives 1, 3, 6, 12, 24, 48, ... (3*2^(n-1))

5. **De Bruijn sequences:**
   Number of distinct de Bruijn sequences B(r,n) = (r!)^{r^{n-1}} / r^n.
   For r=2, n=2: B(2,2) = (2!)^{2^1} / 2^2 = 4/4 = 1? No, it's more complex.
   
   Simpler: just count de Bruijn sequence LENGTH = r^n (they exist!).
   And verify the number of binary strings of length n containing all patterns of length k:
   For k=2, binary: need "00","01","10","11" as substrings → min length = 5 (e.g., "00110").
   
   Actually just verify:
   ```lean
   -- Number of distinct necklaces on binary alphabet of length n (divides 2^n by n, corrected)
   -- Already in Necklaces.lean. Skip this.
   ```
   
   Replace with: **Run-length encoding count:**
   A word of length n on r letters with exactly k runs:
   ```lean
   def runLengthCount (r n k : ℕ) : ℕ :=
     if k = 0 then (if n = 0 then 1 else 0)
     else r * (r - 1)^(k - 1) * Nat.choose (n - 1) (k - 1)
   ```
   Verify: binary (r=2), n=4: runLengthCount 2 4 1 = 2, runLengthCount 2 4 2 = 6,
   runLengthCount 2 4 3 = 6, runLengthCount 2 4 4 = 2. Sum = 16 = 2^4.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.WordsLanguages`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace WordsLanguages`** and close with `end WordsLanguages`

## Output

Write file, verify build, report.
