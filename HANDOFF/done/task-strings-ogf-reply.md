# Strings OGF reply

Created `AnalyticCombinatorics/PartA/Ch1/StringsTheory.lean`.

Proved:

- `alphabetClass (k : ℕ)` with objects `Fin k`, all of size 1.
- `(alphabetClass k).count 1 = k`.
- `(alphabetClass k).count n = 0` for `n ≠ 1`.
- `stringsClass k = seqClass (alphabetClass k) ...`.
- `stringCount_eq_pow (k : ℕ) (_hk : 0 < k) (n : ℕ) :
  (seqClass (alphabetClass k) (alphabetClass.count_zero k)).count n = k ^ n`,
  using induction and `seqClass.count_succ`.
- `stringsClass_count_eq_pow (k n : ℕ) : (stringsClass k).count n = k ^ n`.
- OGF identity for strings:
  `(1 - C k * X) * ogfZ (stringsClass k) = 1`.
- `stringsNoConsecOnesClass`, defined directly as length-indexed `List.Vector (Fin 2)` words satisfying `noConsecOnes`.
- Fibonacci recurrence:
  `stringsNoConsecOnesClass.count (n + 2) =
   stringsNoConsecOnesClass.count (n + 1) + stringsNoConsecOnesClass.count n`.
- Fibonacci count:
  `stringsNoConsecOnes_count n :
   stringsNoConsecOnesClass.count n = Nat.fib (n + 2)`.
- Correct OGF identity for the no-11 class:
  `ogfZ stringsNoConsecOnesClass * (1 - X - X^2) = 1 + X`.
  This is the identity compatible with the requested count `fib(n+2)` and sanity checks `1,2,3,5,8`; `1/(1 - z - z^2)` would have coefficients `fib(n+1)`.
- Binary, ternary, and no-11 sanity checks.

Verified:

```bash
lake build AnalyticCombinatorics.PartA.Ch1.StringsTheory
```

passes.
