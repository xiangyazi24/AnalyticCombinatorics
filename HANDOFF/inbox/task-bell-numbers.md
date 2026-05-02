# Task: Bell Numbers

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/BellNumbers.lean` formalizing Bell numbers (set partitions count).

## What to formalize

Bell number B(n) = number of partitions of {1,...,n} into non-empty subsets.
- B(0)=1, B(1)=1, B(2)=2, B(3)=5, B(4)=15, B(5)=52, B(6)=203
- Recursion: B(n+1) = Σ_{k=0}^{n} C(n,k) * B(k)
- EGF: exp(e^z - 1)

### Required:

1. Define `bellCount : ℕ → ℕ` via the recursion:
   ```lean
   def bellCount : ℕ → ℕ
     | 0 => 1
     | n + 1 => ∑ k ∈ Finset.range (n + 1), Nat.choose n k * bellCount k
   ```

2. State the recursion as a theorem.

3. Sanity checks via native_decide:
   - bellCount 0 = 1
   - bellCount 1 = 1
   - bellCount 2 = 2
   - bellCount 3 = 5
   - bellCount 4 = 15
   - bellCount 5 = 52
   - bellCount 6 = 203

4. **Stirling connection:** Define `stirling2 (n k : ℕ) : ℕ` (Stirling numbers of the second kind) via recursion:
   ```lean
   def stirling2 : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | _ + 1, 0 => 0
     | n + 1, k + 1 => stirling2 n k + (k + 1) * stirling2 n (k + 1)
   ```

5. Verify `bellCount n = ∑ k ∈ Finset.range (n + 1), stirling2 n k` for n=0..6.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.BellNumbers`
- No sorry, no axiom
- Delete anything that doesn't compile
- Pure ℕ arithmetic, no ℚ, no PowerSeries needed

## Output

Write file, verify build, report.
