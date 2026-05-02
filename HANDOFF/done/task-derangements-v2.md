# Task: Derangements (v2, simplified)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/Derangements.lean`.

## Approach

Keep it simple. Define derangement count recursively, prove basic properties, use native_decide for sanity.

```lean
def derangeCount : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (n + 2) => (n + 1) * (derangeCount (n + 1) + derangeCount n)
```

## Required theorems

1. `derangeCount` definition as above
2. Sanity: derangeCount 0 = 1, 1 = 0, 2 = 1, 3 = 2, 4 = 9, 5 = 44 (via native_decide)
3. The recursion formula as a standalone theorem
4. `perm_eq_set_star_derange`: `n! = Σ_{k=0}^{n} C(n,k) * derangeCount(n-k)` — prove via native_decide for n=0..8

Do NOT attempt:
- inclusion-exclusion formula (integer cast issues are hard)
- EGF coefficient theorem (rational arithmetic is fiddly)
- Any theorem involving ℚ division

Just stick to ℕ/native_decide-verifiable content.

## Key constraint

**The file MUST compile with `lake build AnalyticCombinatorics.PartA.Ch2.Derangements` before you write the reply.** Delete any theorem that doesn't compile.

No sorry, no axiom.

## Output

Write file, verify build, report.
