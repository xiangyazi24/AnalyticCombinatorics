# Task: Combinatorial Identities (Ch I/III)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/CombinatorialIdentities.lean`.

## What to formalize

Classic binomial coefficient identities that appear throughout F&S as tools.

1. **Vandermonde's identity:**
   C(m+n, r) = Σ_{k=0}^{r} C(m,k) * C(n, r-k)
   
   Mathlib has this as `Nat.add_choose_eq`. Verify it numerically for
   specific values:
   - C(5+3, 4) = Σ C(5,k)*C(3,4-k) for k=0..4
   - Verify: C(8,4) = 70 = C(5,1)*C(3,3) + C(5,2)*C(3,2) + C(5,3)*C(3,1) + C(5,4)*C(3,0)
     = 5*1 + 10*3 + 10*3 + 5*1 = 5 + 30 + 30 + 5 = 70 ✓

2. **Hockey-stick identity:**
   Σ_{i=r}^{n} C(i,r) = C(n+1, r+1)
   
   Verify for (n,r) = (5,2): C(2,2)+C(3,2)+C(4,2)+C(5,2) = 1+3+6+10 = 20 = C(6,3) ✓

3. **Chu-Vandermonde (at integer values):**
   For the identity C(n, k) = C(n-1, k-1) + C(n-1, k), this is Pascal's rule.
   Verify via native_decide for n,k up to 8.

4. **Binomial sum identities:**
   - Σ_{k=0}^{n} C(n,k) = 2^n  (verify for n=0..10)
   - Σ_{k=0}^{n} (-1)^k * C(n,k) = 0 for n ≥ 1 (use integers, verify n=1..10)
   - Σ_{k=0}^{n} C(n,k)^2 = C(2n, n) (verify for n=0..8)
   - Σ_{k=0}^{n} k * C(n,k) = n * 2^(n-1) (verify for n=1..8)

5. **Double counting identities:**
   - C(2n, 2) = 2 * C(n, 2) + n^2 (verify n=1..8)
   - Σ_{k=1}^{n} k^2 = n*(n+1)*(2*n+1)/6 (verify n=1..10)

6. **Catalan number identities (cross-reference):**
   - C(n) = C(2n,n)/(n+1) (verify n=0..10 against catalan from Mathlib or direct def)
   - Σ_{k=0}^{n} C(k)*C(n-k) = C(n+1) (convolution, verify n=0..8)

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.CombinatorialIdentities`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all numerical checks
- For signed identities (alternating sums), use ℤ not ℕ
- Keep it to verifications; don't try to prove identities in full generality unless Mathlib makes it trivial (e.g., a one-liner `simp [Nat.choose_succ_succ]`)

## Output

Write file, verify build, report.
