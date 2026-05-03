# Task: Alternating Permutations and Tangent/Secant Numbers (Ch II)

## Goal

Create `AnalyticCombinatorics/PartA/Ch2/AlternatingPerms.lean`.

## What to formalize

Alternating permutations (zigzag permutations) have EGF = sec(z) + tan(z).
The counts E_n are the tangent numbers (odd n) and secant numbers (even n).

1. **Zigzag number sequence:**
   ```lean
   def zigzagNumber : ℕ → ℕ
     | 0 => 1
     | n + 1 => (∑ k ∈ Finset.range (n + 1), 
                   Nat.choose n k * zigzagNumber k * zigzagNumber (n - k)) / 2
   ```
   Wait — the standard recursion is:
   E(n+1) = (1/2) * Σ_{k=0}^{n} C(n,k) * E(k) * E(n-k)
   
   But division by 2 is problematic. Better: use the boustrophedon triangle.
   
   **Boustrophedon/Euler triangle:**
   T(0,0) = 1
   T(n,0) = T(n-1, n-1)  for n ≥ 1
   T(n,k) = T(n,k-1) + T(n-1, n-1-k)  for k ≥ 1
   
   Then E(n) = T(n, n).

   ```lean
   def boustrophedon : ℕ → ℕ → ℕ
     | 0, 0 => 1
     | 0, _ + 1 => 0
     | n + 1, 0 => boustrophedon n n
     | n + 1, k + 1 => boustrophedon (n + 1) k + boustrophedon n (n - (k + 1))
   ```
   Note: need care with subtraction. Define T(n,k) = 0 for k > n.
   
   Then `zigzagNumber n = boustrophedon n n`.

2. **Sanity checks (native_decide):**
   - E(0) = 1, E(1) = 1, E(2) = 1, E(3) = 2, E(4) = 5, E(5) = 16, E(6) = 61, E(7) = 272
   - Tangent numbers: E(1) = 1, E(3) = 2, E(5) = 16, E(7) = 272
   - Secant numbers: E(0) = 1, E(2) = 1, E(4) = 5, E(6) = 61

3. **Row sums of boustrophedon triangle:**
   Σ_{k=0}^{n} T(n,k) = E(n+1) (verify for n=0..5)
   Actually: T(n,n) = E(n). Just verify diagonal values.

4. **Connection to Euler numbers:**
   The Euler numbers (with sign) satisfy |E_{2n}| = secant number.
   Just verify secantNumber n = zigzagNumber (2*n) for n=0..4.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch2.AlternatingPerms`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- Be careful with the boustrophedon recursion: handle k > n case (return 0)
- The recursion must terminate — think about termination measure (n is primary, k secondary)

## Output

Write file, verify build, report.
