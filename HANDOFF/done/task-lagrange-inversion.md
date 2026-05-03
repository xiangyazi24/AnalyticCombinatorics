# Task: Lagrange Inversion (Ch I/VII)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/LagrangeInversion.lean`.

## What to formalize

Lagrange inversion: if T(z) = z * φ(T(z)), then [z^n] T(z) = (1/n) * [w^{n-1}] φ(w)^n.
For binary trees: T = z(1+T)^2, so φ(w) = (1+w)^2, giving C_n = (1/(n+1)) * C(2n,n).

1. **Lagrange coefficient formula (verification):**
   For φ(w) = (1+w)^2 (binary trees):
   `lagrangeCoeff (n : ℕ) : ℕ := (2*n).choose n / (n + 1)`
   
   This should equal the Catalan number. Verify for n=0..10.

2. **For φ(w) = 1 + w + w^2 (Motzkin trees):**
   `motzkinLagrangeCoeff (n : ℕ) : ℕ` — compute [w^{n-1}] (1+w+w^2)^n / n
   
   Actually this is complex. Use the simpler:
   
3. **Counting rooted trees via Lagrange (Cayley):**
   T = z * e^T in EGF, so φ(w) = e^w.
   [z^n/n!] T = n^{n-1} / n! → labeled rooted trees on n = n^{n-1}.
   
   Just verify: `cayleyRootedCount (n : ℕ) : ℕ := if n = 0 then 1 else n ^ (n - 1)`
   Values: 1, 1, 2, 9, 64, 625, 7776, ...

4. **Verify catalan = lagrangeCoeff for n=0..12:**
   ```lean
   example : lagrangeCoeff 5 = 42 := by native_decide
   ```

5. **Generalized Catalan (Fuss-Catalan):**
   `fussCatalan (p n : ℕ) : ℕ := (p*n+1).choose n / (p*n+1) * (p*n+1) ... `
   
   Actually: fussCatalan p n = C(pn, n) / (pn + 1) ... but division.
   Use: `fussCatalan (p n : ℕ) : ℕ := if p*n+1 = 0 then 0 else ((p*n).choose n) / (p*n / n + 1)`
   
   Hmm this is messy. Simpler:
   `fussCatalan (p n : ℕ) : ℕ := ((p*n+1).choose n) / (p*n + 1)` ... still division.
   
   Better: use the equivalent `fussCatalan p n = C(pn,n) * 1/(pn+1)`:
   The formula is: C_{p,n} = (1/(pn+1)) * C(pn+1, n) = C(pn, n) / (pn+1) * (pn+1-n+1)...
   
   Actually: Fuss-Catalan = C(pn+1, n) / (pn+1). This is always integer.
   ```lean
   def fussCatalan (p n : ℕ) : ℕ := (p * n + 1).choose n / (p * n + 1)
   ```
   Hmm wait: C(pn+1, n) / (pn+1) — is this always integer? Yes!
   
   Actually the standard Fuss-Catalan is: (1/(pn+1)) * C((p+1)n, n).
   For p=1: (1/(n+1)) * C(2n, n) = Catalan.
   For p=2: (1/(2n+1)) * C(3n, n) — ternary trees.
   
   ```lean
   def fussCatalan (p n : ℕ) : ℕ :=
     if (p + 1) * n = 0 then 1
     else ((p + 1) * n).choose n / ((p + 1) * n + 1)... 
   ```
   
   This is getting complicated. Just use:
   ```lean
   def fussCatalan (p n : ℕ) : ℕ :=
     if n = 0 then 1 else Nat.choose (p * n + p) n / (p * n + 1)
   ```
   Wait: for p=1, n=3: C(6,3)/4 = 20/4 = 5. Catalan(3) = 5. ✓
   For p=2, n=2: C(6,2)/5 = 15/5 = 3.
   For p=2, n=3: C(9,3)/7 = 84/7 = 12.
   
   Verify Fuss-Catalan for p=1 matches Catalan, p=2 gives ternary tree counts.

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.LagrangeInversion`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- Keep it focused on coefficient verification, not the full analytic theorem
- **Must wrap all definitions in `namespace LagrangeInversion`** and close with `end LagrangeInversion`

## Output

Write file, verify build, report.
