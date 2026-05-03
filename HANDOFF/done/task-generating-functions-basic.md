# Task: Basic Generating Function Theory (Ch I core)

## Goal

Create `AnalyticCombinatorics/PartA/Ch1/GeneratingFunctions.lean`.

## What to formalize

Core OGF/EGF connection theorems as coefficient-level verifications.

1. **OGF coefficient extraction:**
   ```lean
   def ogfCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ := a n
   ```
   
   For the all-ones sequence: ogfCoeff (fun _ => 1) = geometric series 1/(1-z).
   Partial sums: Σ_{k=0}^n 1 = n + 1. Verify for n=0..10.

2. **EGF coefficient extraction:**
   ```lean
   def egfCoeff (a : ℕ → ℕ) (n : ℕ) : ℚ := (a n : ℚ) / (Nat.factorial n : ℚ)
   ```
   
   For a_n = n! (permutations): egfCoeff (fun n => n.factorial) n = 1 for all n.
   Verify for n=0..8.

3. **Binomial transform:**
   ```lean
   def binomialTransform (a : ℕ → ℕ) (n : ℕ) : ℕ :=
     ∑ k ∈ Finset.range (n + 1), Nat.choose n k * a k
   ```
   
   Transform of (1,0,0,...) = (1,1,1,...) [binomial row sums].
   Transform of (1,1,1,...) = (1,2,4,8,...) = 2^n.
   Verify: binomialTransform (fun _ => 1) n = 2^n for n=0..8.

4. **Euler transform (connected → total):**
   ```lean
   def eulerTransformCount : ℕ → ℕ → ℕ
   ```
   If c_n = 1 for all n≥1 (one connected structure of each size):
   Total = partition function p(n).
   Verify first 8 values match.

5. **Exponential formula check:**
   If connected structures have EGF C(z), total = exp(C(z)).
   For C(z) = z (one connected structure of size 1):
   exp(z) has [z^n/n!] = 1, so total labeled structures = 1 for all n.
   
   For C(z) = z + z^2/2 (connected = single edge):
   Verify first few coefficients of exp(z + z^2/2).

## Imports

```lean
import Mathlib.Tactic
```

## Constraints

- Must compile: `lake build AnalyticCombinatorics.PartA.Ch1.GeneratingFunctions`
- No sorry, no axiom
- Delete anything that doesn't compile
- native_decide for all checks
- **Must wrap all definitions in `namespace GeneratingFunctions`** and close with `end GeneratingFunctions`

## Output

Write file, verify build, report.
