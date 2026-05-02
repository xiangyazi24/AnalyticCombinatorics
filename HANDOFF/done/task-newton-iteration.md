# Task: Newton's Method for Power Series — Part A Ch I Appendix

## Goal

Create file `AnalyticCombinatorics/PartA/Ch1/Newton.lean` formalizing Newton's iteration for bootstrapping power series solutions from functional equations.

## What to formalize

F&S Theorem I.6 (Newton's iteration): If T(z) satisfies a functional equation F(T,z) = 0, then T can be computed iteratively by doubling precision at each step.

### Focus: the quadratic method for Catalan

The simplest and most important case: the equation `T = 1 + z·T²` has a unique power series solution (the Catalan OGF). Newton's iteration doubles the number of correct coefficients at each step.

### Required:

1. **Power series truncation:**
   ```lean
   noncomputable def trunc (f : PowerSeries ℕ) (n : ℕ) : PowerSeries ℕ :=
     PowerSeries.mk fun k => if k < n then coeff k f else 0
   ```

2. **Agreement up to order n:**
   ```lean
   def agreeUpTo (f g : PowerSeries ℕ) (n : ℕ) : Prop :=
     ∀ k < n, coeff k f = coeff k g
   ```

3. **Newton step for T = 1 + z·T²:**
   The iteration: T_{k+1} = T_k - (T_k - 1 - z·T_k²) / (1 - 2z·T_k)
   Simplified (since we know the fixed point structure): T_{k+1} extracts the next batch of coefficients.

   Actually, simpler to prove: **the bootstrapping lemma**:
   ```lean
   theorem catalan_bootstrap (f : PowerSeries ℕ) (n : ℕ)
       (hagree : agreeUpTo f binaryTreeClass.ogf n)
       (hfunc : agreeUpTo f (1 + X * f ^ 2) (2 * n)) :
       agreeUpTo f binaryTreeClass.ogf (2 * n)
   ```

4. **Explicit first few iterates:**
   - T_0 = 1
   - T_1 = 1 + z (agrees to order 2)
   - T_2 = 1 + z + 2z² + ... (agrees to order 4)

   Verify these with `native_decide` or explicit coefficient comparison.

5. **Uniqueness of power series root:**
   ```lean
   theorem catalan_ogf_unique (f : PowerSeries ℕ) (hf : f = 1 + X * f ^ 2)
       (h0 : coeff 0 f = 1) : f = binaryTreeClass.ogf
   ```

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch1.Trees
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch1.Newton` must pass
- The uniqueness theorem is the most important result — it shows the functional equation characterizes the OGF.
- If the full bootstrapping lemma is too hard, focus on uniqueness + explicit coefficient verification for the first few iterates.

## Output

Write the complete file and report what you proved.
