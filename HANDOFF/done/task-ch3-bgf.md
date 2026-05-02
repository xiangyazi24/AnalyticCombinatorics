# Task: Chapter III — Bivariate Generating Functions and Parameters

## Goal

Extend `AnalyticCombinatorics/PartA/Ch3/Parameters.lean` with bivariate generating function theory from F&S Chapter III.

## What to formalize

Chapter III introduces a *parameter* χ on class A and the bivariate GF:

```
A(z, u) = Σ_{n,k} a_{n,k} z^n u^k
```

where `a_{n,k}` = number of objects of size n with parameter value k.

Key results:

### 1. Bivariate GF definition (already have `jointCount`)

Add:
```lean
/-- The bivariate generating function: A(z,u) = Σ_{n,k} jointCount(n,k) · z^n · u^k.
    Modeled as a power series in z whose coefficients are polynomials in u. -/
noncomputable def bgf (A : CombinatorialClass) (χ : Parameter A) :
    PowerSeries (Polynomial ℕ) := ...
```

### 2. Marginal at u=1 recovers the OGF

```lean
theorem bgf_eval_one (A : CombinatorialClass) (χ : Parameter A) :
    (A.bgf χ).map (Polynomial.eval 1) = A.ogf.map (algebraMap ℕ ℕ)
```

(evaluating u=1 sums over all parameter values, recovering size-only counts)

### 3. Mean value via derivative

The average value of χ over objects of size n:
```lean
noncomputable def meanParam (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) : ℚ :=
  if A.count n = 0 then 0
  else (∑ k ∈ (A.level n).image χ, k * A.jointCount χ n k : ℚ) / A.count n
```

### 4. Cumulated cost = Σ k · a_{n,k}

```lean
noncomputable def cumulatedCost (A : CombinatorialClass) (χ : Parameter A) (n : ℕ) : ℕ :=
  ∑ k ∈ (A.level n).image χ, k * A.jointCount χ n k
```

### 5. Sanity: permutations with fixed-point parameter

Using `permClass` and `permClass.numFixedPoints` from LabelledClass.lean:
- jointCount 2 0 = 1 (the transposition (12))
- jointCount 2 2 = 1 (the identity)
- cumulatedCost 3 = 0·2 + 1·3 + 3·0 = 3 (total fixed points across all 6 perms of {1,2,3})

Actually: for n=3, perms are: id (3 fp), (12)(3) (1 fp), (13)(2) (1 fp), (23)(1) (1 fp), (123) (0 fp), (132) (0 fp).
So jointCount 3 0 = 2, jointCount 3 1 = 3, jointCount 3 3 = 1.
cumulatedCost 3 = 0*2 + 1*3 + 3*1 = 6. Mean = 6/6 = 1.

Verify with native_decide for small n.

## Imports

```lean
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
```

## Constraints

- No sorry, no axiom
- `lake build AnalyticCombinatorics.PartA.Ch3.Parameters` must pass
- Extend the existing file (don't overwrite the 33 lines already there — add below them)

## Output

Report what definitions and theorems you added.
