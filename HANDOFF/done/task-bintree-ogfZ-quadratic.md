# Task — BinTree OGF quadratic over ℤ

**File:** `AnalyticCombinatorics/Examples/BinaryTrees.lean` (append)

**Goal:** Lift the existing `ogf_functional_equation` to ℤ[[z]] via `ogfZ` and prove the quadratic identity.

```lean
/-- Lift the functional equation to ℤ[[z]] via ogfZ. -/
theorem ogfZ_functional_equation :
    ogfZ asClass = 1 + PowerSeries.X * (ogfZ asClass) ^ 2 := by
  unfold CombinatorialClass.ogfZ
  have := congrArg (PowerSeries.map (algebraMap ℕ ℤ)) ogf_functional_equation
  simpa [PowerSeries.map_X] using this

/-- Quadratic form: X · C² - C + 1 = 0 in ℤ[[z]]. -/
theorem ogfZ_quadratic :
    PowerSeries.X * (ogfZ asClass) ^ 2 - ogfZ asClass + 1 = 0 := by
  have h := ogfZ_functional_equation
  linear_combination -h
```

If `simpa [PowerSeries.map_X]` doesn't quite work, the `map_one`, `map_mul`, `map_pow` rewrites are the path.

`linear_combination` is in `Mathlib.Tactic.LinearCombination`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-bintree-ogfZ-quadratic-reply.md
