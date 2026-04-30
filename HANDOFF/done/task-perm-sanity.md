# Task — permClass sanity checks (easy)

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Add `example` sanity checks for `permClass` at small sizes, demonstrating the framework computes correctly.

```lean
/-! Sanity checks: 0!=1, 1!=1, 2!=2, 3!=6, 4!=24. -/
example : permClass.count 0 = 1 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 1 = 1 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 2 = 2 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 3 = 6 := by rw [permClass_count_eq_factorial]; rfl
example : permClass.count 4 = 24 := by rw [permClass_count_eq_factorial]; rfl
```

Also add a sanity check for `singletonClass_labelProdCount_pow`:

```lean
example : CombinatorialClass.labelProdCount singletonClass singletonClass 3 = 8 :=
  singletonClass_labelProdCount_pow 3
example : CombinatorialClass.labelProdCount singletonClass singletonClass 5 = 32 :=
  singletonClass_labelProdCount_pow 5
```

These verify our framework actually evaluates correctly on concrete inputs.

## Hard constraints

- `lake build` green at the end. Currently 2764 jobs.
- If `rfl` doesn't close (Nat.factorial may not auto-reduce), use `decide` or `native_decide` or `norm_num`.

## Reply format

`HANDOFF/outbox/task-perm-sanity-reply.md` with diff summary + `Sonnet: idle — task done`.
