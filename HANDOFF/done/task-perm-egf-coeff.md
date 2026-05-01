# Task — permClass EGF and OGF coefficient forms

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append)

**Goal:** Direct OGF/EGF coefficient identities for permClass.

```lean
example (n : ℕ) :
    permClass.egf.coeff n = 1 := permClass_egf_coeff n

example (n : ℕ) :
    permClass.ogf.coeff n = (n.factorial : ℕ) := by
  rw [coeff_ogf, permClass_count_eq_factorial]
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-perm-egf-coeff-reply.md
