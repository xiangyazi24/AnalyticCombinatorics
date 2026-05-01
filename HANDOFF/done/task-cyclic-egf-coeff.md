# Task — cyclic permutation EGF coeff form

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append)

**Goal:** Direct EGF coefficient identity.

```lean
example (n : ℕ) (hn : 1 ≤ n) :
    labelCycCount Atom n / (n.factorial : ℚ) = 1 / (n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [labelCycCount_Atom_succ, Nat.factorial_succ]
  push_cast
  field_simp
```

If a similar example already exists from earlier task-cyclic-perm-cycles, just verify or append a related variant. Otherwise file blocker.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-cyclic-egf-coeff-reply.md
