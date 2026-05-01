# Task — sum of cycle counts over all sizes

**File:** `AnalyticCombinatorics/Examples/CyclicPermutations.lean` (append at end)

**Goal:** Add `n!` connection: ∑ (over `cycle types of n`) of cycle structures = n! (since every perm has unique cycle decomposition).

This is essentially a check that "Atom labelled SET via labelled CYC" sum integrals to n! when summed over all permutation cycle structures.

```lean
/-- The Atom labelled SET equals 1, the Atom labelled CYC at n equals (n-1)!,
    and these connect via the standard exp(log(...)) relation but we don't formalize
    exp/log composition here.

    A simpler concrete identity: the EGF of permutation cycles equals
    log(1/(1-z)). The EGF coefficient at n is 1/n: that's labelCycCount Atom n / n! =
    (n-1)! / n! = 1/n. -/
example (n : ℕ) (hn : 1 ≤ n) :
    labelCycCount Atom n / (n.factorial : ℚ) = 1 / (n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [labelCycCount_Atom_succ]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
```

If the manipulation needs adjustment, adapt — the key facts are: `labelCycCount Atom (m+1) = m!` and `(m+1)! = (m+1) · m!`, so `m! / (m+1)! = 1/(m+1)`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-cyclic-perm-cycles-reply.md
