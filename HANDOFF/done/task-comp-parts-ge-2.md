# Task — compositions into parts ≥ 2

**File:** `AnalyticCombinatorics/Examples/Compositions.lean` (append)

**Goal:** Define a class of compositions into parts of size ≥ 2 and prove the count satisfies fib(n-1) for n ≥ 2 (with count 0 = 1, count 1 = 0).

```lean
/-- Positive integers with size ≥ 2: each k ≥ 2 has size k. -/
def posIntGe2Class : CombinatorialClass where
  Obj := {n : ℕ // 2 ≤ n}
  size := fun ⟨n, _⟩ => n
  finite_level n := by
    by_cases h : 2 ≤ n
    · apply Set.Finite.subset (Set.finite_singleton (⟨n, h⟩ : {k : ℕ // 2 ≤ k}))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      have hvn : v = n := hx
      subst hvn; rfl
    · apply Set.Finite.subset Set.finite_empty
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨v, hv⟩ := x
      change v = n at hx
      omega

namespace posIntGe2Class

/-- count 0 = 0 (no part of size 0). -/
lemma count_zero : posIntGe2Class.count 0 = 0 := by
  show (posIntGe2Class.level 0).card = 0
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hsz : posIntGe2Class.size x = 0 :=
    (posIntGe2Class.finite_level 0).mem_toFinset.mp hx
  obtain ⟨v, hv⟩ := x
  change v = 0 at hsz
  omega

end posIntGe2Class

/-- The class of compositions into parts of size ≥ 2. -/
noncomputable def compositionGe2Class : CombinatorialClass :=
  seqClass posIntGe2Class posIntGe2Class.count_zero
```

## Hard constraints

- Build green
- No new sorrys when delivered (or file blocker if proofs hard)
- Reply at HANDOFF/outbox/task-comp-parts-ge-2-reply.md
