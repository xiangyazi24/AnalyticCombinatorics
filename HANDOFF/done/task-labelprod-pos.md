# Task — labelProdCount permClass posIntClass

**File:** `AnalyticCombinatorics/Examples/SetPartitions.lean` (append at end)

**Goal:** Compute `labelProdCount permClass posIntClass n` and connect to a closed form.

By Theorem II.1: this corresponds to coefficient of `permClass.egf · posIntClass.egf` = `(1/(1-X)) · (exp(X) - 1)`.

Numerically:
- n = 0: labelProdCount perm posInt 0 = 0 · 1 + (cross terms = 0). Need to compute.
  count 0 of permClass = 1, of posIntClass = 0. So sum = 0.
- n = 1: labelProdCount = ∑ p ∈ antidiag 1, n.choose p.1 · perm.count p.1 · posInt.count p.2
  = (1 choose 0) · 1 · 1 + (1 choose 1) · 1 · 0 = 1.
- n = 2: ?

```lean
example : CombinatorialClass.labelProdCount permClass posIntClass 0 = 0 := by
  unfold CombinatorialClass.labelProdCount
  simp [posIntClass.count_zero]

example : CombinatorialClass.labelProdCount permClass posIntClass 1 = 1 := by
  unfold CombinatorialClass.labelProdCount
  rw [Finset.sum_eq_single (0, 1)]
  · simp [permClass_count_eq_factorial, posIntClass.count_pos (by omega : (1 : ℕ) ≥ 1)]
  · -- (1, 0) gives perm.count 1 · posInt.count 0 = 1 · 0 = 0
    rintro ⟨k, j⟩ hkj hne
    rw [Finset.mem_antidiagonal] at hkj
    have : j = 0 → posIntClass.count j = 0 := fun h => by
      subst h; exact posIntClass.count_zero
    -- analyze cases
    rcases j with _ | j
    · rw [posIntClass.count_zero]; ring
    · -- j = succ, k = 0 (since k+j+1 = 2 means k = 0)
      rcases k with _ | k
      · exfalso; apply hne
        congr; omega
      · simp at hkj; omega
  · intro h
    exfalso; apply h
    rw [Finset.mem_antidiagonal]; omega
```

If the above is fragile, simplify or give a smaller deliverable. Target: just one or two sanity checks.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-labelprod-pos-reply.md
