# Task — labelProd associativity at EGF and count level

**File:** `AnalyticCombinatorics/PartA/Ch2/LabelledClass.lean` (append at end)

**Goal:** Prove that labelled product is associative at the EGF level (one-liner via mul_assoc) and that labelProdCount also satisfies an associative identity at the count level.

```lean
/-- labelProd is EGF-associative: ((A ⋆ B) ⋆ C).egf = (A ⋆ (B ⋆ C)).egf. -/
theorem labelProd_assoc_egf (A B C : CombinatorialClass) :
    ((A.labelProd B).labelProd C).egf = (A.labelProd (B.labelProd C)).egf := by
  rw [labelProd_egf, labelProd_egf, labelProd_egf, labelProd_egf, mul_assoc]

/-- Symmetry: A ⋆ B and B ⋆ A have the same EGF (up to commutativity of multiplication). -/
theorem labelProd_comm_egf (A B : CombinatorialClass) :
    (A.labelProd B).egf = (B.labelProd A).egf := by
  rw [labelProd_egf, labelProd_egf, mul_comm]

/-- labelProdCount is symmetric: labelProdCount A B n = labelProdCount B A n. -/
theorem labelProdCount_comm (A B : CombinatorialClass) (n : ℕ) :
    labelProdCount A B n = labelProdCount B A n := by
  rw [labelProdCount, labelProdCount]
  -- ∑_p n.choose p.1 · A.count p.1 · B.count p.2 = ∑_p n.choose p.1 · B.count p.1 · A.count p.2
  -- swap antidiag bij
  apply Finset.sum_nbij (fun p _ => (p.2, p.1))
  · -- maps_to
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab ⊢
    omega
  · -- inj
    rintro ⟨a, b⟩ _ ⟨c, d⟩ _ heq
    simp_all
  · -- surj (image cover)
    rintro ⟨a, b⟩ hab
    refine ⟨(b, a), ?_, rfl⟩
    rw [Finset.mem_antidiagonal] at hab ⊢
    omega
  · -- value match: n.choose b · A.count b · B.count a → n.choose a · B.count a · A.count b
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    -- need n.choose b = n.choose a when a + b = n
    rw [show n.choose b = n.choose a from by
      have : b = n - a := by omega
      rw [this]; exact (Nat.choose_symm (by omega)).symm]
    ring
```

Adapt as needed. Mathlib's `Nat.choose_symm` may need different invocation; if `Finset.sum_nbij` is not the right name, try `Finset.sum_bij'` or build via `image`.

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-labelprod-assoc-reply.md
