# Task — Additional structural OGF/EGF identities

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append before `end CombinatorialClass`)

**Goal:** Add a small batch of one-line structural identities at OGF / EGF level. All trivial corollaries; no new lemmas needed beyond existing.

```lean
/-- (Atom + Atom).egf = 2 · X. -/
theorem Atom_disjSum_Atom_egf : (Atom.disjSum Atom).egf = 2 * PowerSeries.X := by
  rw [disjSum_egf, Atom_egf, two_mul]

/-- Atom × Atom has OGF X². -/
theorem Atom_cartProd_Atom_ogf : (Atom.cartProd Atom).ogf = PowerSeries.X ^ 2 := by
  rw [cartProd_ogf, Atom_ogf, sq]

/-- atomOfSize a × atomOfSize b has OGF X^(a+b). -/
theorem atomOfSize_cartProd_atomOfSize_ogf (a b : ℕ) :
    ((atomOfSize a).cartProd (atomOfSize b)).ogf = PowerSeries.X ^ (a + b) := by
  rw [cartProd_ogf, atomOfSize_ogf, atomOfSize_ogf, pow_add]

/-- Epsilon disjSum is left-additive zero (additive identity in OGF semiring view). -/
theorem Epsilon_disjSum_ogf (A : CombinatorialClass) :
    (Epsilon.disjSum A).ogf = 1 + A.ogf := by
  rw [disjSum_ogf, Epsilon_ogf]

/-- And right version. -/
theorem disjSum_Epsilon_ogf (A : CombinatorialClass) :
    (A.disjSum Epsilon).ogf = A.ogf + 1 := by
  rw [disjSum_ogf, Epsilon_ogf]
```

All proofs are one-line `rw` / direct combinations of existing OGF/EGF lemmas + power-series ring/algebra rewrites.

## Hard constraints

- Build green; current 2770 jobs.
- No new sorrys.
- Reply at HANDOFF/outbox/task-structural-ogf-extras-reply.md.
