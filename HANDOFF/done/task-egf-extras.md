# Task — More EGF structural identities

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append)

**Goal:** A few more EGF one-liners parallel to the OGF structural identities.

```lean
/-- Epsilon disjSum left at EGF level. -/
theorem Epsilon_disjSum_egf (A : CombinatorialClass) :
    (Epsilon.disjSum A).egf = 1 + A.egf := by
  rw [disjSum_egf, Epsilon_egf]

/-- Epsilon disjSum right at EGF level. -/
theorem disjSum_Epsilon_egf (A : CombinatorialClass) :
    (A.disjSum Epsilon).egf = A.egf + 1 := by
  rw [disjSum_egf, Epsilon_egf]

/-- (Atom + Atom + Atom).egf = 3 · X. -/
theorem Atom_disjSum_three_egf : ((Atom.disjSum Atom).disjSum Atom).egf = 3 * PowerSeries.X := by
  rw [disjSum_egf, disjSum_egf, Atom_egf]
  ring

/-- atomOfSize a · X · atomOfSize b cartProd OGF: X^(a+b+1) -- size of pair plus a singleton. -/
theorem atomOfSize_triple_cartProd_ogf (a b : ℕ) :
    (((atomOfSize a).cartProd (atomOfSize b)).cartProd Atom).ogf = PowerSeries.X ^ (a + b + 1) := by
  rw [cartProd_ogf, cartProd_ogf, atomOfSize_ogf, atomOfSize_ogf, Atom_ogf]
  ring
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-egf-extras-reply.md
