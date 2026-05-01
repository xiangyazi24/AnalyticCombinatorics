# Task — A few small additional `example`s

**File:** `AnalyticCombinatorics/PartA/Ch1/CombinatorialClass.lean` (append before `end CombinatorialClass`)

```lean
/-- Atom × Atom × Atom OGF = X³. -/
example : ((Atom.cartProd Atom).cartProd Atom).ogf = PowerSeries.X ^ 3 := by
  rw [cartProd_ogf, cartProd_ogf, Atom_ogf]
  ring

/-- Epsilon disjSum Epsilon OGF = 2. -/
example : (Epsilon.disjSum Epsilon).ogf = 2 := by
  rw [disjSum_ogf, Epsilon_ogf]; ring
```

## Hard constraints

- Build green
- No new sorrys
- Reply at HANDOFF/outbox/task-misc-restate-reply.md
