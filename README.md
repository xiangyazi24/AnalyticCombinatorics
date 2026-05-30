# AnalyticCombinatorics

A Lean 4 formalization of Flajolet & Sedgewick's *Analytic Combinatorics*,
**rebuilt from scratch starting 2026-05-30**.

## Status — early rebuild, in progress

An earlier auto-generated version of this repository (1,283 files, ~264k lines,
self-described as a "full-book formalization with 0 sorry") was audited and found
to be an **integrity failure**: it passed mechanical checks (it compiled, no
`sorry`) but did not faithfully state, let alone prove, the book's theorems.
Every file was built on a fabricated `Window/budget/certificate/slack/Ready`
template, with ~17k `native_decide` calls (which inject compiler-trust axioms)
and theorems that merely projected a conjunct out of their own hypotheses.

That tree has been removed. It is preserved for provenance at branch
`archive/impostor-2026-05` / tag `archive-impostor-2026-05-30`. The current `main`
is a clean, honest rebuild that grows only as theorems are actually proved.

### What is actually formalized so far

Part A, Chapter I (symbolic method, ordinary generating functions):

- `Ch1.OGF.Defs` — the OGF of a counting sequence; `CombClass` (a combinatorial
  class as a graded family of finite types); the primitive classes `∅`, `ε`, `Z`
  with `ε(z) = 1`, `Z(z) = z`.
- `Ch1.OGF.Sum` — the combinatorial sum: `(B + C)(z) = B(z) + C(z)`.
- `Ch1.OGF.Product` — the Cartesian product: `(B × C)(z) = B(z) · C(z)`.

Each result is anchored on a genuine `Fintype.card` identity, and `Ch1.OGF.Audit`
verifies via `#print axioms` that every headline theorem depends only on
`{propext, Classical.choice, Quot.sound}`.

Still to do in Chapter I alone: the sequence (`SEQ`), multiset (`MSET`),
powerset (`PSET`), and cycle (`CYC`) constructions, and the applications
(compositions, partitions, words, trees). The rest of the book is untouched.

## Discipline

- No `axiom`, no `native_decide`, no `def : Prop` to evade `sorry` counting, no
  smuggling a theorem's conclusion into its hypotheses.
- Every theorem is checked for *statement fidelity* against the book.
- `#print axioms` must show only the three core axioms.

## Build

Lean toolchain `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0`.

```bash
lake exe cache get
lake build
```

## License

Apache License 2.0.
