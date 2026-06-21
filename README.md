# AnalyticCombinatorics

A Lean 4 formalization of Flajolet & Sedgewick's *Analytic Combinatorics*,
**rebuilt from scratch starting 2026-05-30** — clean, honest, and machine-checked.

## Status

Flagship coverage across **all nine chapters (I–IX)** of the book, every headline theorem verified
clean-3: `#print axioms` shows only `{propext, Classical.choice, Quot.sound}`, with **no `sorry`,
no `axiom`, no `native_decide`** (419 Lean files, ~129,000 lines; 622 audited theorems). See
[`PRE_RELEASE_AUDIT.md`](PRE_RELEASE_AUDIT.md) and [`COVERAGE_AND_OPEN_FRONTIERS.md`](COVERAGE_AND_OPEN_FRONTIERS.md).

**Highlights:**

- The **sharp Hardy–Ramanujan partition asymptotic** `p(n) ~ exp(π√(2n/3)) / (4n√3)` — proved
  *unconditionally, without the circle method or modular forms* (an elementary first-entrance renewal
  route); alongside the elementary `log p(n) ~ π√(2n/3)`.
- The **singularity-analysis and saddle-point** coefficient machinery carried to **third order**, with
  concrete instances across the standard tree and permutation families.
- **Lagrange inversion**, **Pólya enumeration / the cycle-index theorem**, the **Flajolet
  continued-fraction theorem**, and the **multivariate Goncharov–Kolchin** limit law.

### Provenance (read this)

An earlier auto-generated version (the retracted **v1.0.0**, 1,283 files, self-described as a
"full-book formalization with 0 sorry") was an **integrity failure**: it compiled and had no `sorry`,
but did not faithfully state the book's theorems — it was built on a fabricated
`Window/budget/certificate/slack` template, used ~17k `native_decide` (injecting compiler-trust
axioms), and "proved" theorems by projecting a conjunct out of their own hypotheses. That tree is
removed from `main`, preserved only for provenance at `archive/impostor-2026-05` /
tag `archive-impostor-2026-05-30`. **The current `main` is an unrelated, from-scratch rebuild** that
grows only as theorems are actually proved and adversarially audited.

## What is formalized

Per-chapter highlights (full map in [`COVERAGE_AND_OPEN_FRONTIERS.md`](COVERAGE_AND_OPEN_FRONTIERS.md);
independent per-chapter audit verdicts in [`AUDIT-WHOLEBOOK.md`](AUDIT-WHOLEBOOK.md)):

- **I — OGF / symbolic method** (Ch1): Pólya enumeration & the cycle-index theorem, necklaces,
  bracelets (dihedral PET), Lagrange inversion.
- **II — EGF / labelled** (Ch2): Bell numbers as genuine partition counts, random-mapping statistics
  (connected / cyclic points / components, all sharp), Cayley's formula & forests, Ramanujan Q.
- **III — MGF / parameters** (Ch3): bivariate GFs, moments, variance, marked constructions.
- **IV + VI — complex & singularity analysis** (Ch4): Δ-domain transfer for `(1−z)^{−α}` to **third
  order**, the √-singularity meta-applicators (2nd & 3rd order), and the general `log^k` transfer (all `k`).
- **V — rational & meromorphic** (Ch5): meromorphic coefficient transfer, surjections, general
  compositions, the Flajolet continued-fraction theorem.
- **VII — singularity-analysis applications** (Ch7): Catalan, Motzkin, Schröder, Riordan, ternary and
  general Fuss-Catalan tree counts, all to **third order**.
- **VIII — saddle point** (Ch8): Hayman H-admissibility (1st/2nd/**3rd** order) with concrete instances
  (involutions, Bell, blocks-≤3, fragmented permutations); and the **Hardy–Ramanujan partition
  asymptotic** — both the elementary `log p(n) ~ π√(2n/3)` and the **sharp**
  `p(n) ~ exp(π√(2n/3)) / (4n√3)`, the latter proved unconditionally *without the circle method*.
- **IX — random structures / limit laws** (Ch9): quasi-powers / Gaussian limit law, fixed-points and
  r-cycles → Poisson, and the multivariate Goncharov–Kolchin theorem.

Remaining work is optional depth/breadth only (4th-order coefficient asymptotics; further Ch IX limit-law
instances; non-integer log powers) — no major named theorem of the book is left open.

## Discipline

- No `axiom`, no `native_decide`, no `def : Prop` to evade `sorry` counting, no smuggling a theorem's
  conclusion into its hypotheses.
- Every theorem is checked for *statement fidelity* against the book.
- `#print axioms` must show only `{propext, Classical.choice, Quot.sound}` — verified centrally in
  `Ch1.OGF.Audit` and re-swept before release.

## Build

Lean toolchain `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0`.

```bash
lake exe cache get
lake build
```

## License

Apache License 2.0.
