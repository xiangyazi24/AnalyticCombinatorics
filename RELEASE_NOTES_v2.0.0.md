# Release notes — v2.0.0 (DRAFT, for review)

**AnalyticCombinatorics — the honest, machine-checked rebuild of Flajolet & Sedgewick.**

## Why v2.0.0 (and what happened to v1.0.0)

`v1.0.0` (2026-05-06) is **retracted**. It was an auto-generated 1,283-file tree that passed mechanical
checks (compiled, no `sorry`) but was an *integrity failure*: a fabricated proof template, ~17k
`native_decide` calls injecting compiler-trust axioms, and theorems that merely projected a conjunct
out of their own hypotheses. It is archived for provenance only
(`archive/impostor-2026-05` / `archive-impostor-2026-05-30`).

**v2.0.0 is a clean break** — an unrelated formalization built from scratch since 2026-05-30, where every
theorem is genuinely stated against the book and genuinely proved. The major-version bump marks that this
shares nothing with v1.0.0 but the repository name.

## What's in it

Flagship coverage across **all nine chapters (I–IX)**, every headline theorem **clean-3**
(`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`/`axiom`/`native_decide`).

Highlights:
- **Singularity analysis to third order** — `(1−z)^{−α}` transfer and √-singularity meta-applicators
  (1st/2nd/3rd order); the tree-count family (Catalan, Motzkin, Schröder, Riordan, ternary, general
  Fuss-Catalan) and the Cayley tree function, all to third order.
- **General `log^k` singularity transfer** (any `k≥1`), Δ-domain.
- **Saddle-point / Hayman** to third order — abstract H-admissible theorem + concrete instances
  (involutions, Bell, blocks-≤3, fragmented permutations).
- **Hardy–Ramanujan partitions** — the elementary `log p(n) ~ π√(2n/3)` *and* the **sharp**
  `p(n) ~ exp(π√(2n/3)) / (4n√3)`, the latter unconditional and **without the circle method**
  (a first-entrance renewal route).
- Chapters I–III, V, IX flagships: Lagrange inversion, Pólya/cycle-index, necklaces & bracelets,
  random-mapping statistics, Cayley's formula, Flajolet continued fractions, the multivariate
  Goncharov–Kolchin limit law, quasi-powers / Gaussian, Poisson laws.

## Verification

- Integrated audit build: **8603 jobs, 0 errors**.
- **622** audited theorems; distinct axioms across all of them = exactly
  `{propext, Classical.choice, Quot.sound}`; zero integrity-escape tokens.
- See [`PRE_RELEASE_AUDIT.md`](PRE_RELEASE_AUDIT.md), [`COVERAGE_AND_OPEN_FRONTIERS.md`](COVERAGE_AND_OPEN_FRONTIERS.md),
  and the per-chapter adversarial audit [`HANDOFF/AUDIT-WHOLEBOOK.md`](HANDOFF/AUDIT-WHOLEBOOK.md).

## Build

Lean `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0`:

```bash
lake exe cache get
lake build
```

## Known scope (not gaps)

Optional extensions only: 4th-order coefficient asymptotics; further Ch IX limit-law instances;
non-integer log powers. No named theorem of the book is left open.

---
_Draft — pending review. Tag `v2.0.0` and publish under `xiangyazi24` once approved._
