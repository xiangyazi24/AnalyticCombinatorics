import AnalyticCombinatorics.Ch1.OGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sum
import AnalyticCombinatorics.Ch1.OGF.Product

/-!
# AnalyticCombinatorics

Faithful Lean 4 formalization of Flajolet & Sedgewick, *Analytic Combinatorics*.

Rebuilt from scratch (2026-05-30) after the prior auto-generated tree was found
to be an integrity failure (trivial-impostor template across all files). The old
state is archived at branch `archive/impostor-2026-05` / tag
`archive-impostor-2026-05-30`.

Discipline (formalization-playbook):
- NO `axiom`, NO `native_decide`, NO `def : Prop` to evade `sorry` counting,
  NO smuggling the conclusion into the hypotheses.
- Every theorem must faithfully state the book's theorem (statement fidelity).
- `#print axioms` must show only `{propext, Classical.choice, Quot.sound}`.

## Part A, Chapter I — Symbolic method (OGF)

- `Ch1.OGF.Defs` — counting-sequence OGF, `CombClass`, primitive classes
  (`∅`, `ε`, `Z`) with `ε(z) = 1`, `Z(z) = z`.
- `Ch1.OGF.Sum` — combinatorial sum: `(B + C)(z) = B(z) + C(z)`.
- `Ch1.OGF.Product` — Cartesian product: `(B × C)(z) = B(z) · C(z)`.

Modules are added here as they are proved.
-/
