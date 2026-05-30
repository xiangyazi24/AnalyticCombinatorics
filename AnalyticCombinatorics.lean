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

Modules are added here as they are proved.
-/
