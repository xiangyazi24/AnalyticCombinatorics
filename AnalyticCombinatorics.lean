import AnalyticCombinatorics.Ch1.OGF.Defs
import AnalyticCombinatorics.Ch1.OGF.Sum
import AnalyticCombinatorics.Ch1.OGF.Product
import AnalyticCombinatorics.Ch1.OGF.Sequence
import AnalyticCombinatorics.Ch1.OGF.Compositions
import AnalyticCombinatorics.Ch1.OGF.SeqFormula
import AnalyticCombinatorics.Ch1.OGF.ProductPower
import AnalyticCombinatorics.Ch1.OGF.SequenceInverse
import AnalyticCombinatorics.Ch1.OGF.SeqApplications
import AnalyticCombinatorics.Ch1.OGF.Fibonacci
import AnalyticCombinatorics.Ch1.OGF.Partitions
import AnalyticCombinatorics.Ch1.OGF.Mset
import AnalyticCombinatorics.Ch1.OGF.Pset

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
- `Ch1.OGF.Sequence` — sequence construction; `(SEQ C)ₙ = ∑_c ∏ᵢ C_{cᵢ}`;
  integer compositions as sequences of positive integers (`= 2^{n-1}`).
- `Ch1.OGF.Compositions` — OGF of integer compositions: `C(z)·(1 - 2z) = 1 - z`.
- `Ch1.OGF.SeqFormula` — `ℙ(z) = z/(1-z)`; the sequence formula for compositions
  `C(z)·(1 - ℙ(z)) = 1` (the end-to-end symbolic-method example).
- `Ch1.OGF.ProductPower` — Cartesian power `(C^k)(z) = C(z)^k`; words of length
  `k` over an `a`-letter alphabet, OGF `(a z)^k`.
- `Ch1.OGF.SequenceInverse` — the general sequence construction: for `C₀ = ∅`,
  the functional equation `S = 1 + C·S` and `(seq C)(z)·(1 - C(z)) = 1`.
- `Ch1.OGF.SeqApplications` — words over a finite alphabet (`a^n` words, OGF
  `1/(1 - a z)`); compositions as a special case of the sequence transfer.
- `Ch1.OGF.Fibonacci` — compositions into parts `1,2` are counted by `F_{n+1}`,
  with OGF `1/(1 - z - z²)`.
- `Ch1.OGF.Partitions` — integer partitions (MSET flagship): Euler's product
  `P(z) = ∏_{m≥1} 1/(1 - z^m)`, via Mathlib's `Nat.Partition.genFun`.
- `Ch1.OGF.Mset` — general multiset construction `MSET(C)`: counts layer
  `MSET(C)ₙ = ∑_p ∏_m multichoose(Cₘ, mult_m p)`, and the Euler product OGF
  `MSET(C)(z) = ∏_{m≥1} (1 - z^m)^{-Cₘ}`.
- `Ch1.OGF.Pset` — general powerset construction `PSET(C)`: sets of C-objects, with
  `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ}`.

Modules are added here as they are proved.
-/
