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
import AnalyticCombinatorics.Ch1.OGF.DistinctPartitions
import AnalyticCombinatorics.Ch1.OGF.Pointing
import AnalyticCombinatorics.Ch1.OGF.CycleModel
import AnalyticCombinatorics.Ch1.OGF.CycleBurnside
import AnalyticCombinatorics.Ch1.OGF.CycleOGF
import AnalyticCombinatorics.Ch2.EGF.Defs
import AnalyticCombinatorics.Ch2.EGF.LabelledProduct
import AnalyticCombinatorics.Ch2.EGF.LabelledSum
import AnalyticCombinatorics.Ch2.EGF.LabelledPower
import AnalyticCombinatorics.Ch2.EGF.LabelledSet
import AnalyticCombinatorics.Ch2.EGF.SetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSetOde
import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch2.EGF.LabelledSeq
import AnalyticCombinatorics.Ch2.EGF.Applications
import AnalyticCombinatorics.Ch2.EGF.LabelledCyc
import AnalyticCombinatorics.Ch3.BGF.Defs
import AnalyticCombinatorics.Ch3.BGF.Moments
import AnalyticCombinatorics.Ch3.BGF.Variance
import AnalyticCombinatorics.Ch3.BGF.SeqMarked
import AnalyticCombinatorics.Ch3.BGF.BinaryWords
import AnalyticCombinatorics.Ch3.BGF.LabelledSeqMarked
import AnalyticCombinatorics.Ch3.BGF.LabelledSetMarked
import AnalyticCombinatorics.Ch3.BGF.LabelledBGFApplications
import AnalyticCombinatorics.Ch3.BGF.CompositionMoments
import AnalyticCombinatorics.Ch3.BGF.BinaryWordMoments
import AnalyticCombinatorics.Ch4.Analytic.Bridge
import AnalyticCombinatorics.Ch4.Analytic.Poles
import AnalyticCombinatorics.Ch4.Analytic.Rational
import AnalyticCombinatorics.Ch4.Analytic.Fibonacci
import AnalyticCombinatorics.Ch4.Analytic.SingularityInteger
import AnalyticCombinatorics.Ch4.Analytic.SingularityGeneral
import AnalyticCombinatorics.Ch4.Analytic.CentralBinomial
import AnalyticCombinatorics.Ch4.Analytic.Catalan
import AnalyticCombinatorics.Ch4.Analytic.PringsheimCore
import AnalyticCombinatorics.Ch4.Analytic.Pringsheim
import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import AnalyticCombinatorics.Ch4.Analytic.RepeatedPole
import AnalyticCombinatorics.Ch4.Analytic.PringsheimExample
import AnalyticCombinatorics.Ch4.Analytic.RealAsymptotics
import AnalyticCombinatorics.Ch4.Analytic.Derangements
import AnalyticCombinatorics.Ch4.Analytic.GrowthRates
import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
import AnalyticCombinatorics.Ch4.Analytic.DeltaGeometry
import AnalyticCombinatorics.Ch4.Analytic.KernelEstimate
import AnalyticCombinatorics.Ch4.Analytic.OTransfer
import AnalyticCombinatorics.Ch4.Analytic.LittleOTransfer
import AnalyticCombinatorics.Ch4.Analytic.TransferTheorem
import AnalyticCombinatorics.Ch4.Analytic.DerivEstimate
import AnalyticCombinatorics.Ch4.Analytic.CoeffDescent
import AnalyticCombinatorics.Ch4.Analytic.LittleODescent
import AnalyticCombinatorics.Ch4.Analytic.TransferGeneral
import AnalyticCombinatorics.Ch4.Analytic.SubstComp
import AnalyticCombinatorics.Ch8.SaddlePoint.Bound
import AnalyticCombinatorics.Ch8.SaddlePoint.Assembly
import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import AnalyticCombinatorics.Ch8.SaddlePoint.ExpStirling
import AnalyticCombinatorics.Ch8.SaddlePoint.Exp
import AnalyticCombinatorics.Ch8.SaddlePoint.Bell
import AnalyticCombinatorics.Ch8.SaddlePoint.BellBridge
import AnalyticCombinatorics.Ch8.SaddlePoint.HAdmissible
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer
import AnalyticCombinatorics.Ch5.Meromorphic.Surjections
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees
import AnalyticCombinatorics.Ch7.SingularityApp.Motzkin
import AnalyticCombinatorics.Ch7.SingularityApp.FussCatalan
import AnalyticCombinatorics.Ch9.LimitLaws.QuasiPowers

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
- `Ch1.OGF.DistinctPartitions` — partitions into distinct parts `= PSET(ℙ)`, with
  generating function `∏_{m≥1} (1 + z^m)`.
- `Ch1.OGF.Pointing` — the pointing construction `Θ(C)(z) = z·C'(z)` (counts `n·Cₙ`).

## Part A, Chapter II — Labelled structures (EGF)

- `Ch2.EGF.Defs` — exponential generating functions `A(z) = ∑ Aₙ zⁿ/n!`;
  permutations (`1/(1-z)`) and the set class (`e^z`).
- `Ch2.EGF.LabelledProduct` — the labelled product: `(A ⋆ B)(z) = A(z)·B(z)`
  (binomial convolution `(A⋆B)ₙ = ∑ₖ C(n,k)·Aₖ·B_{n-k}`).
- `Ch2.EGF.LabelledSum` — the labelled sum: `(A + B)(z) = A(z) + B(z)`.
- `Ch2.EGF.LabelledPower` — labelled power `(C^{⋆k})(z) = C(z)^k`.
- `Ch2.EGF.LabelledSet` — labelled set construction `SET(C)` (counts layer):
  `SET(C)ₙ = ∑_π ∏_{B∈π} C_{|B|}` over set partitions.
- `Ch2.EGF.SetExp` — ODE machinery toward `SET(C)(z)=exp(C(z))`: `exp(C(z))` solves
  `F'=C'·F`, and that ODE has a unique solution.
- `Ch2.EGF.LabelledSetOde` — the combinatorial ODE `SET(C)'=C'·SET(C)` (pointing
  bijection on set partitions); the recurrence `SET_{n+1}=∑ C(n,i)·C_{i+1}·SET_{n-i}`.
- `Ch2.EGF.LabelledSetExp` — **`SET(C)(z) = exp(C(z))`** (the exponential formula),
  via the ODE + uniqueness.
- `Ch2.EGF.LabelledSeq` — labelled sequence: `SEQ(C)(z)·(1 - C(z)) = 1`, i.e. `1/(1-C(z))`.
- `Ch2.EGF.Applications` — Bell `exp(e^z-1)`; surjections `1/(2-e^z)`; involutions `exp(z+z²/2)`.
- `Ch2.EGF.LabelledCyc` — the labelled cycle construction `CYC(C)' = C'·SEQ(C)`
  (= `C'(z)/(1-C(z))`, i.e. `log(1/(1-C(z)))`), with `CYC(0)=0` (ODE characterization).

## Part A, Chapter III — Combinatorial parameters (bivariate GF)

- `Ch3.BGF.Defs` — parameterized classes; bivariate GF `F(z,u)=∑ b_{n,k} z^n u^k`
  over `ℚ[u]⟦z⟧`; sum/product transfers; `evalU 1 = OGF`.
- `Ch3.BGF.Moments` — mean via `∂_u` at `u=1`; compositions-by-#parts flagship.
- `Ch3.BGF.Variance` — variance (2nd factorial/raw moment); closed bivariate GF of
  compositions by #parts `(1-z)/(1-(1+u)z)`.

Modules are added here as they are proved.
-/
