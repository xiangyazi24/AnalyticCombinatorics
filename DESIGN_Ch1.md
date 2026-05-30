# Ch1 Symbolic Method (OGF) — Design (three-round brainstorm)

Faithful target: Flajolet & Sedgewick, Part A, Chapter I — *Combinatorial
Structures and Ordinary Generating Functions*. The chapter's real content is the
**symbolic method**: a systematic translation from combinatorial constructions
to OGF operations (Theorem I.1, the admissibility dictionary).

## Verified Mathlib inventory (grepped on uisai1, v4.29.0 — NOT impression)

Provides (⇒ re-proving any of these = banking, FORBIDDEN):
- `PowerSeries R` / `R⟦X⟧`; `coeff`, `mk`, `coeff_mk`, `constantCoeff`,
  `constantCoeff_mk`; `coeff_mul n φ ψ = ∑ antidiagonal …` (Cauchy product).
- `invOfUnit φ u`, `mul_invOfUnit`, `invOfUnit_mul`; over a field `φ⁻¹`,
  `coeff_inv`, `isUnit_iff_constantCoeff`. Geometric: `mk_one_mul_one_sub_eq_one`
  `(mk 1)*(1-X)=1`; `invUnitsSub`, `invOneSubPow`.
- `catalanSeries`, `catalanSeries_sq_mul_X_add_one : catalanSeries^2*X+1 = catalanSeries`.
- `largeSchroderSeries_eq_one_add_X_mul_… ` (Schröder GF eq).
- `catalan`, `catalan_eq_centralBinom_div`, `catalan_succ`,
  `treesOfNumNodesEq_card_eq_catalan`.
- `Composition n`, `CompositionAsSet n`, `compositionAsSet_card = 2^(n-1)`.

Does NOT provide: any species / combinatorial-class / OGF-transfer framework.
**⇒ The faithful, non-banking deliverable is the transfer framework itself.**

---

## Round 1 — Atom decomposition

| # | Atom (math fact) | Mathlib? | Plan |
|---|---|---|---|
| A1 | `ℚ⟦X⟧`, coeff, mk, `*` | ✅ | use as-is |
| A2 | OGF of a counting sequence `A(z)=∑Aₙzⁿ` | ❌ (trivial wrapper) | `def ogf (a:ℕ→ℚ) := mk a` |
| A3 | Combinatorial class = graded type `C:ℕ→Type` `[Fintype]`; `counts C n := card (C n)` | ❌ | define |
| A4 | **Sum** `(B+C)(z)=B(z)+C(z)` | side-tools only | prove transfer (easy) |
| A5 | **Product** `(B×C)(z)=B(z)·C(z)`, `countsₙ=∑_{k≤n}Bₖ·C_{n-k}` | `coeff_mul` gives PS side | prove transfer (CORE) |
| A6 | **Sequence** `SEQ(B)(z)=1/(1-B(z))`, needs `B₀=0` | `invOfUnit`/geom | prove transfer (HARDEST) |
| A7 | binary words 2ⁿ | ✅ card | example via SEQ |
| A8 | compositions 2^(n-1) | ✅ `compositionAsSet_card` | example, cross-check |
| A9 | Catalan via recursive spec | ✅ GF eq + trees | example |

Hardest / riskiest: **A6 (Sequence)**. `SEQ(B)=ε+B×SEQ(B)` ⇒ `A=1+B·A` ⇒
`A·(1-B)=1` ⇒ `A=(1-B)⁻¹` (clean, via `invOfUnit`, needs `B₀=0` so `1-B` is a
unit). The combinatorial bijection `SEQ(B) ≅ ε + B×SEQ(B)` at type level is the
real work. Second hardest: **A5**, the size-graded product equivalence
`(B×C at n) ≅ Σ_{k≤n} B k × C (n-k)` — the foundational bridge.

---

## Round 2 — Definition review (checklist per playbook §1.2)

1. `def ogf (a : ℕ → ℚ) : ℚ⟦X⟧ := PowerSeries.mk a`. Boundary ✅; faithful ✅.
2. Class as graded type `C : ℕ → Type*` `[∀ n, Fintype (C n)]`; size = grading
   index; `counts C n := Fintype.card (C n)`; `classOGF C := ogf (fun n => counts C n)`.
   - 退化: `C n = Empty` ⇒ counts 0 ✅; neutral `ε`: `C 0=Unit, _+1=Empty` ⇒ OGF=1 ✅.
   - 论文对齐: F&S uses one set + size fn; graded-type is an equivalent encoding
     (objects of size n ↔ `C n`). Fidelity note required in the file.
   - 兼容: `Fintype` ✅.
3. Constructions as graded types:
   - Sum: `(C ⊕g D) n := C n ⊕ D n`; `counts` via `Fintype.card_sum`.
   - Product: `(C ×g D) n := Σ k : Fin (n+1), C k × D (n-k)`; counts = convolution.
   - Sequence: `SEQ C` = lists of C-objects of total size n; needs `C 0 = Empty`.

Reviewer challenges (for the adversarial pass):
- Is `Σ k:Fin(n+1), C k × D (n-k)` faithful to "pairs (β,γ), |β|+|γ|=n"? (k=0..n, complement n-k.)
- SEQ finiteness ⇔ `C₀=∅`. F&S states exactly this. Encode as hypothesis, do not hide.

---

## Round 3 — Path selection

- **Path A (type-level framework):** graded-type classes + full Fintype-equivalence
  transfers for Sum/Product/Sequence, then examples. Most faithful, heaviest;
  SEQ type-level bijection is fiddly.
- **Path B (sequence-level transfers + per-example combinatorial bridge):** prove
  `ogf (conv a b)=ogf a*ogf b`, `ogf (a+b)=…`, and SEQ geometric
  `a₀=1 ∧ (∀n, a(n+1)=conv b a (n+1)) ∧ b₀=0 ⇒ ogf a=(1-ogf b)⁻¹` — clean
  PowerSeries algebra (NOT in Mathlib). Each example supplies its own real
  combinatorial `card` identity feeding the convolution (so non-trivial).
- **Path C (examples only):** compositions, Fibonacci closed forms. Misses the
  method; least valuable.

**Recommended: Path B as milestone 1, designed so Path A layers on top.**
Rationale: playbook "选最轻路径" + "Mathlib 优先"; B's transfer theorems ARE the
GF content of Theorem I.1, provable cleanly, absent from Mathlib; each example
carries a genuine combinatorial cardinality identity (no triviality).

### Milestone 1 files
- `Ch1/OGF/Defs.lean` — `ogf`, coeff lemmas.
- `Ch1/OGF/Sum.lean` — sum transfer.
- `Ch1/OGF/Product.lean` — convolution transfer (CORE).
- `Ch1/OGF/Sequence.lean` — geometric/SEQ transfer (HARDEST).
- `Ch1/OGF/Compositions.lean` — compositions count 2^(n-1) routed via SEQ,
  cross-checked vs `compositionAsSet_card`.

Discipline: every theorem FAITHFUL/honest-tagged; `#print axioms` = core three
only (no `native_decide`/`ofReduceBool`). One file one writer. Remote build only.

---

## Round 3 FINAL (post adversarial review) — hybrid, card-anchored

Adversarial review caught: (1) `tsum_pow_mul_one_sub_of_constantCoeff_eq_zero`
(`PowerSeries/PiTopology.lean:174`) already gives `(∑' fⁱ)(1-f)=1` for `f₀=0`,
so the SEQ *algebra* is near-banking — CITE it. (2) Path B's SEQ statement with
`aₙ₊₁=conv b a` as a hypothesis is the impostor pattern (answer projected out of
the hypothesis). (3) `Composition n = {blocks//all pos, sum=n}` IS `SEQ(ℙ)` and
already has Fintype + `2^(n-1)` — use it as the SEQ model. (4) Real bottleneck =
generic SEQ Fintype, not the inverse algebra (which is ~free). (5) ℕ→ℚ cast and
antidiagonal↔range reindex frictions.

**Decision:** every headline theorem anchored on a `Fintype.card` equality
Mathlib lacks; PowerSeries-inverse facts CITED, never reproved.

**Milestone 1 (this pass) — reusable transfer core:**
- `Ch1/OGF/Defs.lean` — `ogf : (ℕ→ℕ)→ℚ⟦X⟧`, `CombClass` (graded Fintype family),
  `counts`, `CombClass.ogf`, empty/neutral/atom classes.
- `Ch1/OGF/Sum.lean` — `CombClass.sum`; `counts_sum`, `ogf_sum` (card_sum bridge).
- `Ch1/OGF/Product.lean` — `CombClass.prod` (`Obj n := Σ k:Fin(n+1), C k × D(n-k)`);
  `counts_prod = ∑_{k≤n} …` (card_sigma/card_prod), `ogf_prod = · * ·` (coeff_mul
  + antidiagonal reindex + cast). THE foundational non-banking result.

**Milestone 2 (next) — SEQ + first flagship example:**
- generic SEQ graded type + honest Fintype (modeled on `Composition`); prove
  `SEQ C ≅ ε ⊕ (C₊ ×g SEQ C)` and the count recursion; OGF `=(1-·)⁻¹` via cited
  inverse lemmas. Worked example: compositions `2^(n-1)` DERIVED through the
  chain, cross-checked vs `compositionAsSet_card`.
