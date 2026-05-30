# Generic SEQ inverse — design (three rounds)

Goal: for `C : CombClass` with `C.counts 0 = 0` (F&S side-condition C₀=∅),

  **`(seq C).ogf * (1 - C.ogf) = 1`**, i.e. `SEQ(C)(z) = (1 - C(z))⁻¹`.

`seq C` is the existing Composition-based class (`Sequence.lean`):
`(seq C).Obj n = Σ c : Composition n, ∀ i : Fin c.length, C.Obj (c.blocksFun i)`,
and `counts_seq : (seq C).counts n = ∑_{c:Composition n} ∏_i C.counts (c.blocksFun i)`.

## Round 1 — atoms

| # | fact | status |
|---|---|---|
| A1 | first-part decomposition `Composition (n+1) ≃ Σ k:Fin(n+1), Composition (n-k)` | BUILD (Mathlib lacks) |
| A2 | product-over-blocks of a cons splits: `∏ over ((k+1)::c'.blocks) = C.counts(k+1) · ∏ over c'.blocks` | `Fin.prod_univ_succ` |
| A3 | counts recursion `(seq C).counts (n+1) = ∑_{k:Fin(n+1)} C.counts(k+1)·(seq C).counts(n-k)` | A1+A2 + `Fintype.sum_equiv`/`sum_sigma` |
| A4 | `(seq C).counts 0 = 1` | Composition 0 unique, empty product |
| A5 | OGF functional eq `(seq C).ogf = 1 + C.ogf·(seq C).ogf` | A3,A4 + `coeff_mul` + (C₀=0 kills j=0 term) |
| A6 | `S(1-C)=1` and `S = (1-C)⁻¹` | ring + `invOfUnit`/cancel (constantCoeff(1-C)=1) |

**Hardest: A1.** Build via `consTo`/`uncons`:

```
consTo (k : Fin (n+1)) (c' : Composition (n - k)) : Composition (n+1) :=
  { blocks := (k+1) :: c'.blocks,
    blocks_pos := by mem-cons: k+1>0 or c'.blocks_pos,
    blocks_sum := by rw[List.sum_cons, c'.blocks_sum]; omega }   -- (k+1)+(n-k)=n+1, k≤n
```
No dependent-type cast: we build `Composition (n+1)` directly; the sum obligation is a Prop closed by `omega` (uses `↑k ≤ n` from `Fin`).

uncons: `c : Composition (n+1)` ↦ blocks nonempty (sum>0) = `b::rest`, `k := b-1 : Fin(n+1)`
(b≥1 ⇒ k+1=b; b≤n+1 ⇒ b-1≤n ⇒ k<n+1), `c' := {blocks:=rest, sum = (n+1)-b = n-k}`.

Equiv round-trips via `Composition.ext` (equal iff `blocks` equal; the two proof
fields are propositions ⇒ proof-irrelevant).

## Round 2 — definitions / faithfulness

- The hypothesis is exactly `C.counts 0 = 0` (F&S C₀=∅). Stated explicitly, not hidden.
- A1 is a genuine bijection (no double counting): every composition of n+1 has a
  unique first block b≥1, and (b, rest) ↦ composition is its inverse.
- Sigma equality in round-trips: first components are *equal* (not just heq) so the
  dependent second component compares directly; use `Composition.ext`/`Sigma` ext.

## Round 3 — path

Route = consTo/uncons Equiv (Prop-level, no Type-cast) over:
- (rejected) WF-recursive `seqAux` type: WF defs don't reduce definitionally ⇒
  Fintype instance needs transported equation lemma — worse.
- (rejected) subset/`CompositionAsSet` route: cut-point bookkeeping no simpler.

Verification needed (subagent): confirm these Mathlib names/sigs exist —
`Composition.ext` (or ext by blocks), `Composition.blocksFun = blocks.get`,
`Composition.blocks_sum`, `one_le_blocks`/`blocks_pos`, `Fin.prod_univ_succ`,
`List.sum_cons`, `Fintype.sum_equiv` / `Equiv.sum_comp` / `Fintype.sum_sigma`,
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` (have), `coeff_mul` (have),
`invOfUnit`/`mul_right_cancel₀` (have). Pressure-test consTo/uncons for pitfalls.
