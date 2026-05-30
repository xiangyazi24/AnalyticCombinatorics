# MSET-2: general multiset transfer — design (three rounds)

Goal (F&S Theorem I.1, unlabelled): for a class `C` with `C₀=∅` (`C.counts 0 = 0`),

  **`MSET(C)(z) = ∏_{m≥1} (1 - z^m)^{-Cₘ}`**,

generalizing the partition flagship (`C = ℙ`, `Cₘ=1`) from `Partitions.lean`.

## Key reduction (the design's spine)

A multiset of C-objects of weight `n`, grouped by object size `m`, is: a partition
`p` of `n` (size `m` occurs with multiplicity `kₘ = #size-m objects`) together with,
for each `m`, a size-`kₘ` multiset of the `Cₘ` objects of size `m`. Hence

  `MSET(C)ₙ = ∑_{p:Partition n} ∏_m multichoose(Cₘ, mult_m p)`,

and the number of size-`k` multisets over a `c`-set is `multichoose(c,k)`
(`card_sym_eq_multichoose`). Crucially this is **exactly Mathlib's**
`Nat.Partition.genFun (fun m j => multichoose(C.counts m, j))` evaluated at `n`
(`genFun f n = ∑_{p} p.parts.toFinsupp.prod f`). So we reuse `hasProd_genFun`:

  `MSET(C).ogf = ∏'_i (1 + ∑'_j multichoose(Cᵢ₊₁, j+1)·X^{(i+1)(j+1)})`,

and per-factor `∑_{k≥0} multichoose(c,k) X^{mk} = (1 - X^m)^{-c}` (`invOneSubPow`
gives coeff `choose(c-1+k, c-1) = multichoose(c,k)`; substitute `X ↦ X^m` via
`expand`/`subst`). For `c = Cₘ = 1` this recovers `∑_j X^{mj} = 1/(1-X^m)` (MSET-1).

## Round 1 — atoms

| # | atom | status |
|---|---|---|
| A1 | faithful graded Fintype model of `MSET(C)` | **build** — candidate: `Obj n := Σ p:Partition n, Π m:Fin(n+1), Sym (C.Obj m) (p.parts.count m)` (clean Fintype: Sigma over `Partition n`, Pi over `Fin`, `Sym` fibers) |
| A2 | `card(Sym X k) = multichoose(#X, k)` | Mathlib `card_sym_eq_multichoose` |
| A3 | `counts_mset n = ∑_{p} ∏_{m:Fin(n+1)} multichoose(Cₘ, count m)` | `Fintype.card_sigma`+`card_pi`+A2 |
| A4 | `= genFun (fun m j => multichoose(Cₘ,j)) n` | reconcile `Π_{Fin(n+1)}` vs `toFinsupp.prod` (trivial factors multichoose(c,0)=1) |
| A5 | factor `∑_k multichoose(c,k) X^{mk} = (1-X^m)^{-c}` | `invOneSubPow` coeff + `expand`/`subst X^m` |
| A6 | OGF product `MSET(C).ogf = ∏'_i (1-X^{i+1})^{-Cᵢ₊₁}` | `genFun_eq_tprod` + A5 + `tprod_congr` (reuse Partitions.lean topology setup) |

Hardest: **A1 model faithfulness/Fintype** and **A4 reconciliation** and **A5
multichoose↔invOneSubPow↔expand**.

## Open API questions for the subagent (Mathlib v4.29.0)

1. `Nat.multichoose` def + `card_sym_eq_multichoose` exact sig; `multichoose c 0 = 1`,
   `multichoose _ _` lemmas. `Sym α k` Fintype, `card` API.
2. `invOneSubPow` coeff: confirm `(invOneSubPow S c).val.coeff k = choose(c-1+k,c-1)`
   and how it equals `multichoose c k`; the `c=0`/`c+1` indexing.
3. `PowerSeries.expand`/`subst (X^m)`: `coeff_expand_mul`, applying to `(1-X)^{-c}` to
   get `(1-X^m)^{-c}` and its coeff `multichoose(c,k)` at `X^{mk}`. Cleanest route.
4. `Nat.Partition.genFun`: `p.parts.toFinsupp`, `.count`, `toFinsupp.prod`, and lemmas
   to turn `∏_{m∈support}` into `∏_{m:Fin(n+1)}` (parts ≤ n; `Partition.parts_le`?).
5. Is the A1 model the lightest faithful one, or is `{s : Multiset (Σm,C.Obj m)//weight=n}`
   (with its own Fintype) cleaner? Recommend.

## Round 3 — DECISION (post API survey)

All API verified. Decisions:
- **Model = A1 Sym-partition:** `Obj n := Σ p:Partition n, ∀ m:Fin(n+1), Sym (C.Obj m.val) (p.parts.count m.val)`.
  Faithful (multiplicities via `p`, identities via `Sym`; orthogonal, no double count).
  Rejected the `Multiset (Σm,C.Obj m)` model (Mathlib has NO Fintype for weight-bounded
  multisets over an infinite Σ-type — would require building A1 anyway + an extra equiv).
- **GOTCHA:** `Fintype (Sym α k)` needs `[DecidableEq α]`, which `CombClass` lacks ⇒ use
  `classical` (sound: everything is `Fintype.card`, a Nat, instance-irrelevant).
- **Count formula over `Finset.range (n+1)`** (not `Fin`) to avoid `Fin.val` casts; bridge
  to `Fin` via `Fin.prod_univ_eq_prod_range`. genFun reconciliation via
  `Finsupp.prod_of_support_subset` (support ⊆ range(n+1) by `le_of_mem_parts`,
  `multichoose _ 0 = 1`).
- **A5 = `invOneSubPow` + `expand`:** `coeff (m*k) (expand m hm (invOneSubPow ℚ c).val)
  = multichoose c k`, `=0` off multiples (`coeff_expand_mul`/`_of_not_dvd`); `(1-X^m)^{-c}`
  free since `expand` is an AlgHom on `(invOneSubPow ℚ c).inv = (1-X)^c`.
- **STAGED:** (1) counts layer `mset.counts = genFun(fun m j => multichoose(Cₘ,j)).coeff`
  (pure `Fintype.card`, no topology); (2) OGF layer `mset.ogf = ∏'(1-X^{i+1})^{-Cᵢ₊₁}`
  reusing `Partitions.lean` topology scaffolding. Partitions = special case `Cₘ=1`
  (`multichoose 1 k = 1`). No banking (Mathlib lacks general MSET + Euler form).

Verified names: `Nat.multichoose`, `multichoose_zero_right`, `multichoose_one`,
`multichoose_eq`, `Sym.card_sym_eq_multichoose`, `invOneSubPow_val_succ_eq_mk_add_choose`,
`invOneSubPow_inv_eq_one_sub_pow`, `expand`/`coeff_expand_mul`/`coeff_expand_of_not_dvd`/
`expand_X`, `coeff_genFun`/`genFun_eq_tprod`, `Nat.Partition.le_of_mem_parts`,
`Multiset.toFinsupp_apply`/`_support`, `Finsupp.prod_of_support_subset`,
`Fin.prod_univ_eq_prod_range`.
