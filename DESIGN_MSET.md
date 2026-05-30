# MSET / PSET (Euler transform) — design (three rounds)

The remaining hard core of Ch1 §I.2. Goal (F&S Theorem I.1, unlabelled):

- **MSET(C)** (finite multisets of C-objects, `C₀=∅`):
  `MSET(C)(z) = ∏_{m≥1} (1 - z^m)^{-Cₘ} = exp(∑_{k≥1} (1/k)·C(z^k))`.
- **PSET(C)** (finite sets, each object ≤ once):
  `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ} = exp(∑_{k≥1} ((-1)^{k-1}/k)·C(z^k))`.

Flagship special case: **integer partitions** `P = MSET(ℙ)` (ℙ = one object per size
≥1), giving Euler's `P(z) = ∏_{m≥1} 1/(1-z^m)`. Distinct-part partitions = `PSET(ℙ)`.

## Round 1 — atoms (and the hard unknowns)

| # | atom | status / question |
|---|---|---|
| A1 | combinatorial model of `MSET(C)` as a graded `Fintype` | HARD: multisets of C-objects of total size n. `Multiset (Σk, C.Obj k)` with size n — is it `Fintype`? Or `→₀ ℕ` multiplicities. |
| A2 | OGF target as **infinite product** `∏_{m≥1}(1-z^m)^{-Cₘ}` | needs X-adic infinite products of `PowerSeries`. Mathlib? |
| A3 | OGF target as **exp-log** `exp(∑_k C(z^k)/k)` | needs `PowerSeries.exp`/`log` (ℚ), substitution `C(z^k)`, infinite sum. Mathlib? |
| A4 | **finite-truncation** identity: `coeff n MSET(C) = coeff n ∏_{m=1}^{n}(1-z^m)^{-Cₘ}` | avoids infinite objects entirely — only finite products. Most promising? |
| A5 | combinatorial core: multiset ↔ (multiplicity of each part), the Euler bijection | the real content, analogue of SEQ's first-part decomposition |
| A6 | flagship: `P = MSET(ℙ)`, `P(z)=∏1/(1-z^m)`; relate to Mathlib `Nat.Partition` | Mathlib partition GF? (banking check) |

## Unknowns for the subagent to resolve (Mathlib v4.29.0)

1. `PowerSeries.exp`, `PowerSeries.log` / `rescale` / substitution `C(z^k)`: exact API,
   the `constantCoeff = 0` hypotheses, `exp_add`, `exp(log)`, coeff formulas.
2. Infinite products of `PowerSeries`: is there `tprod`/`Multipliable` in the X-adic
   (`PowerSeries.PiTopology`/order) topology? `Finset.prod` + order/truncation lemmas?
   Any `PowerSeries.prod`-style convergence by order tending to ∞?
3. `(1 - X^m)⁻¹` / `invOneSubPow` for `X^m`; `(1 + X^m)`; their coeff (partitions).
4. `Nat.Partition`: is there an existing **generating function** result
   (`∏ 1/(1-X^n)` = partition GF, or distinct/odd partitions)? NAME it (banking risk),
   and any `Fintype`/`card` API usable to model MSET(ℙ).
5. `Multiset`/`Sym`/`Finsupp` `Fintype` instances usable to model `MSET(C).Obj n`.
6. Anything in `Mathlib/Combinatorics` or `RingTheory/PowerSeries` already proving an
   Euler-product / multiset generating function (would reshape or trivialize this).

## API survey results (subagent, verified on uisai1)

- `PowerSeries.exp` EXISTS (Exp.lean), but **`PowerSeries.log` MISSING** ⇒ exp-log
  path BLOCKED. Defer the `exp(∑C(zᵏ)/k)` form.
- **Infinite products EXIST** (`RingTheory/PowerSeries/PiTopology.lean`):
  `multipliable_one_sub_X_pow`, `multipliable_one_add_of_tendsto_order_atTop_nhds_top`,
  `summable_of_tendsto_order_atTop_nhds_top`, `tendsto_iff_coeff_tendsto`,
  `coeff_prod`, `one_sub_mul_tsum_pow_of_constantCoeff_eq_zero` (geometric).
- **Partition GF framework EXISTS** (`Combinatorics/Enumerative/Partition/GenFun.lean`,
  `Glaisher.lean`): `Nat.Partition.genFun f = mk (n ↦ ∑ p:Partition n, p.parts.toFinsupp.prod f)`,
  `hasProd_genFun`, `multipliable_genFun`, `genFun_eq_tprod` — shape `∏(1+∑'ⱼ f·X^{ij})`.
  Euler `card_odds_eq_card_distincts` proven via GF. **BUT the literal `∏(1-Xⁿ)⁻¹`
  partition product is an explicit TODO (unproven)** ⇒ proving it is NEW content.
- `Sym α n` is `Fintype`; `Nat.Partition n` is `Fintype`. General class-C multiset
  Fintype + multiplicity bijection = the real gap to build.
- `PowerSeries.expand p / subst (X^p)` gives `C(zᵏ)` with `coeff_expand_mul`.

## Round 2 — definitions

- **Flagship (MSET-1):** `CombClass.partitions : CombClass`, `Obj n := Nat.Partition n`
  (Mathlib Fintype). `counts n = #(Partition n)`. Faithful: a partition of n is a
  multiset of positive integers summing to n = `MSET(ℙ)` at size n.
- **General (MSET-2):** `CombClass.mset C`: model size-n objects by multiplicity
  functions `f : ℕ →₀ ℕ` over part-sizes with `∑ m·f(m) = n` decorated by C-objects,
  or `Multiset (Σk, C.Obj k)` of total weight n; Fintype from `Sym`. The transfer is
  `MSET(C).ogf = ∏'_{m≥1} (1 - X^m)^{-Cₘ}`, anchored on the multiplicity bijection.
- Boundary: `C₀=∅` required (else infinite multisets); state as `C.counts 0 = 0`.

## Round 3 — path (DECISION)

**Path = infinite-product (Mathlib-supported); staged.** exp-log rejected (no `log`).

- **MSET-1 (next milestone): integer-partition flagship.** Prove
  `partitions.ogf = ∏'_{m} (1 - X^(m+1))⁻¹` (Euler's product, Mathlib's TODO):
  1. `partitions.ogf = Nat.Partition.genFun (fun _ _ => 1)` (both `= mk(n↦#Partition n)`;
     `prod (fun _ _ => 1) = 1`).
  2. `genFun_eq_tprod` ⇒ `= ∏'_i (1 + ∑'_j X^{(i+1)(j+1)})`.
  3. geometric rewrite per factor `1 + ∑'_j X^{(i+1)(j+1)} = ∑'_j X^{(i+1)j} = (1-X^{i+1})⁻¹`
     via `one_sub_mul_tsum_pow_of_constantCoeff_eq_zero` (f = X^{i+1}, constantCoeff 0).
     ← the genuinely-new piece.
  Anchored on `#(Partition n)` (real card). Reuse of Mathlib `genFun`/topology is
  legitimate infra reuse, not banking; the Euler product form is the new theorem.
- **MSET-2: general MSET(C) transfer.** Build `mset C` Fintype + multiplicity bijection;
  generalize the `genFun`/`hasProd_genFun` proof pattern to arbitrary `Cₘ`. Hard core.
- **PSET / distinct partitions:** `∏(1+X^m)`; reuse the same machinery.

Every theorem anchored on a `Fintype.card`; no banking on the (nonexistent) Mathlib
Euler product. exp-log form optional later (needs building `PowerSeries.log` first).
