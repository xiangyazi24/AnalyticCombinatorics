# TASK T2-value — gap report: value-level common-submeasure regeneration

This run executed the R6 value-level plan (`/tmp/hr_t2_value.md`, audit `/tmp/ac_a_coupling.txt`).
Two bricks are now banked clean-3; the remaining three (2.2-mass / 2.3 / 2.4) are blocked behind
genuinely new analytic infrastructure, and the R6 escape design (brick 2.1) was found to be
**mathematically incorrect as stated** and was replaced by the correct conditional form.

`#print axioms` for every banked item below is `[propext, Classical.choice, Quot.sound]` (clean-3),
0 sorry/admit/native_decide, no custom axioms, NEW files only.

## Banked this run

### 2.0 — `overlap_ge_of_common_submeasure` (commit `a9dc55a`)
File `AnalyticCombinatorics/Ch8/Partitions/CommonSubmeasure.lean`.
```lean
lemma overlap_ge_of_common_submeasure {κ : ℕ → ℕ → ℝ} {S : Finset ℕ} {lam : ℕ → ℝ}
    {n n' : ℕ} {δ : ℝ}
    (hn : ∀ z ∈ S, lam z ≤ κ n z) (hn' : ∀ z ∈ S, lam z ≤ κ n' z)
    (hmass : δ ≤ ∑ z ∈ S, lam z) :
    δ ≤ ∑ z ∈ S, min (κ n z) (κ n' z)
```
Generalizes the banked `overlap_ge_of_minorization` from a per-state floor to a spread submeasure.
This is exactly the bridge the engine needs to consume a common mass spread over a growing band.

### 2.1-core — `enterBand_deep_mass_le_of_conditional` (commit `ef0d1f2`)
File `AnalyticCombinatorics/Ch8/Partitions/EnterBandEscape.lean`.
```lean
lemma enterBand_deep_mass_le_of_conditional
    {P : ℕ → ℕ → ℝ} {B : Finset ℕ} {deep : ℕ → Prop} [DecidablePred deep]
    {M : ℝ} (hM0 : 0 ≤ M) (hPnn : ∀ n k, 0 ≤ P n k)
    (hPsupp : ∀ m k, m ≤ k → P m k = 0)
    (hcond : ∀ v, v ∉ B →
        ∑ k ∈ B.filter (fun k => deep k), P v k ≤ M * ∑ k ∈ B, P v k)
    {n : ℕ} (hn : n ∉ B) :
    ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B n z
      ≤ M * ∑ z ∈ B, enterBandKer P B n z
```

## CRITICAL CORRECTION to the R6 escape design (brick 2.1)

R6/spec set `e R := C₀(A R+1)e^{−γ A R}` and claimed the overshoot (first-entrance mass landing
below rank `R`) is `≤` the per-step rank-drop tail `M := ∑_{d>A R} rankDropKer v d`.

**This is false.** The overshoot is a *first-entrance probability*. Write, for an off-band vertex
`v`, the deep-crossing mass `a(v) = ∑_{k∈B, rnk k<R} P v k`, the total-crossing mass
`c(v) = ∑_{k∈B} P v k`, and the off-band continuation `s(v) = ∑_{k∉B} P v k`, with `c+s = 1`
(row-stochastic off-band). The overshoot satisfies `esc(v) = a(v) + s(v)·E[esc(next)]`. A chain with
high holding (`c(v)=a(v)=ε`, `s(v)=1−ε`) gives `esc = ε + (1−ε)esc = 1` — overshoot `→ 1` even though
each step's deep-crossing mass `a(v)=ε` is tiny. So `esc ≤ M` is **provably false** in general;
`a(v) ≤ M` per vertex does NOT bound the overshoot.

The correct, provable, engine-sufficient statement is **conditional**: if
`a(v) ≤ M·c(v)` at every off-band vertex (the *conditional* deep-crossing fraction is `≤ M`), then
`esc(v) ≤ M·tot(v)` (`tot ≡ 1` under certain entrance), i.e. overshoot `≤ M`. This is
`enterBand_deep_mass_le_of_conditional`, banked above. The super-solution `esc ≤ M·tot` is the right
invariant; the absolute super-solution `esc ≤ M` is not preserved by the recursion.

## Why the conditional bound is not yet dischargeable, and the embedded-chain coupling

To feed the conditional lemma we must bound, uniformly over off-band `v`,
```
a(v)/c(v) = P(crossing rank-drop > A R | the step crosses the ceiling) ≤ M = e R → 0.
```
The numerator `a(v)` is dominated by the banked tail majorant
`∑_{d>A R} rankDropKer v d ≤ C₀(A R+1)e^{−γ A R}` (`Pker_rankDrop_tail_majorant`). The denominator
`c(v)` is the *total crossing probability from v this step* — it can be arbitrarily small when `v`
has high rank (it must drop a lot to cross) or high holding, so `c(v)` has **no uniform lower bound**.
Hence the ratio is not controlled by the tail majorant alone.

The intended fix (audit §3) is the **embedded rank-change exit chain** `exitRankKer` (brick 2.2):
fold out the `d=0` holding so every step is a strict rank decrease (`c ≡ 1` for the embedded chain),
and lower-bound the per-exit rank-decrease probability by the banked per-drop minorization
`rankDropKer v 1, v 2 ≥ η` (`Pker_rankDrop_minorization`). Then the conditional ratio for the
embedded chain is `≤ (tail)/(2η) → 0`. But the engine consumes `enterBandKer Pker` (with holding),
so this route additionally requires the **holding-compression identity**
`enterBandKer Pker B n = enterBandKer (embedded exit kernel) B n` (or an inequality version), which
does not exist and is subtle: an embedded exit step lands on a strictly-lower-rank value that may
still be off-band relative to `B = ceilBand R (A R)`, so the two first-entrance kernels do not agree
definitionally. This identity is the genuine open infrastructure between 2.1-core and the engine.

## Bricks 2.2 / 2.3 / 2.4 — precise state

- **2.2 (`exitRankKer`, `exitRankKer_mass_one`).** Definitions are fine
  (`exitRankKer v := enterBandKer Pker (lowerRankBand v) v`,
  `lowerRankBand v := (range v).filter (rnk · < rnk v)`). But `exitRankKer_mass_one : ∑ = 1` is
  **not literally true**: `enterBandKer_row_sum` needs every off-band reached point to be
  row-stochastic, i.e. `∑_{k<m} Pker m k = 1`, which fails for the small `m` (`m ≤ 1`, zero kernel
  mass) that the recursion from `v` reaches at the bottom. Mass-one holds only conditionally / for
  the high part; the statement needs the same `hkm`/`m ≥ 2` guards the engine uses, plus the same
  certain-entrance argument. This is buildable but is not the trivial three-liner the spec implies.

- **2.3 (`rankRenewal_hit_rank_lower_bound`, HARD #1).** Requires an aperiodic renewal hitting lower
  bound: from any high `v`, the embedded rank chain hits a specific rank `s` (before descending below
  it) with prob `≥ α > 0`, uniform. The gcd{1,2}=1 + exp-tail "block-fills every rank" argument is a
  full renewal-theory development (a positive recurrence/local-renewal lower bound), comparable in
  size to `RankDropMinor.lean`. None of `conv`/`convPow`/`renewalMass` (RenewalCore) currently
  assembles into such a hitting lower bound; it is new mathematics, not effort.

- **2.4 (`sameRank_value_exit_overlap`, HARDEST).** The irreducible value-level content: two values
  `x, y` of the same rank `r` (so `|x−y| ≲ √v`) exit to a **common set of concrete lower values**
  with overlap `β > 0`. This is a uniform L1-overlap estimate of two adjacent `erdosWeight` rows
  `Pker x ·`, `Pker y ·` as functions of the concrete predecessor `z`, floor-phase-uniform. It is a
  genuine sliding-window density estimate at value resolution (NOT implied by `rankDropKer`, which
  aggregates over values), of size comparable to the whole `RankDropMinor.lean` development. New
  analysis, not effort.

## Status of `erdos_partition_limit_exists`

**NOT closed.** The reduction chain
`hoverlap ⟹ hitVal_cauchy_of_ceilBand_overlap_escape_variable ⟹ hhit ⟹
erdos_partition_limit_exists_of_hit ⟹ (∃a>0, Tendsto u (𝓝 a))` is verified intact, and two
engine-facing bricks (2.0 overlap bridge, 2.1-core conditional escape) are now banked clean-3. The
single remaining engine input `hoverlap` (overlap `δ` + escape `e R`) is blocked behind:

1. the **holding-compression identity** linking `enterBandKer Pker` to the embedded exit chain
   (needed to discharge the conditional hypothesis of `enterBand_deep_mass_le_of_conditional` from
   the banked tail majorant + minorization);
2. **2.3** (aperiodic renewal rank-hitting lower bound, `α`);
3. **2.4** (same-rank value-exit L1-overlap, `β`).

All three are genuinely new analytic/renewal infrastructure (each ~the size of `RankDropMinor.lean`),
not mechanical effort. The R6 plan's per-brick difficulty estimates understated 2.1 (which required
the conditional correction) and 2.2 (mass-one is conditional, not trivial).

Files added this run:
- `AnalyticCombinatorics/Ch8/Partitions/CommonSubmeasure.lean`
- `AnalyticCombinatorics/Ch8/Partitions/EnterBandEscape.lean`
