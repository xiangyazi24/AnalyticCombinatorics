# TASK T2-ceiling — progress report (R7 ceiling-level regeneration route)

Route: ceiling-level regeneration + same-ceiling value Doeblin + mixture overlap (ChatGPT R7,
`/tmp/hr_t2_ceiling.md`, `/tmp/ac_a_direct.txt`).  Goal: close `hhit` ⟹ `erdos_partition_limit_exists`.

## Banked this run (all clean-3: `[propext, Classical.choice, Quot.sound]`, 0 sorry/admit/native_decide, NEW files)

### L1 — `overlap_of_mixtures_of_pairwise_overlap` (commit `16d316a`)
File `MixtureOverlap.lean`.  Mixture-overlap bridge: pairwise level-state overlap `β` + level masses
`α` ⟹ mixture overlap `α·β`.  Proof: doubly-weighted common mass `W z = ∑_{x,y} a x b y min(K x z,
K y z)`, `W z / max(Sa,Sb) ≤ min(A z, B z)`, sum and use `Sa·Sb/max = min(Sa,Sb) ≥ α`.
NOTE: needs `0 ≤ α` (added hypothesis; false for `α<0` with negative spurious `β`).  Engine has `α>0`.

### L2 — `enterBandKer_factor_through_ceiling_level` + `enterBandKer_tower` (commit `2d18cf8`)
File `CeilingFactor.lean`.  First-entrance **tower identity** (NEW, general):
`enterBandKer P B n z = ∑_{x∈B'} enterBandKer P B' n x · enterBandKer P B x z` for `B ⊆ B'`
(strong Markov at first hit of `B'`; strong induction on `n`).  L2 restricts the `x`-sum from
`B' = ceilBand C 1` to the level `L = {rnk = C}`, discarding nonneg overshoot terms.

### L3 — `Pker_hit_ceiling_level_mass_lower` (commit `854a533`)
File `CeilingHit.lean`.  **The rank-renewal heart.**  `∃ α>0, ∀ᶠ C, ∀ n, C ≤ rnk n ⟹ α ≤ ceilHit C n`
(exact-level-C first-entrance mass, UNIFORM over all heights).

**KEY FINDING: this is renewal-free.  The ceiling route does NOT need the aperiodic
Erdős–Feller–Pollard renewal theorem** (contra the pessimism in `TASK-T2-value-gap.md`).  Mechanism:
* `ceilHit_recursion`: `ceilHit C v = ∑_{k<v} Pker v k · ceilHit C k` (holding included).
* `pushforward_rankDrop`: regroup one step by rank-drop `d`.
* Holding (drop-0, `Θ(1)` mass) folds out **inline** by strong induction on the value `v` (the
  drop-0 successor is `< v`, same rank, so the IH applies) — NO separate embedded kernel / no
  holding-compression identity needed (that worry in the value-route doc was about the *escape*
  upper bound, not this lower bound).
* The per-level overshoot tail is absorbed by the **product subsolution**
  `betaSub ε η r = (∏_{j=1}^r (1+ε_j/η))⁻¹`, antitone, `β 0 = 1`, slope **equality**
  `η(β(r-1)−β r) = ε_r·β r`, uniform floor `β r ≥ exp(−(∑'ε)/η) = α > 0` via `1+x ≤ exp x`,
  `∏ exp = exp ∑`, partial-sum ≤ tsum.  `η` = banked `Pker_rankDrop_minorization` (drop-1),
  `ε` = banked `Pker_rankDrop_tail_majorant`.  **This is NOT `η^gap`** (which decays in height).
* ChatGPT R7's `β(r)=η^K(1−∑ε̂_j)` had a **scaling bug** (off by `1/η`; closes only if `η≥1`); the
  correct multiplicative coupling is the product form above (verified, banked).

Reusable cores in this file: `pushforward_rankDrop`, `ceilHit_recursion`, `ceilHit_ge_pushforward`,
`pushforward_ge_beta`, `ceilHit_ge_beta` (abstract subsolution comparison), `betaSub` + properties,
`rankDropKer_eq_zero_of_gt`, `rankDropKer_total`, `rnk_lt_self`.

## Remaining: L4 (hardest), L5 (close).  NOT a renewal obstruction — genuine value-level work.

### L4 — `Pker_same_ceiling_value_overlap` (β>0): same-ceiling value Doeblin
```
∃β>0, ∀ᶠ R, ∀ x y, rnk x = R+A R → rnk y = R+A R →
  β ≤ ∑_{z∈(ceilBand R (A R)).filter(R≤rnk·)}
        min(enterBandKer Pker (ceilBand R (A R)) x z, enterBandKer Pker (ceilBand R (A R)) y z)
```
Two values `x,y` of the SAME ceiling rank `C=R+A R` (so `|x−y| ≲ √v`).  Their first-entrance laws
into the band `{rnk<C}` share value-level mass `β` on the in-band slice `{R ≤ rnk z < C}`.
ROUTE (R7, confirmed sound): single-step / embedded-exit VALUE Doeblin.  The predecessor laws
`Pker(x,·)`, `Pker(y,·)` each spread over `~√v` values with positive Erdős density
(`Model.erdos_kernel_window`, `modelIntegral C a b > 0`, `KernelWindow.lean`/`ModelAssembly.lean`);
find a COMMON target window inside the in-band slice and lower-bound BOTH kernels on it.  This is the
value-resolution analogue of `RankDropMinor.rankDropKer_ge_window` (reuse the sliding-window
technique, now floor-phase-uniform at value resolution, for TWO concrete starts simultaneously).
Genuinely the hardest brick (parallels the full `RankDropMinor` machinery but for a common two-start
window); NOT begun this run.

### L5 — `Pker_ceilBand_overlap_escape_variable` ⟹ engine ⟹ close
Compose L2 (factor through level) ⟹ both `x,n` and `y,n'` write their entrance laws as mixtures over
ceiling-level states with weights `a x = enterBandKer Pker (ceilBand C 1) n x` (level mass `≥ α` by
L3) and continuation `K x = enterBandKer Pker (ceilBand R (A R)) x ·`; feed L4 (pairwise `β`) + L1
(mixture bridge) ⟹ value overlap `δ = αβ` on the in-band slice.  ESCAPE part: the overshoot below `R`
is bounded by `e R → 0` via the SAME subsolution machinery as L3 but as an UPPER bound (super-solution
`esc ≤ ε(A R)` using the embedded-crossing lower bound `q(v) ≥ 2η` from the banked minorization +
`Pker_rankDrop_tail_majorant`; this is the renewal-free resolution of the holding worry).  Then feed
`hitVal_cauchy_of_ceilBand_overlap_escape_variable` (banked, `RankBandEntrance.lean`) with
`A R = A₀ + ⌊√(R+1)⌋` ⟹ `hhit` ⟹ `erdos_partition_limit_exists_of_hit` (banked, `ErdosLimit.lean`)
⟹ `erdos_partition_limit_exists`.

## Status of `erdos_partition_limit_exists`
NOT yet closed.  L1, L2, L3 banked clean-3.  L4 (value Doeblin, hardest) and L5 (compose + escape +
engine) remain.  The whole route is confirmed mathematically sound and renewal-free; the remaining
work is the value-level density estimate (L4) and mechanical composition + the escape super-solution
(L5), not a new obstruction.
