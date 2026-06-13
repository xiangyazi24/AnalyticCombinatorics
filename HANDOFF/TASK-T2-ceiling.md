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

## Banked this run (Opus, R8): L4 CORE reduction (clean-3, NEW file)

### L4-core — `Pker_le_enterBandKer` + `min_Pker_le_min_enterBandKer_sum` (commit `8c0568a`)
File `CeilingValueStep.lean`.  **One-step entrance lower bound** `Pker x z ≤ enterBandKer Pker B x z`
(for `x ∉ B`, `z ∈ B`, `z < x`: the `k=z` term of the entrance recursion is `Pker x z · 1`, rest
nonneg) and its slice consequence
`∑_{z∈slice} min (Pker x z) (Pker y z) ≤ ∑_{z∈slice} min (enterBandKer B x z) (enterBandKer B y z)`.
**This reduces the L4 first-entrance value Doeblin to a positive ONE-STEP value overlap**
`∑_{z∈slice} min (Pker x z) (Pker y z) ≥ β`, eliminating the entrance-kernel from the hard estimate.
Both `[propext, Classical.choice, Quot.sound]`; built green via `acbuild.sh`.

## Remaining hard cores: L4-residual + L5-escape.  Both are GENUINE analytic estimates (not mechanical).

After R8's careful re-derivation, the two remaining pieces are confirmed to be genuine substantial
estimates — each parallels the full `KernelWindow`/`RankDropMinor` development at a NEW resolution.
They are NOT closeable by re-wrapping banked bricks; both need new sliding-window analysis.

### L4-residual — positive one-step two-start value overlap (β>0)
Reduced (by `min_Pker_le_min_enterBandKer_sum`) to:
```
∃β>0, ∀ᶠ R, ∀ x y, rnk x = rnk y = R+A R →
  β ≤ ∑_{z : R ≤ rnk z < R+A R} min (Pker x z) (Pker y z)
```
`Pker x z = erdosWeight x (x−z)/kernelMass x`, `Pker y z = erdosWeight y (y−z)/kernelMass y`.
**The genuine difficulty (verified R8):** the two summed terms hit *different* divisor values
`σ(x−z)` vs `σ(y−z)` at the same `z` (since `x≠y`).  σ is irregular (prime ⟹ small), so a
*pointwise* per-term min lower bound is FALSE; and the TV between `Pker(x,·)` and `Pker(y,·)` does NOT
→0 (the starts differ by `O(√v)` = the predecessor spread), so a "window-mass − ∑|diff|" bound can be
negative.  The correct estimate is an OVERLAP of two divisor-weighted measures at shifted supports on
a common z-window — a two-start analogue of the entire `KernelWindow.erdos_kernel_window` +
`RankDropMinor.rankDropKer_ge_window` development at value resolution.  This is the real heart; it
needs a genuinely new common-two-start window mass estimate (averaging σ on both shifted windows
simultaneously), not present in the banked library.

### L5-escape — the conditional overshoot ratio needs a TAIL LOWER bound (new obstruction vs banked)
Composition (L2+L3+L4+L1 ⟹ in-band overlap δ=αβ) is mechanical.  The ESCAPE
`∑_{z : rnk z < R} enterBandKer Pker (ceilBand R (A R)) n z ≤ e R → 0` is NOT.

**Verified R8 (corrects the R7 escape sketch):** the banked escape super-solution
`enterBand_deep_mass_le_of_conditional` (EnterBandEscape.lean) needs, at EVERY off-band vertex `v`
(`rnk v ≥ C = R+A R`), the conditional `hcond`:
`∑_{k∈B, rnk k<R} Pker v k ≤ M · ∑_{k∈B} Pker v k`, i.e. `tail(rnk v−R) ≤ M·tail(rnk v−C)`
where `tail(t) = ∑_{d>t} rankDropKer v d`.  With `g := rnk v−C ≥ 0` this is
`tail(g + A R) ≤ M·tail(g)` for ALL `g`.  The super-solution's denominator is forced to be the
crossing-into-`B` mass `c(v)=tail(g)` (holding/small-drops fold into the off-band continuation
`1−c(v)`, so the total-drop `q(v)≥2η` does NOT serve as denominator — the R7 "q(v)≥2η suffices"
sketch is INCORRECT).  Bounding `tail(g+AR)/tail(g) ≤ M` uniformly in `g` (with `M=e R→0`) requires a
**geometric LOWER bound on the rank-drop tail** `tail(g) ≥ c·e^{−γ' g}` (then
`tail(g+AR)/tail(g) ≤ (C₀/c)(g+AR+1)e^{−(γ−γ')g−γ AR} ≤ (C₀/c)(AR+1)e^{−γ AR} → 0` for `γ'<γ`).
The banked `Pker_rankDrop_minorization` only gives `rankDropKer v 1, v 2 ≥ η` (i.e. `tail(0)≥2η`,
`tail(1)≥η`) — **no lower bound at thresholds `g≥2`.**  So L5-escape needs a NEW
**per-drop geometric minorant** `rankDropKer v d ≥ η_d`, `η_d ≳ d·e^{−Cd/3}`, for all `d` (eventually
in `v`).  This IS provable by the banked `rankDropKer_ge_const_of_tband` sliding-window technique
generalized from `d∈{1,2}` to a phase-cover-in-d (4 windows per `d`, endpoints scaling with `d`, the
window half-mass `modelIntegral C a b ≥ width·(π²/6)·a·e^{−(C/2)b} ≳ d·e^{−Cd/3}` by the
`y e^{−(C/2)y}` floor on `[a,b]`).  Substantial but mechanical along that template; not begun.

## Status of `erdos_partition_limit_exists`
NOT closed.  L1, L2, L3 banked clean-3; L4-CORE reduction banked clean-3 (R8, `CeilingValueStep.lean`).
The route is mathematically sound and renewal-free.  Two genuine analytic estimates remain:
(i) L4-residual = two-start common divisor-weighted value-window overlap; (ii) L5-escape = per-drop
geometric tail minorant (resolving the conditional overshoot ratio).  Each is a `KernelWindow`-scale
sliding-window development; neither is closeable by re-wrapping banked bricks.

## UPDATE (R8 elementary-route run, Opus): L4 CLOSED, δ-overlap CLOSED, full chain wired modulo escape

The R8 elementary idea (single common value window via σ(m) ≥ m) RESOLVES L4-residual: it needs NO
two-start divisor estimate.  All bricks below are clean-3 `[propext, Classical.choice, Quot.sound]`,
0 sorry/admit/native_decide/axiom, NEW files importing banked bricks.

### `CeilingValueWindow.lean` — L4 (8 bricks, CLOSED)
- `sigmaR_ge_self` : `(m:ℝ) ≤ σ(m)` for `1 ≤ m` (divisor `m ∣ m`).  [commit 6cce4a6]
- `commonValueWindow T := Icc ((T+1)²/9 − 2T) (T²/9 − T)`; `cast_div9_bounds`.  [05d8988]
- `commonValueWindow_jump_bounds` : for `rnk x = T`, `z ∈ W_T`: `1 ≤ z < x`, `T ≤ x−z ≤ 3T`,
  `√x − √z ≤ 10`.  (floor/sqrt algebra)  [05d8988]
- `commonValueWindow_subset_slice (A) (Tendsto A atTop atTop)` : `W_{R+A R} ⊆ slice`.  [7311b92]
- `Pker_commonValueWindow_lower` : `∃ c>0, ∀ᶠ T, ∀ x z, rnk x = T → z∈W_T → c/T ≤ Pker x z`
  with `c = (9/2)e^{−10C}`; uses ONLY σ(x−z) ≥ x−z ≥ T, z ≤ T²/9, √x−√z ≤ 10, kernelMass x ≤ 2.  [7311b92]
- `commonValueWindow_card_linear` : `(1/2)T ≤ |W_T|` (real length (7T−1)/9).  [2dd7902]
- `Pker_same_ceiling_oneStep_overlap (A) (hA)` : `∃ β>0` one-step value overlap `β=c/2` via banked
  `Renewal.overlap_ge_of_minorization` (η=c/T, |S|≥T/2).  [aea2a06]
- **`same_ceiling_enterBand_overlap (A) (hA)` = L4** : first-entrance value overlap `≥ β`, lifted via
  banked `min_Pker_le_min_enterBandKer_sum`.  [aea2a06]

### `CeilingCompose.lean` — δ-overlap (CLOSED)
- **`Pker_ceilBand_inband_overlap (A) (hA)`** : `∃ δ = α·β > 0, ∀ᶠ R, ∀ n n' of rank ≥ R+A R, the
  first-entrance laws into ceilBand R (A R) overlap ≥ δ on the in-band slice.**  Composition of
  L3 (`Pker_hit_ceiling_level_mass_lower`, α) + L2 (`enterBandKer_factor_through_ceiling_level`) +
  L4 (`same_ceiling_enterBand_overlap`, β) + L1 (`overlap_of_mixtures_of_pairwise_overlap`).  [3561bcf]
  This is the engine's `hoverlap`-overlap clause.  NOTE: this BYPASSES the inhomogeneous-renewal-
  with-holding coupling that `TASK-T2-gap.md` Step 2 flagged as the open obstruction — the σ≥m single
  common minorant gives a uniform δ directly, no renewal regeneration needed.

### `ErdosCeilingLimit.lean` — full assembly modulo escape (CLOSED clean-3)
- `ceilA R := 1 + ⌊√(R+1)⌋`; `ceilA_tendsto`, `ceilA_sublinear` (≤ R/2), `ceilA_pos_eventually`.
- `CeilingEscape : Prop` — the escape hypothesis (overshoot below floor R vanishes, e R → 0).
- **`erdos_partition_limit_exists_of_escape (hesc : CeilingEscape) : ∃ a, 0 < a ∧ Tendsto u atTop (𝓝 a)`**
  — clean-3.  Feeds `hitVal_cauchy_of_ceilBand_overlap_escape_variable` (δ-overlap banked, hharm via
  `hitVal_eq`, hkm via `kernelMass_pos_eventually`+`rnk_ge_of`) ⟹ hhit ⟹
  `erdos_partition_limit_exists_of_hit`.  [cf59194]

### THE SINGLE REMAINING INPUT: `CeilingEscape` (the genuine wall)
Reduces (via banked `enterBand_deep_mass_le_of_conditional`, EnterBandEscape.lean, with `tot ≡ 1`) to
the per-vertex conditional, for every off-band `v` with `g := rnk v − (R+A R) ≥ 0`:

  `tail_v(g + A R) ≤ (e R) · tail_v(g)`,   `tail_v(t) := ∑_{d > t} rankDropKer v d`.

PROVEN-OUT MATCHING-CONSTANT OBSTRUCTION (this run, Opus): the upper majorant
`Pker_rankDrop_tail_majorant` has rate `γ = C/60` (LOOSE); the true tail decay is `Θ(d·e^{−C d/3})`
(`modelIntegral_ge` gives `e^{−(C/2)b}` with `b ≈ 2d/3` ⟹ `e^{−C d/3}`), so any provable LOWER bound
has rate `γ' ≥ C/3`.  Since the conditional needs `tail(g+AR)/tail(g) ≤ e R` UNIFORMLY in `g`, the
ratio's `g`-exponent is `−γ(g+AR) + γ' g = −γ AR + (γ'−γ)g`; with `γ' = C/3 > γ = C/60` this GROWS in
`g` and the conditional fails.  Closing escape therefore requires BOTH:
  (a) a TIGHTENED tail UPPER majorant with rate `γ ≈ C/3` (re-prove `Pker_rankDrop_tail_majorant`
      with the tight constant, matching the true decay), AND
  (b) the per-drop GEOMETRIC LOWER minorant `rankDropKer v d ≥ η_d ≳ d·e^{−C d/3}`, uniform in `d`
      up to `d ≲ √v` at a SINGLE `v` — i.e. make `rankDropKer_ge_const_of_tband`'s eventual-in-`v`
      threshold EXPLICIT in `(a,b,d)` (the `3b²/(2√v)` phase-cover error scales like `d²/√v`, needing
      `v ≳ d⁴`), then a tail sum `∑_{d>g} η_d ≥ c·g·e^{−(C/3)g}` with the matching constant.
`modelIntegral_ge` (the geometric-rate integral ingredient) is banked (`RankDropGeoMinor.lean`).
This is a `KernelWindow`/`RankDropMinor`-scale sliding-window development at a NEW (per-drop, uniform-
in-d, constant-matched) resolution; it is genuinely new mathematics, NOT re-wrapping banked bricks,
and NOT effort.  Until (a)+(b) exist and produce a `CeilingEscape` witness, `erdos_partition_limit_exists`
is closed ONLY modulo `CeilingEscape`.
