# TASK #9 gap: the active FK block-drop hitting bound is a uniform *fixed-horizon* recurrence fact, not derivable from the banked (growing-horizon) occupation lemmas

## Banked this task (both green via `/tmp/acbuild.sh`, both clean-3 `[propext, Classical.choice, Quot.sound]`)

- `322fd63 HR hhit: active-domain layer (A)`
  - `AnalyticCombinatorics/Ch8/Partitions/ActiveDomain.lean`
    - `Active rnk J xy := J ≤ rnk xy.1 ∧ J ≤ rnk xy.2`, `PointFrozenBelow P rnk J`.
    - `not_active_of_below`, `cmass_eq_zero_of_frozen_apart`, `frozen_apart_not_active_cmass_zero`:
      a frozen-apart counter-row (both ranks `< J`, distinct points, point-frozen kernel) is `¬ Active`
      and has `cmass = 0`.  This isolates exactly the rows that make the *all-start* FK drop false.
- `e1366df HR hhit: active coupling inequality (B), abstract core`
  - `AnalyticCombinatorics/Ch8/Partitions/ActiveCoupling.lean`
    - `one_sub_overlap_le_umass`: `1 − overlap (Mpow P m i) (Mpow P m j) ≤ umass P rnk W i j m`
      (from banked `umass_eq` + `rho_mass_le_overlap`).
    - `harmonic_diff_le_umass`: for bounded `h` (`|h| ≤ B`) that is `Mpow`-harmonic at `i, j`,
      `|h i − h j| ≤ umass P rnk W i j m · (2 B)`.  This is the spec's coupling inequality
      `|hitVal_J(i) − hitVal_J(j)| ≤ umass_active(i,j) · osc_J(u)` with `osc_J(u) = 2 B`, route-independent.

## What (B)/(D) already reduce to (no new work needed there)

The ℕ-level `hhit` reduction is **already banked**, contradicting the TASK8-gap impression that no glue
exists at the ℕ↔abstract boundary:

- `ErdosLimit.lean:24` `erdos_partition_limit_exists_of_hit` : `(∀ᶠ J, ∃ L, Tendsto (hitVal Pker rnk J u))
  ⟹ ∃ a>0, Tendsto u`.
- `RenewalAlign.lean:29` `tendsto_of_renewal_alignment` : the convergence engine.  Consumes
  (i) `hitVal` bounded (`HitValBound.lean` `hitVal_abs_le`), (ii) `killedKer` row-stochastic
  (`KilledStochastic.lean`), (iii) `hitVal` harmonic for every killed power
  (`KilledHarmonic.lean` `killed_harmonic_pow`), and (iv) the **alignment hypothesis** `halign`.
  It does NOT need a summable rate (it uses `tailOsc` antitone + a vanishing family of `(1−δ)^m + ε`
  bounds), so center-tracking summability is sidestepped.
- `ErdosAlignConnect.lean:31` `erdos_partition_limit_exists_of_alignment` : wires the above to the
  concrete `Pker`/`hitVal`/`u`, reducing the whole problem to

  ```
  ErdosAlignment J  :=  ∃ δ, 0 < δ ∧ δ ≤ 1 ∧
    ∀ m ε, 0 < ε → ∃ R₀, ∀ i j, R₀ ≤ rnk i → R₀ ≤ rnk j →
      1 − (1−δ)^m − ε ≤ ∑_{k ≤ max i j} min (KPowK m (killedKer Pker rnk J) i k)
                                            (KPowK m (killedKer Pker rnk J) j k)
  ```
  for cofinitely many `J`  (`ErdosAlignConnect.lean:23`).

By `harmonic_diff_le_umass`/`one_sub_overlap_le_umass` (brick B) on the finite restriction of
`killedKer Pker rnk J` to `Fin (N+1)` (`KPowK` over `range (max i j + 1)` ⊆ `[0, N]` by `KPowK_support`),
the overlap RHS equals `1 − umass`, so `ErdosAlignment J` is EQUIVALENT to the active-`umass` bound

  ```
  ∀ m ε, 0 < ε → ∃ R₀, ∀ i j active high-rank (rnk ≥ R₀),  umass(i,j,m) ≤ (1−δ)^m + ε.        (★)
  ```

This is the target the spec calls `umass_active → 0` with a *geometric in m* rate.  Everything upstream
of (★) is banked.  (★) is the single remaining analytic input.

## The wall: (★) requires a uniform *fixed-horizon* FK block drop, which is (a) what the FK bridge demands and (b) FALSE over far-active pairs, while the banked occupation lemmas only deliver a *growing-horizon* recurrence

### (a) The FK route's hypothesis is all-state, fixed-`M'`

The only banked route to a *geometric* `umass` bound is the FK block bridge:

- `FKBlockBridge.lean:176` `fk_block_bridge` requires `hdrop : ∀ s, blockWeight (weightedKernel Q w) M s
  ≤ 1 − c0` — a drop from **every** state `s` (blocks compose, so the bound must be uniform over the
  whole state space, not just a subdomain).
- `FKPartitionHitting.lean:42-43` `umass_tendsto_zero_of_uniform_drop_hit` instantiates this with the
  hitting hypothesis `hhit : ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy`, i.e.
  **from every pair `xy`** the free `KhatResPair` walk hits `dropSet δ = {cmass ≥ δ}` within a **fixed**
  `M` steps with prob `≥ p0`.

The spec (C) proposes restricting this to `Active xy`.  But two obstructions remain, and they are the gap:

### (b) Restricting to `Active` does not save a fixed-`M'` hitting bound — far-active pairs break it

`dropSet δ = {cmass ≥ δ}`.  Off the rank window (`¬ GoodW`), `cmass = 0`
(`KhatRes.lean:111` `cmass_eq_zero_of_not_GoodW`), so `dropSet δ` ⊆ the comparable window `GoodW`.
The Doeblin minorant `Pker_window_minor` (`ErdosMinorization.lean:86`) gives `cmass ≥ δ(D) =
exp(−C(2+D))/8 > 0` **only on the comparable window** `|√x − √y| ≲ D`.  So:

- A comparable active pair (in `GoodW`) is already in `dropSet δ`: `hitProb ≥ 1` trivially (`M' = 1`).
- A **far** active pair (both ranks `≥ J`, but `|rnk x − rnk y|` large, `¬ GoodW`) is **not** in
  `dropSet δ`, and the free walk there is the product walk (`KhatRes.lean:120`
  `KhatRes_eq_prod_of_not_GoodW`).  With bounded increment `b` (banked `b ~ (3/2) n^{1/6}`), the
  difference walk needs `≳ |rnk x − rnk y| / b` steps to reach the window.  Since `Active` does not
  bound the rank gap (it bounds only `min(rnk x, rnk y) ≥ J`), for any fixed `M'` there are active far
  pairs with gap `> b·M'` from which `hitProb (dropSet δ) M' = 0`.  Hence

  ```
  ¬ ∃ p0 > 0, ∃ M', ∀ xy, Active J xy → p0 ≤ hitProb (KhatResPair Pker rnk W) (dropSet δ) M' xy.
  ```

  The active restriction removes the *frozen-apart below-J* rows (brick A) but NOT the *far high-rank*
  rows, which break the uniform fixed-`M'` hitting bound for exactly the same reason the all-start
  version failed.  So `fk_block_bridge` cannot be instantiated on `Active` either.

### (c) (★) itself is FALSE as universally quantified over far pairs — the alignment def needs comparable confinement, which the banked engine does not expose

In (★)/`ErdosAlignment`, `R₀` is chosen AFTER `(m, ε)` but bounds only `min(rnk i, rnk j) ≥ R₀`, not the
gap `|rnk i − rnk j|`.  For fixed `m`, the killed-kernel drift at high rank is tiny (banked
`muTilde_two_term`, `MuNumAssembly.lean:1062`: `μ̃(n) = μ̄ + μA/√n + O(1/n)`, and per-step rank change
is `O(1)`), so `KPowK m (killedKer) i` stays concentrated within `O(b·m)` of `rnk i`.  Picking `i` at
rank `R₀` and `j` at rank `R₀ + 2 b m` (both `≥ R₀`, both active) gives disjoint `m`-step supports, so

  ```
  overlap (KPowK m i) (KPowK m j) ≈ 0,    i.e.   1 − overlap ≈ 1 > (1−δ)^m + ε   for small m.
  ```

So `ErdosAlignment J` (`ErdosAlignConnect.lean:23`) and (★) are **not satisfiable as stated** over
unbounded-gap pairs.  The mathematically correct statement is the **comparable** version (the spec's own
(C)/(D): "active block-drop for *comparable* active pairs + far pairs by center-tracking",
`CompContraction.lean` / `CenterTracking.lean`).  But the banked convergence engine
`tendsto_of_renewal_alignment` (via `tailOsc_le_of_pairwise`, `TailBand.lean:100`) consumes the
**all-pairs** bound, not a comparable-only bound plus center links.  There is no banked theorem that
derives `∀ᶠ J, (∃ L, Tendsto (hitVal Pker rnk J u))` from a *comparable-only* `umass` decay plus
`CompContraction`/`CenterTracking` links; the only banked path is through the all-pairs
`tendsto_of_renewal_alignment`.

## The exact missing lemma(s)

To close TASK #9 without faking, one of the following must be supplied; neither is derivable from the
banked moments (`two_term_local_lip` `TwoTermLocalLip.lean:22`, `muTilde_two_term`,
`sigmaMoment_one_two_term` `MassRateMomentOneTwoTerm.lean:332`, the variance/4th-moment bricks
`OccupationAssembly.lean`/`OccupationFinal.lean`) which only give a **growing-horizon** occupation
`∃ T, target ≤ ∑_{t<T} occ(t)` (`OccupationFinal.lean` `occupation_unbounded`,
`LocalizedOccupation.lean:30` `occupation_unbounded_loc`) and the **non-summable** energy rate
`umass M ≤ K0/M` (`UmassZero.lean` `umass_tendsto_zero`):

1. **Comparable convergence engine** (preferred; matches spec C/D):
   ```
   theorem tendsto_hitVal_of_comparable_umass
     (J : ℕ)
     (hcmp : ∃ δ W0, 0 < δ ∧ ∀ m ε, 0 < ε → ∃ R₀, ∀ i j,
        R₀ ≤ rnk i → R₀ ≤ rnk j → |Real.sqrt i − Real.sqrt j| ≤ W0 →   -- COMPARABLE only
        umassKilled J i j m ≤ (1 - δ) ^ m + ε)
     (hlink : Summable (center-link bound from CompContraction/CenterTracking)) :
     ∃ L, Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)
   ```
   i.e. wire `CompContraction.lean` `tendsto_of_comparable_contraction` (currently UNUSED by the main
   line) to `harmonic_diff_le_umass` (brick B) for comparable pairs, with far pairs via summable center
   links.  MISSING: the bridge from `umassKilled` (comparable) + center links to `tendsto hitVal`; the
   banked engine is all-pairs only.

2. **Fixed-horizon active-comparable hitting bound** (feeds `fk_block_bridge` on a comparable-confined
   subdomain):
   ```
   ∃ δ p0 M', 0<δ ∧ 0<p0 ∧ 0<M' ∧
     ∀ xy, Active J xy → comparable xy →
        p0 ≤ hitProb (KhatResPair Pker rnk W) (dropSet Pker rnk W δ) M' xy
   ```
   together with a confinement lemma showing the comparable-confined walk does not leave the comparable
   band within a block (FALSE for the free walk: increment `b ~ n^{1/6} ≫ W0`), or a reflecting/return
   estimate giving a fixed-`M'` return probability uniform over comparable active pairs.  MISSING: a
   **fixed-horizon recurrence** `P(τ_window ≤ M') ≥ p0`.  The banked occupation lemmas give only the
   **growing-horizon** statement `∃ T(target), target ≤ ∑_{t<T} occ(t)` (T grows with the target), which
   does not yield a uniform single-block hitting probability; converting one to the other requires a
   Markov-type renewal / return-time bound (e.g. `E[τ_window] ≤ C` ⟹ `P(τ_window ≤ 2C) ≥ 1/2`) that is
   **not** among the banked moments and is not derivable from cumulative occupation alone.

## Why this is a genuine wall, not a finite-sum re-derivation

- The frozen-apart obstruction (TASK8) is resolved for the *below-J* rows (brick A), but the *far
  high-rank* rows break the same uniform fixed-`M'` hitting bound, and `Active` does not constrain the
  rank gap.
- The banked occupation/energy machinery delivers either a growing-horizon recurrence
  (`occupation_unbounded[_loc]`) or a non-summable `O(1/M)` rate (`umass_tendsto_zero`).  The geometric
  rate needed for `ErdosAlignment` comes ONLY from `fk_block_bridge`, whose all-state fixed-`M'` drop
  hypothesis is false here.
- The correct comparable-only formulation has no banked convergence engine: `tendsto_of_renewal_alignment`
  is all-pairs, and `CompContraction`/`CenterTracking` are not wired to the killed `umass`/`hitVal`.

## Minimal next task

Build the **comparable convergence engine** (option 1): a theorem deriving `∃ L, Tendsto (hitVal Pker rnk
J u)` from (i) `harmonic_diff_le_umass` restricted to comparable active pairs, (ii) a comparable-only
`umass` decay `umassKilled J i j m ≤ (1−δ)^m + ε` (itself needing the fixed-horizon active-comparable
hitting bound, option 2, or a directly-proven comparable recurrence), and (iii) the summable center
links from `CompContraction.lean`/`CenterTracking.lean`.  Until the fixed-horizon return-time / hitting
bound (option 2's `P(τ_window ≤ M') ≥ p0`) is proven from the banked moments — or shown to need a new
moment input — the geometric `umass` decay (★) cannot be obtained, and `ErdosAlignment`/`hhit` cannot be
discharged without assuming a false uniform fixed-`M'` hitting hypothesis.
