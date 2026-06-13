# TASK T2 — gap report: the rank-drop local limit (T2.1) is FALSE for the floor-rank

**Status of T2 after this run**

- **T2.2 (the designated hard core) — DONE, banked, clean-3.**
  `homogeneousRenewal_uniform_overshoot_overlap`
  (`AnalyticCombinatorics/Ch8/Partitions/RenewalOverlap.lean:262`), commit `16b5d22`.
  The abstract discrete-renewal overshoot/overlap theorem in the engine's finite-band form is
  proved by renewal coupling, with the offset-law delay-independence
  (`offsetLaw_eq`, RenewalOverlap.lean:~178) as the coupling fact:
  the first-crossing offset law from any delay `s`, measured at the first post-descent renewal, is
  `p(·+1)` **independent of `s`**, so the two delay laws share `∑_{d<B} p(d+1) ≥ p 1 > 0` on a fixed
  top slice and each escapes beyond `A` with mass `incrTail p (A+1) ≤ incrTail p A → 0`.
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

- **T2.1 (`Pker_rankDrop_asymptotic`) — BLOCKED: the stated local-limit clause is mathematically
  false** for the partition rank `rnk n = ⌊3·√n⌋` (`PartitionRenewal.lean:31`). See below.

- **T2.3 / T2.4 — cannot be built as specified**, because they consume the (false) T2.1 local limit
  to transfer the homogeneous T2.2 overlap floor to the inhomogeneous `enterBandKer Pker`.

---

## The exact missing/false fact

**Spec (`/tmp/hr_t2_renewal.md` T2.1, and `/tmp/ac_a_renewalovershoot.txt` §2.1):**

```
rankDropKer v d := ∑ k ∈ (range v).filter (rnk v - rnk k = d), Pker v k
∃ p, … ∧ ∀ D, Tendsto (fun v => ∑ d ∈ range (D+1), |rankDropKer v d − p d|) atTop (𝓝 0)
```

i.e. for each fixed rank-drop `d`, `rankDropKer v d → p d` (a single limit).

**This limit does not exist.** The rank is a *floor*: `rnk v = ⌊3√v⌋`. For a fixed jump `m`, the
rank-drop `rnk v − rnk(v−m) = ⌊3√v⌋ − ⌊3√(v−m)⌋` depends on `frac(3√v)`, and this dependence does
**not** wash out at the single-`d` resolution. Concretely, the set of jumps `m` mapping to drop
`d = 1` is the `y`-window (with `y = m/√v`) whose **upper edge oscillates with `frac(3√v)`**:
`m_max/√v` runs over roughly `[0.67, 1.12]` as `frac(3√v)` runs over `[0,1)`. Integrating the
nondegenerate Erdős density `f(y) = (π²/6) y e^{−(C/2)y}` (`KernelWindow.erdos_kernel_window`,
`modelIntegral`, KernelWindow.lean:200) over a window with `O(1)`-oscillating edges gives a
`rankDropKer(v,1)` that **oscillates and does not converge**.

Numerical witness (Riemann sum of `f` over the floor-induced `d=1` window, robust across scales):

| v | frac(3√v) | rankDropKer(v,1) | rankDropKer(v,2) |
|---|---|---|---|
| 1 000 000 | 0.000 | 0.276 | 0.568 |
| 1 000 200 | 0.300 | 0.400 | 0.601 |
| 1 000 450 | 0.675 | 0.507 | 0.621 |
| 4 000 000 | 0.000 | 0.276 | 0.568 |
| 4 000 071 | 0.053 | 0.301 | 0.575 |

The `d=1` mass swings by ≈ 0.23 (≈ 0.28 → 0.51) with the **same** amplitude at `v = 10⁶` and
`v = 4·10⁶`; the oscillation is pinned to `frac(3√v)` and is `Θ(1)`, not `o(1)`.

**Why this is a genuine obstruction, not effort.** This is exactly the lattice / arithmetic-
aperiodicity content that the full discrete Erdős–Feller–Pollard renewal theorem resolves (via the
aperiodic / non-lattice renewal limit), which the spec explicitly instructs NOT to formalize. The
floor-rank `⌊3√v⌋` makes the rank-process a *non-stationary, frac-driven* sequence; its per-step drop
law has a non-vanishing periodic-in-`frac(3√v)` component, so no single `p(d)` limit exists.

## What the engine actually needs — and why the salvage is itself non-trivial

The variable engine (`RankBandEntrance.lean:337`) does **not** consume the local limit directly. It
consumes, for the *first-entrance* kernel `enterBandKer Pker (ceilBand R (A R))`:

- **escape**: `∑_{z: rnk z < R} enterBandKer … n z ≤ e R`, `e R → 0`;
- **overlap**: `δ ≤ ∑_{z: R ≤ rnk z < R+A R} min(enterBandKer … n z, enterBandKer … n' z)`.

So the false pointwise local limit is **not strictly required**; what the audit (`§3`) actually asks
for is the weaker pair: an exp-tail majorant + a uniform aperiodic minorization
`rankDropKer(v,1) ≥ η`, `rankDropKer(v,2) ≥ η`.

- **Escape tail — buildable.** Needs only an exp-tail *majorant* of the rank-drop, uniform in `v`,
  dominated by the jump tail (`KernelWindow` / `far_erdos_tail_le`), `≤ C₀(A+1)e^{−γA}`, `γ ≈ C/3`.
  An upper bound is unaffected by the floor oscillation. This direction is genuinely reachable.

- **Overlap floor — the real remaining obstruction.** Numerically the per-drop mass stays uniformly
  positive across all phases (`rankDropKer(v,1) ∈ [0.28, 0.51]`, `rankDropKer(v,2) ∈ [0.57, 0.62]`),
  so a uniform minorization `rankDropKer(v,1), rankDropKer(v,2) ≥ η > 0` **is true**. But deriving it
  from the banked window mass `kernelWindow_one_two_pos` (`PartitionRenewal.lean:298`) is blocked by
  the same `m ↔ d` floor-conversion that carries the noise:

  * `kernelWindow 1 2 n` (`KernelBarriers.lean:28`) is positive mass on the **jump** window
    `m ∈ (√n, 2√n]`, i.e. `y ∈ (1,2]`. Under the floor-rank this maps to rank-drops `d ≈ 3y/2`,
    a *phase-dependent* set of consecutive integers `d ∈ {2,3}`(±1) — **not** a single fixed `d`.
    The banked window certifies aggregate mass on a few drops, not the per-`d` minorization the
    renewal-coupling overlap needs.
  * Worse, a fixed `y`-window low enough to guarantee `d = 1` for one phase maps partly to `d = 0`
    (no rank change) for another phase. `d = 0` events violate the renewal-increment requirement
    "every increment `≥ 1`" (`IsIncrementLaw.zero`, RenewalCore.lean:36) on which the entire
    `resKer` descent / `offsetLaw_eq` coupling rests. So the homogeneous T2.2 coupling cannot be
    instantiated verbatim; the inhomogeneous chain has a non-trivial `d = 0` holding probability that
    must be folded out (a lazy-chain / Doeblin-with-holding argument) before the offset law is even
    well-defined.

  To turn the uniform per-`d` positivity (true) into the engine's `δ` one needs **one** of:

  1. A **per-drop uniform minorization** `rankDropKer(v,1) ≥ η`, `rankDropKer(v,2) ≥ η` proved
     directly from the density (not from the `y`-window), handling the `d = 0` holding mass — i.e. a
     phase-uniform lower bound on the floor-induced single-`d` mass. This is new analysis (the banked
     window machinery is phase-blind / `y`-window only) but is finite and elementary in spirit.
  2. A non-lattice / equidistribution **averaged** renewal limit (Weyl on `frac(3√v)`), heavier.
  3. Replacing `rnk` by a non-floor surrogate — edits frozen bricks; out of scope.

## Recommendation

T2.2 (the designated hard core) is banked. The literal T2.1 local-limit clause must be **dropped**
(it is false). The honest remaining path to `hhit` is:

1. **Restate T2.1** as: exp-tail majorant (buildable) + uniform per-drop minorization
   `rankDropKer(v,1), rankDropKer(v,2) ≥ η` (true; needs the new phase-uniform single-`d` lower bound,
   incl. handling the `d = 0` holding mass).
2. **Rework T2.3** to obtain the engine overlap from the *boundary-pinned* offset minorization (both
   chains cross the common ceiling `R+A R`, so they share the boundary floor phase), not from a
   homogeneous equilibration limit — i.e. a lazy/holding-aware coupling using step (1)'s minorization.
3. Then T2.4 closes via `hitVal_cauchy_of_ceilBand_overlap_escape_variable`.

Step (1)'s phase-uniform single-`d` minorization and step (2)'s holding-aware coupling are the genuine
remaining mathematics. They are NOT the false local limit and NOT full Erdős–Feller–Pollard; they are
the engine-facing minorization + a holding-chain coupling. Until step (1) exists, `hhit` /
`erdos_partition_limit_exists` cannot be closed.

File:line anchors:
- false clause target: `Pker_rankDrop_asymptotic` (to be stated) over `rnk` = `PartitionRenewal.lean:31`
- density source: `KernelWindow.erdos_kernel_window` = `KernelWindow.lean:200`
- engine to feed: `hitVal_cauchy_of_ceilBand_overlap_escape_variable` = `RankBandEntrance.lean:337`
- banked hard core: `homogeneousRenewal_uniform_overshoot_overlap` = `RenewalOverlap.lean:262`

---

## UPDATE (T2.1-finish run): Step 1b banked; Steps 1a/2/3 obstructions located precisely

**New banked file `RankDropKer.lean` (all clean-3, `[propext, Classical.choice, Quot.sound]`):**

- `rankDropKer v d` — the rank-drop law of `Pker` (the pushforward of `Pker v ·` under
  `k ↦ rnk v − rnk k`); `rankDropKer_nonneg`.
- `large_drop_forces_large_jump` — drop `> A` on step `v→k` ⟹ jump `v−k > (A/3)√v`. The *upper*
  rank-drop bound; unaffected by the floor oscillation.
- `rankDropKer_tail_eq_mass` — `∑_{d>A} rankDropKer v d = ∑_{k: A<drop<v} Pker v k` (exact regrouping).
- `rankDrop_mass_le_far_window`, `far_window_split_le`, `left_block_tail_le`, `left_block_const_bound`,
  `succ_mul_exp_neg_le` — supporting bricks.
- **`Pker_rankDrop_tail_majorant` (Step 1b, DONE):**
  `∃ γ C₀, 0<γ ∧ ∀ᶠ v, ∀ A, ∑_{d>A} rankDropKer v d ≤ C₀·(A+1)·e^{−γA}`, with `γ = C/60`.
  Proof: drop `>A` ⟹ jump `>(A/3)√v`; bulk (`2m≤v`) via banked block majorants at index `⌊A/3⌋`,
  right half (`2m>v`) via `right_half_kernel_sum_le` + the poly-beats-exp slack `v³ ≤ e^{(C/20)√v}`;
  for `A ≥ 3√v` the far window is empty.

So the exp-tail majorant half of the restated T2.1 is now a banked theorem.

### Step 1a (the per-drop minorization) — exact missing analytic input, NUMERICALLY CONFIRMED

The minorization `rankDropKer v 1 ≥ η`, `rankDropKer v 2 ≥ η` is TRUE but is NOT reachable from the
banked window machinery, for a now-pinned reason. The **drop-1 set in `m`** is the exact integer
window
```
m ∈ ( v − (L/3)² , v − ((L−1)/3)² ],   L := rnk v = ⌊3√v⌋,
```
i.e. in `y = m/√v` coordinates a window of FIXED width `2/3` whose LOWER edge slides over
`[0, 0.45+]` and UPPER edge over `[0.667, 1.12]` as `frac(3√v)` runs over `[0,1)` (verified
numerically: at `frac=0` the window is `y∈(0, 0.667]`; at `frac=0.675` it is `y∈(0.45, 1.116]`;
at `frac→1` it is `≈ y∈(2/3, 4/3]`). **The intersection of the drop-1 windows over all phases is
empty** (the `frac=0` window `(0,2/3]` and the `frac→1` window `(2/3,4/3]` are disjoint). Hence
*no fixed `(a,b)` sub-window lies in the drop-1 set for all `v`*, so the pointwise banked limit
`erdos_kernel_window (a,b)` (one fixed pair) cannot supply the bound.

What is genuinely required is a **uniform-in-endpoints window-mass lower bound**: a version of
`erdos_kernel_window` that holds uniformly as the endpoints `(a_v, b_v)` slide over a compact family
(equivalently, `∑_{(a_v√v, b_v√v]} erdosWeight v m ≥ ∫_{a_v}^{b_v} f − ε` uniformly in the phase),
then `η := min over phase ∫_{window} f > 0` from `f`'s explicit positivity on the bulk. This is new
analysis of the size of `KernelWindow.lean` (a uniform/compact-family refinement of the per-(a,b)
limit), NOT a re-wrap. The `large_drop_forces_large_jump` machinery only gives the *upper* side
(the tail), which is why Step 1b went through cleanly while Step 1a did not.

### Steps 2/3 (holding coupling + `enterBandKer` overlap) — verified non-existent infrastructure

The engine consumes `hoverlap` for the **first-entrance kernel** `enterBandKer Pker (ceilBand R (A R))`
(RankBandEntrance.lean:347), not `rankDropKer`. `enterBandKer`/`ceilBand` appear ONLY in the engine
statement and in the abstract bridge `overlap_ge_of_minorization` (`grep` confirms: 2 files). The
bridge needs a uniform **single-state** minorization `enterBandKer Pker B n z ≥ η` on a FIXED set
`S` for ALL high starts `n` — which is FALSE for a *growing* band `A R → ∞` (the first-entrance
landing law spreads over the whole band, so `max_z enterBandKer B n z → 0`; a fixed `(η, |S|)` gives
`δ = η|S|` that cannot stay uniform). The uniform `δ` must therefore come from the **renewal
regeneration** mechanism (offset-law delay-independence, exactly the banked T2.2
`homogeneousRenewal_uniform_overshoot_overlap`), applied to the *rank chain* — but T2.2 is for a
single HOMOGENEOUS increment law, and the floor-rank step law `rankDropKer v ·` is inhomogeneous in
`v` (the documented `frac(3√v)` oscillation) and has a `d=0` holding atom. Converting the per-step
minorization of Step 1a into the first-entrance `hoverlap` requires NEW inhomogeneous-renewal-with-
holding coupling infrastructure (an embedded rank-change / lazy-chain regeneration giving a uniform
boundary-pinned offset overlap). No such bridge exists in the repo.

### Status of `erdos_partition_limit_exists`

NOT closed. The full reduction chain
`Step 3 ⟹ hitVal_cauchy_of_ceilBand_overlap_escape_variable ⟹ hhit ⟹
erdos_partition_limit_exists_of_hit ⟹ erdos_partition_limit_exists` is verified intact, but its
single remaining input `hoverlap` (Step 3) is blocked behind Step 1a (uniform sliding-window mass
lower bound) AND Step 2 (inhomogeneous holding coupling for `enterBandKer`). Both are genuine new
mathematics (not effort): Step 1a a uniform/compact-family refinement of `erdos_kernel_window`;
Step 2 an inhomogeneous-renewal-with-holding regeneration coupling. The exp-tail half (Step 1b) is
the part that the floor oscillation does NOT obstruct, and it is now banked.

New file: `AnalyticCombinatorics/Ch8/Partitions/RankDropKer.lean`.
