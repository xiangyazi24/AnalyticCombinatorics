# TASK #11 gap: the first-entrance rank-band route closes A–D, but Step E hits a *new* obstruction — the overshoot escape mass does not vanish for a fixed band width

## Banked this task (both green via `/tmp/acbuild.sh`, both clean-3 `[propext, Classical.choice, Quot.sound]`)

File: `AnalyticCombinatorics/Ch8/Partitions/RankBandEntrance.lean`.

- `32d0d14 HR hhit TASK11 Steps A–C` (clean-3 each):
  - **Step A** `enterBandKer P B : ℕ → ℕ → ℝ` — the first-entrance (run-until-hit) kernel
    (well-founded on `k < n`, same style as `hitVal`).  Banked: `enterBandKer_eq` (defining eqn over
    `range n`), `enterBandKer_nonneg`, `enterBandKer_supp` (vanishes off `B`), `enterBandKer_row_sum`
    (total mass `= 1` given row-stochasticity at every off-band point).
  - **Step B** `hitVal_eq_enterBand_average` — the entrance decomposition
    `hitVal n = ∑_{z∈B} enterBandKer n z · hitVal z`, valid when `hitVal` is harmonic at every off-band
    point (`hharm : ∀ m ∉ B, harmonic at m`).  Deterministic, from `hitVal_eq` + the `enterBandKer`
    recursion.
  - **Step C** `enterBand_average_diff_le` — wires the banked `doeblin_average_diff_bound`:
    two entrance laws overlapping by `≥ δ`, averaging band-confined values, differ by `≤ (1−δ)·W`.
  - **`ceilBand R A`** — the finite ceiling down-set `{k | rnk k < R+A}` (truncated to the recursion
    window `range ((R+A+2)²)`, justified by `mem_ceilBand_iff`), plus `not_mem_ceilBand_rank_ge`
    (off-band ⟹ `rnk ≥ R+A`).  **Crucial design choice:** the band is a *down-set* (unskippable on the
    way down), so Step B's harmonic hypothesis is discharged at every off-band point (rank `≥ R+A ≥ J`).
    A *thin* band `[R,R+A)` is **skippable** (a single `Pker` step can drop rank arbitrarily), which is
    why the spec's literal `rankBand R A` = `[R,R+A)` is not the right entrance set; the down-set is.

- `c905960 HR hhit TASK11 Step D` (clean-3):
  - **Step D — the abstract engine** `hitVal_cauchy_of_ceilBand_overlap_escape`
    (`RankBandEntrance.lean:221`).  Iterates the banked escape-split Doeblin contraction
    `doeblin_escape_bound` over descending ceilings via the Step B entrance decomposition; lifts to the
    tail-oscillation step contraction `V(R) ≤ (1−δ)·V(R−A) + 3·(e (R−A))·Mφ` (`tailOsc_le_of_pairwise`),
    drives `V → 0` (banked `tendsto_zero_of_step_contraction`, forcing `e → 0`), and concludes via
    `tendsto_of_tail_osc_to_zero`.  **No summability, non-circular** (the limit is produced by the
    contraction).  Its hypotheses are exactly Step E's job:
    ```
    hoverlap : ∀ᶠ R, ∀ n n', R+A ≤ rnk n → R+A ≤ rnk n' →
        (δ ≤ ∑_{z∈ceilBand R A, R ≤ rnk z} min (enterBandKer n z) (enterBandKer n' z))     -- IN-BAND OVERLAP
      ∧ (∑_{z∈ceilBand R A, rnk z < R} enterBandKer n  z ≤ e R)                              -- OVERSHOOT ESCAPE
      ∧ (∑_{z∈ceilBand R A, rnk z < R} enterBandKer n' z ≤ e R)
    with  e R → 0  (RankBandEntrance.lean:225, hetend).
    ```

So **everything upstream of the analytic overlap/escape pair is banked**, and the engine is honest
(no fake "no-escape"): it consumes both an in-band overlap `δ>0` and a *vanishing* overshoot escape
`e R → 0`.  The `ℕ↔abstract` glue to `hhit`/`erdos_partition_limit_exists` is unchanged
(`ErdosLimit.lean:24` `erdos_partition_limit_exists_of_hit`), so closing the engine's hypotheses
closes the whole problem.

## The new wall (Step E): the overshoot escape `e R` does NOT vanish for a *fixed* band width `A`

This is a *different* obstruction from TASK9 (which was the all-pairs / fixed-step-count `L` overlap
being false for far-apart ranks).  The first-entrance device fixes *that* — variable hitting time means
the two chains' entrance laws are taken when each *first* reaches the ceiling, not after a common fixed
number of steps.  But it exposes a new one:

### Quantitative analysis of the escape

`ceilBand R A = {rnk < R+A}` is a down-set, so a chain started at rank `≥ R+A` enters it at the
**first** step that crosses below `R+A`.  Write the crossing step as a rank drop `D` from the
last above-ceiling position `r ≥ R+A`.  The landed rank is `r − D`.

- **In-band** (`R ≤ r−D < R+A`) requires `D ≤ r − R`.  When `r` is near the ceiling (reached by small
  "window" steps), `D ∈ {1,2,3}` (a window step `m ∈ (√v, 2√v]` drops rank by
  `≈ 3(√v − √(v−m)) ≈ 3m/(2√v) ∈ (3/2, 3]`), so for `A ≥ 3` the landing is in-band.  The window mass is
  banked `≥ ν > 0` (`kernelWindow_one_two_pos`, `PartitionRenewal.lean:298`), giving the in-band part
  positive mass.
- **Overshoot** (`r−D < R`, i.e. `D > r − R`) requires a drop `D > A` when `r = R+A`.  The drop
  density is the Erdős/model density `f(y) = (π²/6) y e^{−(C/2)y}` on the scale `y = m/√v`
  (`ModelAssembly.lean:42` `modelIntegral`, `KernelWindow.lean:200` `erdos_kernel_window`), with `D ≈
  3y/2`.  So the conditional overshoot probability from the ceiling is
  ```
  P(D > A)  ≈  ∫_{2A/3}^∞ (π²/6) y e^{−(C/2)y} dy  =:  q(A),
  ```
  a constant **independent of R**, with `q(A) → 0` only as `A → ∞`.

Hence the escape mass `e R` is bounded **below** by a constant `q(A) > 0` that does **not** depend on
`R`.  The engine needs `e R → 0` *as `R → ∞` with `A` fixed* (the step contraction has a fixed step
length `A`).  A constant escape floor `q(A)` makes the contraction
`V(R) ≤ (1−δ)·V(R−A) + 3 q(A) Mφ` converge only to the residual band `≈ 3 q(A) Mφ / δ`, **not to 0**.

### Why this is genuinely new and not mere effort

1. The only banked local kernel fact is the *window-MASS* lower bound `kernelWindow 1 2 n ≥ ν`
   (averaged over `m ∈ (√n, 2√n]`) and the window LIMIT `erdos_kernel_window`.  These bound the
   *in-band* one-step mass from below (giving a route to the overlap `δ`), but they say nothing that
   makes the *overshoot tail* `q(A)` vanish at fixed `A`.
2. There is **no banked pointwise local-limit lower bound** `Pker(v, v−m) ≥ c/√v` (the spec's proposed
   Step E input).  `LocalLower.lean` is about `u`, not the kernel.  Such a pointwise local-limit
   theorem is itself unbanked and strictly stronger than the averaged window mass.
3. Even granting the pointwise lower bound, it would give the **in-band overlap `δ`** but would NOT kill
   the overshoot tail `q(A)` — the overshoot is the *upper* tail of the jump density, which is positive
   at every fixed `A`.

### The two routes out, neither banked

To discharge `hitVal_cauchy_of_ceilBand_overlap_escape` honestly, one of:

(E1) **Renewal-overshoot equidistribution** (the genuine missing theorem).  Let the band width grow,
   `A = A(R) → ∞` slowly, so `q(A(R)) → 0` (escape vanishes), *and* prove the in-band overlap `δ` stays
   bounded below as the band widens.  This requires the first-entrance / overshoot distribution of the
   rank-descent renewal process to converge (a renewal theorem / coupling of the overshoot chain),
   which Mathlib does not have and which is not derivable from the banked one-step window mass +
   moments (`muTilde_two_term`, `sigmaMoment_*`).  But a growing `A(R)` *also breaks the engine*: the
   tail-oscillation step contraction `tendsto_zero_of_step_contraction` needs a **fixed** step length
   `A`; a growing band gives a non-geometric iteration and is not covered by the banked driver.
   So E1 needs BOTH (i) a renewal-overshoot limit (unbanked) AND (ii) a variable-step contraction
   engine (unbanked).

(E2) **A directly-proven coupling** of the two first-entrance laws into a fixed-width band with a
   uniformly-positive common part *and* uniformly-small overshoot — i.e. prove
   `e R ≤ ε` for arbitrarily small `ε` at *fixed* `A`.  This is **false** by the analysis above
   (`e R ≥ q(A) > 0`), so E2 cannot be done with a fixed band; it is the precise sense in which the
   spec's fixed-`A` `rankBand`/`ceilBand` overlap-only hypothesis is **not satisfiable**.

## Exact missing fact (file:line + statement)

Engine: `RankBandEntrance.lean:221` `hitVal_cauchy_of_ceilBand_overlap_escape`.  Its open hypotheses
(`:229 hoverlap`, `:225 hetend`) require, for `ceilBand R A` and the partition `Pker`:

```
∃ (A : ℕ → ℕ) (δ : ℝ) (e : ℕ → ℝ),  0 < δ  ∧  (∀ R, 0 ≤ e R)  ∧  Tendsto e atTop (𝓝 0)  ∧
  ∀ᶠ R, ∀ n n', R + A R ≤ rnk n → R + A R ≤ rnk n' →
      δ ≤ ∑_{z ∈ ceilBand R (A R), R ≤ rnk z}
            min (enterBandKer Pker (ceilBand R (A R)) n z) (enterBandKer Pker (ceilBand R (A R)) n' z)
    ∧ ∑_{z ∈ ceilBand R (A R), rnk z < R} enterBandKer Pker (ceilBand R (A R)) n z ≤ e R
```

with the additional engine upgrade to a **variable step length** `A R` (currently fixed `A`).  The
analytic core is the **renewal-overshoot equidistribution of the rank-descent chain**: as the band
widens, the first-entrance (overshoot) law into `{rnk < R + A R}` from any high start (i) loses its
overshoot-below-`R` mass and (ii) keeps a uniformly-positive common part across two starts.  This is
not derivable from the banked window mass / moments and is not in Mathlib.

## Minimal next task

Two independent, both required:
1. **Variable-step tail-oscillation engine**: generalize `tendsto_zero_of_step_contraction`
   (`StepContraction.lean:18`) and the lift in `hitVal_cauchy_of_ceilBand_overlap_escape` to a step
   length `A R → ∞` with the forcing `e (R − A R) → 0`.  Pure analysis; bankable without new math.
2. **Renewal-overshoot bound** for the rank-descent chain: the genuinely missing theorem (E1).  Until
   it (or an equivalent coupling) is supplied, the escape `e R` cannot be driven to `0`, and the engine
   — though fully banked — has no satisfiable instance for `Pker`, so `hhit`/`erdos_partition_limit_exists`
   stays open.
