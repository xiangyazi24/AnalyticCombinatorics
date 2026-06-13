# TASK #8 gap: concrete FK block-drop needs an active-domain split

## Status banked before this gap

- `411342f HR hhit: add FK residual bridge`
  - `FKBlockBridge.lean`: abstract finite-state FK block bridge.
  - `FKPartitionBridge.lean`: `Kres = (1 - cmass) * KhatRes`, `umass = uMass KresPair`, and
    `umass_tendsto_zero_of_fk_block_drop`.
- `a0cf8a5 HR hhit: add FK hitting drop bridge`
  - `FKHittingBridge.lean`: abstract `hitProb` and hitting-to-FK-block-drop lemma.
- `68ebdf2 HR hhit: connect drop hitting to umass`
  - `FKPartitionHitting.lean`: concrete drop set
    `dropSet P rnk W δ xy := δ ≤ cmass P rnk W xy.1 xy.2` and the conditional theorem
    `umass_tendsto_zero_of_uniform_drop_hit`.

All three committed bricks were built through `/tmp/acbuild.sh` and their inline `#print axioms` output
was clean-3 (`propext`, `Classical.choice`, `Quot.sound`).  The full root build was not used as a green
signal because `bash /tmp/acbuild.sh AnalyticCombinatorics` spent >23 minutes in the pre-existing
`MassRateReg3` module; the target modules above build cleanly.

## What is now reduced

The survival-tilt obstruction from `TASK7-gap.md` is resolved.  The current concrete bridge is:

- `FKHittingBridge.lean:156-163`
  ```lean
  theorem blockWeight_le_of_hitProb ... :
    ∀ s, blockWeight (weightedKernel Q w) M s ≤ 1 - δ * p0
  ```
- `FKPartitionHitting.lean:39-44`
  ```lean
  theorem umass_tendsto_zero_of_uniform_drop_hit ...
    (hhit :
      ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0)
  ```

So the remaining analytic input is exactly a concrete lower bound for hitting
`dropSet P rnk W δ = {xy | δ ≤ cmass xy}` by the free `KhatResPair` walk.

## New blocker

The all-start hypothesis in `FKPartitionHitting.lean:42-43` is false for the killed partition chain.
Spec8 warned about this, and the source confirms it:

- `KilledHarmonic.lean:17-19`:
  ```lean
  def killedKer (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) : ℕ → ℕ → ℝ :=
    fun n k => if rank n < J then (if k = n then 1 else 0) else P n k
  ```
  Below the cutoff, the killed chain is identity-absorbing.
- `ITERCoupling.lean:42-45`:
  ```lean
  def Cpart (x y z : α) : ℝ := if GoodW rnk W x y then min (P x z) (P y z) else 0
  def cmass (x y : α) : ℝ := ∑ z, Cpart P rnk W x y z
  ```
  For two distinct below-cutoff states `x ≠ y`, the two rows are different point masses, so their overlap
  is `0`.
- `KhatRes.lean:23-30` parks only the `cmass = 1` rows.  Rows with `cmass = 0` retain survival weight
  `1` and do not force any FK drop.

Thus for a frozen-apart pair `(x,y)` with both ranks below `J` and `x ≠ y`, the free `KhatResPair` walk
stays at that pair, `cmass = 0`, `dropSet δ` is never hit for any `δ > 0`, and the block weight is `1`.
Consequently a theorem of the form

```lean
∀ xy, p0 ≤ hitProb (KhatResPair (killedKer Pker rnk J) rnk W)
                  (dropSet ... δ) M xy
```

cannot be true with `p0 > 0`.

## Missing interface

To continue without faking, the next brick must replace the all-start bridge by an active/frozen split.
One workable interface is:

```lean
def Active (J : ℕ) (xy : Fin (N+1) × Fin (N+1)) : Prop :=
  J ≤ rnk xy.1.1 ∧ J ≤ rnk xy.2.1

theorem khatRes_active_drop_hit :
  ∃ δ p0 M, 0 < δ ∧ 0 < p0 ∧ 0 < M ∧
    ∀ xy, Active J xy →
      p0 ≤ hitProb (KhatResPair P_N rnk W) (dropSet P_N rnk W δ) M xy
```

together with a downstream split theorem saying that mass leaving `Active` before hitting `dropSet` is
absorbed by the boundary/center-tracking argument, not by `umass → 0`.  In other words, the final assembly
must consume:

1. active FK drop before exit, and
2. a separate bound that frozen/below-`J` boundary values have asymptotically negligible oscillation.

The existing code has neither:

- no `Active` predicate or finite killed-pair restriction for `KhatResPair` (search for `Fin (N+1)` /
  active-domain wrappers found no such module);
- no theorem proving KhatRes drift/QV/increment hypotheses on the active domain;
- no theorem transferring an active-only FK drop plus frozen-exit mass into the `hhit`/center-tracking
  conclusion.

## Why existing occupation bricks do not close it

`LocalizedOccupation.lean:30-39` is still global:

```lean
(hlvge : ∀ x, v0 ≤ locVar K D x)
(hcross : ∀ x, ...)
(hdrift_off : ∀ x, ...)
(hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b)
```

Those hypotheses fail on the killed boundary/frozen rows, where local variance is zero.  They also are
not instantiated for the concrete `KhatResPair` kernel.  The soft-tail truncation concern is not the
blocker here; the blocker is the absence of the active-domain state space/split theorem required by
spec8.

## Minimal next task

Build a new active-domain layer, not another all-start theorem:

1. Define the finite killed kernel on `Fin (N+1)` and its pair kernel.
2. Define `Active J` and prove the frozen-apart counter-rows are outside it.
3. Prove active-domain KhatRes moment inputs or a direct active hitting theorem for `dropSet`.
4. Prove a split lemma connecting active FK drop + below-`J` center tracking to the `hhit` interface.

Until that active/frozen split exists, applying `umass_tendsto_zero_of_uniform_drop_hit` to the killed
partition chain would require the false all-start hitting hypothesis above.
