# TASK #6 gap: final `hhit` cannot be wired from the current exported interfaces

Attempted target:

```lean
∀ᶠ J : ℕ in atTop, ∃ L : ℝ,
  Tendsto (fun n => hitVal Pker rnk J u n) atTop (𝓝 L)
```

The `muTilde` input is present:

- `AnalyticCombinatorics/Ch8/Partitions/MuTilde.lean:40`
  `muTilde_eq_drift`
- `AnalyticCombinatorics/Ch8/Partitions/MuNumAssembly.lean:1062`
  `muTilde_two_term`

The current blocker is the missing conditioned-residual active-occupation theorem connecting these facts to
the `Umat`/`umass` coupling.

## Exact missing fact

For the finite killed chain on `Fin (N+1)`, define the conditioned residual kernel

```lean
KhatRes x y a b =
  Kres P rnk W x y a b / (1 - cmass P rnk W x y)
```

on rows with `cmass < 1` (equivalently `Lres ⊗ Rres / (1 - cmass)^2`, with arbitrary harmless rows when
`cmass = 1`).  The missing theorem needs to prove, for a high-rank active predicate

```lean
GoodHi (x,y) :=
  Jhi ≤ rnk x ∧ Jhi ≤ rnk y ∧ |3*sqrt x - 3*sqrt y| ≤ Wρ
```

that the conditioned residual walk has unbounded expected occupation of `GoodHi` from comparable high
starts, and that this is the same `g(t)` needed by the coalescence bridge:

```lean
theorem khat_residual_active_good_occupation_tends_infty :
  ∀ A > 0, ∃ R0 M, ∀ i j,
    R0 ≤ rnk i → R0 ≤ rnk j →
    |3 * Real.sqrt (i : ℝ) - 3 * Real.sqrt (j : ℝ)| ≤ W0 →
      A ≤ ∑ t ∈ Finset.range M,
        ∑ xy, distPow (KhatRes J W N) (pairDelta i j) t xy *
          (if GoodHi Jhi Wρ xy then (1 : ℝ) else 0)
```

plus the bridge lemma:

```lean
g t =
  (∑ x, ∑ y, if GoodHi x y then Umat P rnk W i j t x y else 0)
    / umass P rnk W i j t
```

and

```lean
u(t+1) ≤ u(t) - δ * (u(t) * g(t))
```

so it can feed `umass_lt_of_occupation_unbounded`.

## Why the existing bricks do not close it

- `LocalizedOccupation.lean:30-39` proves unbounded occupation for a stochastic kernel under global
  hypotheses, including `∀ x, v0 ≤ locVar K D x` at line 33 and the hard bounded-increment support
  condition `K x z ≠ 0 → |D z - D x| ≤ b` at line 36.
- The killed/residual process for partitions is not in that shape globally. Low/absorbed rows have zero
  variance, while the raw Erdős predecessor kernel has soft far tails rather than a hard bounded support.
  The available tail estimates (`erdos_kernel_tail`, `weighted_far_erdos_tail_le`) do not provide a
  theorem converting those soft tails into the hard `hbinc` hypothesis or into an active-horizon
  occupation statement.
- `GoodHiRecursion.lean:30-34` gives the deterministic `umass` contraction for an arbitrary `Good`, and
  `CoalesceBridge.lean:22-27` consumes an abstract unbounded conditioned occupation sequence `g`.  What is
  missing is the theorem identifying the conditioned `distPow KhatRes` occupation with that `g` and proving
  it is unbounded for the concrete killed Erdős chain.
- `ITERCoupling.lean:52-54` defines only the substochastic `Kres`, whose row sum is `1 - cmass`; no
  exported `KhatRes` stochastic kernel or normalized-`Umat` evolution lemma currently exists.

Without this fact, proving `hhit` would require either adding an axiom/sorry or silently assuming the core
analytic probability statement.  I stopped here per the task constraint.
