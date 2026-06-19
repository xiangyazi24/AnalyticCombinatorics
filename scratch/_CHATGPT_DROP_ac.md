# Q1 (ac): RC drain bound for `PEM_expected_allR_to_consensus`

## Short answer

The paper does **not** get the reset-count drain bound by applying an additive hitting-time theorem of the form

```text
E[τ] ≤ Φ₀ / δ
```

to the exponential potential. That would indeed give an exponential bound.

It uses the exponential potential with a **logarithmic multiplicative-drift** argument. Equivalently, the progress measure is the logarithm of the exponential potential, or the ratio of the current potential to the target threshold.

For reset counts, let

```lean
Φ(D) = ∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount
```

and stop the RC-drain phase once all resetcounts are zero. At that target,

```text
Φ = n.
```

If initially every resetcount is at most `Rmax`, then

```text
Φ₀ ≤ n * 3^Rmax.
```

Thus the relevant logarithmic range is not `Φ₀`; it is

```text
log (Φ₀ / n) ≤ Rmax * log 3.
```

With the paper drift

```text
E[Φ_{t+1} | C_t] ≤ (1 - 2/(3n)) * Φ_t
```

before the drain target, logarithmic multiplicative drift gives

```text
E[τ_RC] ≤ O((log (Φ₀/n)) / (2/(3n))) = O(n * Rmax)
```

interactions.

That is the missing step: **multiplicative drift gives a logarithmic hitting-time bound, not `Φ₀ / δ`.**

---

## A Lean theorem to add: thresholded logarithmic multiplicative drift

Your existing theorem

```lean
expectedHittingTime_le_of_multiplicative_drift
```

apparently gives the additive-style bound `Φ₀ * (1-q)⁻¹`. That is the wrong interface for this lemma.

Add a theorem with a positive threshold `B`:

```lean
theorem expectedHittingTime_le_of_multiplicative_drift_log_threshold
    {φ : Config n → ℝ}
    {Target : Set (Config n)}
    (B δ : ℝ)
    (hφ_nonneg : ∀ C, 0 ≤ φ C)
    (hB_pos : 0 < B)
    (hδ_pos : 0 < δ)
    (hδ_le_one : δ ≤ 1)
    (hTarget_of_small : ∀ C, φ C ≤ B → C ∈ Target)
    (hDrift : ∀ C, C ∉ Target →
      expectedOneStep P C φ ≤ (1 - δ) * φ C) :
    expectedHittingTime P hn2 C Target
      ≤ ENNReal.ofReal ((Real.log (φ C / B) + 1) / δ) := by
  -- Standard proof:
  -- 1. Show `E[φ_t] ≤ (1 - δ)^t * φ C` until hitting `Target`.
  -- 2. If `τ > t`, then `C_t ∉ Target`, so `φ C_t > B`.
  -- 3. Markov:
  --      Pr[τ > t] ≤ E[φ_t] / B ≤ (1 - δ)^t * φ C / B.
  -- 4. Sum the tail bound using the usual logarithmic split.
  --
  -- A slightly cleaner bound uses `-Real.log (1 - δ)` instead of `δ`:
  --      (Real.log (φ C / B) + 1) / (-Real.log (1 - δ))
  -- then use `δ ≤ -log(1-δ)`.
  sorry
```

For the RC drain, instantiate

```lean
B = n
δ = 2 / (3 * n)
φ = fun D => ∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount
Target = {D | ∀ w, (D w).1.resetcount = 0}
```

The target-threshold implication is exact:

```lean
lemma all_zero_of_rcExpPot_le_n
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hΦ : (∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount) ≤ n) :
    ∀ w : Fin n, (D w).1.resetcount = 0 := by
  -- Each term is at least 1.
  -- If some resetcount is positive, its term is at least 3,
  -- so the sum is at least n + 2, contradiction.
  sorry
```

Initial range:

```lean
lemma rcExpPot_initial_le
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    (∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount)
      ≤ n * (3 : ℝ) ^ Rmax := by
  -- pointwise monotonicity of `k ↦ 3^k`, then sum bound
  sorry
```

Then:

```lean
lemma expected_allR_to_all_rc_zero_log
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    expectedHittingTime P hn2 D {C | ∀ w : Fin n, (C w).1.resetcount = 0}
      ≤ ENNReal.ofReal ((Rmax * Real.log 3 + 1) / ((2 : ℝ) / (3 * n))) := by
  -- Apply `expectedHittingTime_le_of_multiplicative_drift_log_threshold`.
  -- Use:
  --   φ(D) ≤ n * 3^Rmax
  -- so:
  --   log (φ(D) / n) ≤ log (3^Rmax) = Rmax * log 3.
  sorry
```

This is the paper-tight framework.

---

## RC drift lemma for the paper potential

The local drift lemma should be stated for the thresholded exponential potential:

```lean
noncomputable def rcExpPot (D : Config n) : ℝ :=
  ∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount
```

```lean
lemma rcExpPot_mul_drift
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hNotDone : ¬ (∀ w : Fin n, (D w).1.resetcount = 0)) :
    expectedOneStep P D rcExpPot
      ≤ (1 - (2 : ℝ) / (3 * n)) * rcExpPot D := by
  -- Paper Lemma 3.3 style calculation.
  -- For a Resetting/Resetting interaction, if the selected pair has
  -- resetcounts `x,y > 0`, then both become roughly `max (x-1) (y-1)`.
  -- The exponential `3^rc` makes this a constant-factor loss on the
  -- selected pair's contribution.
  -- Averaging over ordered uniform interactions gives a loss of order `1/n`.
  sorry
```

If the exact inequality is hard with raw `Σ 3^rc`, use the normalized threshold version:

```lean
noncomputable def rcExpPotRatio (D : Config n) : ℝ :=
  (∑ w : Fin n, (3 : ℝ) ^ (D w).1.resetcount) / n
```

Then the target is `rcExpPotRatio D ≤ 1`, and the initial value is at most `3^Rmax`.

---

## Easier Lean route for the stated `3 * Rmax * n^2` theorem

For your theorem, you do **not** need the tight `O(n * Rmax)` drain. The bound allows `O(Rmax * n^2)`. The simplest formalization is a max-level/count additive potential.

```lean
noncomputable def rcMax (D : Config n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun w => (D w).1.resetcount

noncomputable def rcMaxCount (D : Config n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun w =>
    (D w).1.resetcount = rcMax D).card

noncomputable def rcDrainRank (D : Config n) : ℕ :=
  if rcMax D = 0 then 0 else rcMax D * n + rcMaxCount D
```

Key deterministic lemmas:

```lean
lemma rcDrainRank_step_le
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    {i j : Fin n} (hij : i ≠ j) :
    rcDrainRank (D.step P i j) ≤ rcDrainRank D := by
  -- Resetting/Resetting interactions do not increase the max resetcount.
  -- If the max level is unchanged, the number of max-level agents does not increase.
  sorry
```

```lean
lemma rcDrainRank_step_drop_of_touches_max
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hpos : 0 < rcMax D)
    {i j : Fin n} (hij : i ≠ j)
    (htouch : (D i).1.resetcount = rcMax D ∨
              (D j).1.resetcount = rcMax D) :
    rcDrainRank (D.step P i j) + 1 ≤ rcDrainRank D := by
  -- If a max-level agent is touched, either max-count decreases,
  -- or the max level itself drops. The factor `* n` absorbs the possible
  -- jump in the new max-count after a level drop.
  sorry
```

Initial bound:

```lean
lemma rcDrainRank_initial_le
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    rcDrainRank D ≤ Rmax * n + n := by
  -- `rcMax D ≤ Rmax`, and `rcMaxCount D ≤ n`.
  sorry
```

If you keep the exact theorem RHS `3 * Rmax * n * n`, add positivity:

```lean
(hRmax_pos : 0 < Rmax)
```

because when `Rmax = 0`, the RHS is zero even though the later phases may still require interactions.

With `0 < Rmax`:

```lean
lemma rcDrainRank_initial_le_two
    (hRmax_pos : 0 < Rmax)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    rcDrainRank D ≤ 2 * Rmax * n := by
  have h := rcDrainRank_initial_le (D := D) hRCBound
  -- since `n ≤ Rmax * n`
  omega
```

Now strengthen the additive hitting-time lemma to exploit many good ordered pairs:

```lean
theorem expectedHittingTime_le_of_good_pair_descent
    {φ : Config n → ℕ} {Target : Set (Config n)}
    (K : ℕ)
    (hK_pos : 0 < K)
    (hzero : ∀ C, φ C = 0 ↔ C ∈ Target)
    (hmono : ∀ C i j, i ≠ j → φ (C.step P i j) ≤ φ C)
    (hgood : ∀ C, C ∉ Target →
      K ≤ ((orderedPairs n).filter fun ij =>
        φ (C.step P ij.1 ij.2) + 1 ≤ φ C).card) :
    expectedHittingTime P hn2 C Target
      ≤ ((φ C * (n * (n - 1)) / K : ℕ) : ENNReal) := by
  -- Same proof as deterministic descent, but the one-step descent
  -- probability is at least `K / (n*(n-1))`.
  sorry
```

For RC drain, use

```lean
K = 2 * (n - 1)
```

because outside the target there is at least one max-resetcount agent, and all ordered pairs touching that agent are good.

```lean
lemma rcDrain_good_pair_card
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hNotDone : ¬ (∀ w : Fin n, (D w).1.resetcount = 0)) :
    2 * (n - 1) ≤
      ((orderedPairs n).filter fun ij =>
        rcDrainRank (D.step P ij.1 ij.2) + 1 ≤ rcDrainRank D).card := by
  -- Choose one agent `a` with resetcount `rcMax D`.
  -- The `2*(n-1)` ordered pairs `(a,x)` and `(x,a)`, `x ≠ a`,
  -- are all good by `rcDrainRank_step_drop_of_touches_max`.
  sorry
```

Then:

```lean
lemma expected_allR_to_all_rc_zero_quad
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax)
    (hRmax_pos : 0 < Rmax) :
    expectedHittingTime P hn2 D {C | ∀ w : Fin n, (C w).1.resetcount = 0}
      ≤ ((Rmax * n * n : ℕ) : ENNReal) := by
  classical

  have hφ0 : rcDrainRank D ≤ 2 * Rmax * n :=
    rcDrainRank_initial_le_two (D := D) hRmax_pos hRCBound

  have h :=
    expectedHittingTime_le_of_good_pair_descent
      (P := P) (hn2 := hn2)
      (φ := rcDrainRank)
      (Target := {C | ∀ w : Fin n, (C w).1.resetcount = 0})
      (K := 2 * (n - 1))
      -- hK_pos, hzero, hmono, hgood

  -- h gives:
  --   Eτ ≤ rcDrainRank D * n*(n-1) / (2*(n-1))
  --      ≤ rcDrainRank D * n / 2
  --      ≤ Rmax * n * n.
  sorry
```

---

## Final theorem shape

```lean
theorem PEM_expected_allR_to_consensus
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w, (D w).1.answer = majorityAnswer D)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax)
    (hTimerBound : IsTimerBoundedConfig (7 * (Rmax + 4)) D)
    (hRmax_pos : 0 < Rmax) :
    expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((3 * Rmax * n * n : ℕ) : ENNReal) := by
  -- 1. RC drain: `expected_allR_to_all_rc_zero_quad` gives ≤ Rmax*n*n.
  -- 2. Dormant/reset phase from rc=0 using `hTimerBound`.
  -- 3. Ranking recruitment.
  -- 4. Swap/sort.
  -- 5. Decision/median correctness using `hAllCorrect`.
  -- 6. Chain phase bounds with the hitting-time composition lemma.
  sorry
```

If you do not want to add `hRmax_pos`, weaken the target to `(Rmax + 1)`.

## Bottom line

* The paper's tight drain bound is logarithmic multiplicative drift on `Σ 3^rc`, stopped at threshold `n`, giving `O(n * Rmax)` interactions.
* Your existing multiplicative theorem gives the wrong additive-style consequence and therefore looks exponential.
* For the current Lean theorem with `3 * Rmax * n^2`, the easiest proof is the max/count additive potential `rcMax * n + rcMaxCount`, plus a good-pair descent lemma.
