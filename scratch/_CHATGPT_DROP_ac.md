# RC drain bound for `PEM_expected_allR_to_consensus`

## Main point

The exponential bound comes from using the wrong consequence of multiplicative drift.

For the paper-style reset-count drain, the potential

```lean
Φ(D) = ∑ w, 3 ^ resetcount(w)
```

should not be fed to an additive-drift theorem of the form `Φ₀ / (1-q)`. That theorem gives the exponential bound you observed:

```text
Φ₀ / δ ≈ n * 3^Rmax * n.
```

The paper-style use is the **logarithmic multiplicative drift theorem**:

```text
if    E[Φ_{t+1} | Φ_t] ≤ (1 - δ) Φ_t
then  E[τ] ≤ (log Φ₀ + O(1)) / δ.
```

With `δ = 2 / (3*n)` and `Φ₀ ≤ n * 3^Rmax`, this gives

```text
E[τ] ≤ (3*n/2) * (log n + Rmax * log 3 + O(1)).
```

When the protocol chooses `Rmax = Θ(log n)`, this is `O(n * Rmax)` interactions. This is the tight paper-style RC-drain estimate.

For your target theorem, however,

```lean
expectedHittingTime P hn2 D IsConsensusConfig ≤ ((3 * Rmax * n * n : ℕ) : ENNReal)
```

you do not need the logarithmic multiplicative theorem. A simpler lexicographic additive potential gives the required `O(Rmax * n^2)` interaction bound and is much easier to formalize in Lean.

---

## Warning about the theorem signature

As written, the theorem is still too strong if `Rmax = 0`.

If `Rmax = 0`, the RHS is `0`, but an all-Resetting configuration with `resetcount = 0` still has to pass through the dormant/reset/ranking/swap/decision phases unless it is already consensus. So add one of:

```lean
(hRmax_pos : 0 < Rmax)
```

or weaken the target to something like:

```lean
((3 * (Rmax + 1) * n * n : ℕ) : ENNReal)
```

For the protocol value `Rmax = 60 * log n`, positivity is automatic, but Lean will need the assumption or a bundled definition that implies it.

---

## Recommended Lean route for the stated `3 * Rmax * n^2` bound

Use a **max-level/count lexicographic potential**, not `Σ 3^rc`.

Define:

```lean
noncomputable def rcMax (D : Config n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun w => (D w).1.resetcount

noncomputable def rcMaxCount (D : Config n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun w =>
    (D w).1.resetcount = rcMax D).card

noncomputable def rcDrainRank (D : Config n) : ℕ :=
  if rcMax D = 0 then
    0
  else
    rcMax D * n + rcMaxCount D
```

The idea is:

* `rcMax D` is the current maximum resetcount.
* `rcMaxCount D` is the number of agents currently at that maximum.
* If an interaction touches a max-resetcount agent, then either the number of max agents decreases, or the maximum level itself decreases.
* The expression `rcMax * n + rcMaxCount` handles the case where the maximum level drops and the new max-count jumps upward.

The key deterministic transition lemmas should be:

```lean
lemma rcDrainRank_step_le
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    {i j : Fin n} (hij : i ≠ j) :
    rcDrainRank (D.step P i j) ≤ rcDrainRank D := by
  -- Use the Resetting/Resetting transition:
  -- both selected resetcounts become
  --   max (rc_i - 1) (rc_j - 1)
  -- and all other resetcounts are unchanged.
  -- If neither selected agent has rcMax, max/count are unchanged.
  -- If a max agent is selected, no new rcMax is created.
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
  -- If max-count is ≥ 2, touching a max removes at least one current max.
  -- If max-count is 1, the maximum level drops from M to ≤ M-1;
  -- the new count is at most n, so
  --   (M-1) * n + newCount ≤ M * n < M * n + 1.
  sorry
```

Initial bound:

```lean
lemma rcDrainRank_initial_le
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    rcDrainRank D ≤ Rmax * n + n := by
  -- rcMax ≤ Rmax and rcMaxCount ≤ n.
  sorry
```

If `0 < Rmax`, then:

```lean
lemma rcDrainRank_initial_le_two
    (hRmax_pos : 0 < Rmax)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax) :
    rcDrainRank D ≤ 2 * Rmax * n := by
  have h₁ := rcDrainRank_initial_le (D := D) hRCBound
  -- since n ≤ Rmax * n when 0 < Rmax
  omega
```

---

## Probabilistic descent lemma to add

Your existing deterministic lemma likely gives `φ₀ * n * (n-1)` because it only uses the existence of one good ordered pair.

Here we need the fact that **many** ordered pairs are good: every ordered pair touching a current-max agent is good.

Add this general theorem:

```lean
theorem expectedHittingTime_le_of_uniform_good_descent
    {φ : Config n → ℕ} {Target : Set (Config n)}
    (hzero : ∀ C, φ C = 0 ↔ C ∈ Target)
    (hmono : ∀ C i j, i ≠ j →
      φ (C.step P i j) ≤ φ C)
    (hgood_card : ∀ C, C ∉ Target →
      K ≤ ((orderedPairs n).filter fun ij =>
        φ (C.step P ij.1 ij.2) + 1 ≤ φ C).card)
    (hKpos : 0 < K) :
    expectedHittingTime P hn2 C Target
      ≤ ((φ C * (n * (n - 1)) / K : ℕ) : ENNReal) := by
  -- Same proof as deterministic descent, but use probability K/(n*(n-1))
  -- instead of 1/(n*(n-1)).
  sorry
```

For this protocol, use:

```lean
K = 2 * (n - 1)
```

because if `m ≥ 1` agents have current maximum resetcount, the number of ordered pairs touching at least one of them is

```text
n*(n-1) - (n-m)*(n-m-1) = m * (2*n - m - 1) ≥ 2*(n-1).
```

Formal lemma:

```lean
lemma card_orderedPairs_touching_rcMax_ge
    (hpos : 0 < rcMax D) :
    2 * (n - 1) ≤
      ((orderedPairs n).filter fun ij =>
        (D ij.1).1.resetcount = rcMax D ∨
        (D ij.2).1.resetcount = rcMax D).card := by
  -- Let A = {w | rc(w) = rcMax D}; hpos implies A.Nonempty.
  -- Count complement pairs where neither endpoint is in A.
  -- Or inject `{other : Fin n // other ≠ a}` into pairs `(a, other)` and `(other, a)`
  -- for a fixed max agent `a`.
  sorry
```

Then the one-step good descent cardinality follows from `rcDrainRank_step_drop_of_touches_max`.

---

## RC drain bound obtained from the lexicographic potential

Define the target for the drain phase:

```lean
def AllResetcountZero (D : Config n) : Prop :=
  ∀ w, (D w).1.resetcount = 0
```

Then prove:

```lean
lemma expected_allR_to_all_rc_zero
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax)
    (hRmax_pos : 0 < Rmax) :
    expectedHittingTime P hn2 D AllResetcountZero
      ≤ ((Rmax * n * n : ℕ) : ENNReal) := by
  classical

  have hφ0 : rcDrainRank D ≤ 2 * Rmax * n :=
    rcDrainRank_initial_le_two (D := D) hRmax_pos hRCBound

  have h :=
    expectedHittingTime_le_of_uniform_good_descent
      (φ := rcDrainRank)
      (Target := {C | AllResetcountZero C})
      -- hzero, hmono, hgood_card, hKpos

  -- h gives roughly:
  --   Eτ ≤ rcDrainRank D * n*(n-1) / (2*(n-1))
  --      ≤ rcDrainRank D * n / 2
  --      ≤ Rmax * n * n
  -- Use ENNReal coercion monotonicity plus Nat arithmetic.
  nlinarith
```

This is the cleanest route for your stated theorem. It avoids logs, avoids exponential constants, and gives a stronger drain-phase bound than the `3 * Rmax * n^2` budget.

---

## Paper-tight alternative: logarithmic multiplicative drift

If you want the actual paper-style `O(n * Rmax)` interactions for the RC drain, add a logarithmic multiplicative-drift theorem.

Use the zero-at-target exponential potential:

```lean
noncomputable def rcExpPot (D : Config n) : ℕ :=
  ∑ w : Fin n, (3 : ℕ) ^ (D w).1.resetcount - 1
```

The selected pair contribution decreases by at least one third of its current contribution, hence:

```lean
lemma rcExpPot_mul_drift
    (hAllR : ∀ w, (D w).1.role = .Resetting) :
    expectedOneStep P D rcExpPot
      ≤ (1 - (2 : ℝ) / (3 * n)) * rcExpPot D := by
  -- For ordered uniform scheduler,
  --   E[selected pair contribution] = (2/n) * rcExpPot D.
  -- A selected pair with positive contribution loses at least 1/3 of that pair contribution.
  sorry
```

Then prove/use:

```lean
theorem expectedHittingTime_le_of_multiplicative_drift_log
    {φ : Config n → ℕ} {Target : Set (Config n)}
    (hzero : ∀ C, φ C = 0 ↔ C ∈ Target)
    (hmin : ∀ C, C ∉ Target → 1 ≤ φ C)
    (hstep : ∀ C, C ∉ Target →
      expectedOneStep P C φ ≤ (1 - δ) * φ C)
    (hδ : 0 < δ) :
    expectedHittingTime P hn2 C Target
      ≤ ((Real.log (φ C) + 1) / δ : ℝ≥0∞) := by
  -- Standard proof: multiplicative decay of E[φ_t], Markov tail bound,
  -- and summing the tail probabilities.
  sorry
```

For the drain:

```lean
rcExpPot D ≤ n * (3 ^ Rmax - 1)
```

so:

```text
Eτ ≤ (3*n/2) * (log n + Rmax * log 3 + O(1)).
```

This is the mechanism behind the non-exponential paper bound. The exponential result came from applying additive drift to an exponential potential instead of applying multiplicative drift in its logarithmic form.

---

## How to use this in `PEM_expected_allR_to_consensus`

After the drain lemma, chain phases by the strong Markov / hitting-time composition lemma you probably already have:

```lean
lemma PEM_expected_allR_to_consensus
    (hAllR : ∀ w, (D w).1.role = .Resetting)
    (hAllCorrect : ∀ w, (D w).1.answer = majorityAnswer D)
    (hRCBound : ∀ w, (D w).1.resetcount ≤ Rmax)
    (hTimerBound : IsTimerBoundedConfig (7 * (Rmax + 4)) D)
    (hRmax_pos : 0 < Rmax) :
    expectedHittingTime P hn2 D IsConsensusConfig
      ≤ ((3 * Rmax * n * n : ℕ) : ENNReal) := by
  -- 1. Drain resetcounts using `expected_allR_to_all_rc_zero`.
  -- 2. From all Resetting + rc=0 + timer bound, use dormant countdown/reset bound.
  -- 3. Use existing ranking bound.
  -- 4. Use existing swap/sort bound.
  -- 5. Use decision/median correctness using `hAllCorrect`.
  -- 6. Add the bounds with the hitting-time composition lemma.
  --
  -- The RC drain budget can be ≤ Rmax*n*n.
  -- The remaining phases must fit inside the remaining `2*Rmax*n*n`,
  -- which requires `0 < Rmax` or a `(Rmax+1)` target.
  sorry
```

Bottom line:

* For the **paper-tight** reset drain: prove a logarithmic multiplicative-drift theorem for `Σ (3^rc - 1)`.
* For your **current Lean theorem** with RHS `3 * Rmax * n^2`: use the lexicographic max/count potential `rcMax * n + rcMaxCount` and a good-pair additive drift lemma with `K = 2*(n-1)` good ordered pairs.
