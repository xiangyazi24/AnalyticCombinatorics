import AnalyticCombinatorics.Ch8.Partitions.RenewalCore

/-!
# TASK T2.2: the overshoot/residual chain and its Doeblin coupling

The first-crossing offset of an integer renewal process is governed by the **residual chain**
(a.k.a. overshoot chain): the Markov chain on `ℕ` whose state is the current undershoot/residual
to the next ceiling.  Concretely, if the renewal increments have law `p` (supported on `{1,2,…}`),
the residual chain has transition

* from state `0` (just landed on the level): jump by an increment `d ∼ p`, leaving residual `d − 1`;
* from state `r+1` (residual `r+1` to the next level): deterministically step down to residual `r`.

So one *unit* of the level coordinate is one residual step.  The chain hits `0` exactly at renewal
epochs.  Crucially, the **stationary offset law** is the size-biased increment law, and two copies of
the residual chain from any two starting residuals couple by the Doeblin minorization coming from
`p 1 > 0` (an increment of `1` resets the residual to `0` regardless of the past).

This file builds the residual chain's one-step kernel `resStep`, its `n`-step kernel `resKer`,
the **return-to-zero-then-restart** structure, and the elementary facts (row-stochastic,
nonneg, support).  The Doeblin coupling / overlap + escape-tail conclusions are in
`RenewalOverlap.lean`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- **One-step residual kernel.**  `resStep p r r'` = probability that the residual chain moves from
state `r` to state `r'` in one *unit-level* step.

* From `0`: an increment `d = r' + 1 ∼ p` is drawn, leaving residual `r'` (so `resStep p 0 r' =
  p (r' + 1)`).
* From `r+1`: deterministic step down to `r` (so `resStep p (r+1) r' = [r' = r]`). -/
noncomputable def resStep (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun r' => p (r' + 1)
  | (r+1) => fun r' => if r' = r then 1 else 0

lemma resStep_zero (p : ℕ → ℝ) (r' : ℕ) : resStep p 0 r' = p (r' + 1) := rfl

lemma resStep_succ (p : ℕ → ℝ) (r r' : ℕ) :
    resStep p (r+1) r' = if r' = r then 1 else 0 := rfl

lemma resStep_nonneg {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (r r' : ℕ) : 0 ≤ resStep p r r' := by
  cases r with
  | zero => rw [resStep_zero]; exact hp _
  | succ r => rw [resStep_succ]; split <;> norm_num

/-- The residual kernel from `0` is summable (a reindex of `p`). -/
lemma resStep_zero_summable {p : ℕ → ℝ} (hps : Summable p) :
    Summable (fun r' => resStep p 0 r') := by
  simp only [resStep_zero]
  exact (summable_nat_add_iff 1).2 hps

/-- Row-stochasticity of the residual kernel: each row sums (as a `tsum`) to `1`.  From `0` it is the
total increment mass `∑_{d≥1} p d = 1`; from `r+1` it is the point mass at `r`. -/
lemma resStep_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p) (r : ℕ) :
    ∑' r', resStep p r r' = 1 := by
  cases r with
  | zero =>
    simp only [resStep_zero]
    -- ∑'_{r'} p (r'+1) = (∑'_d p d) − p 0 = 1 − 0 = 1
    have hsplit : ∑' d : ℕ, p d = p 0 + ∑' r' : ℕ, p (r' + 1) :=
      hl.summable.tsum_eq_zero_add
    rw [hl.total, hl.zero, zero_add] at hsplit
    exact hsplit.symm
  | succ r =>
    simp only [resStep_succ]
    rw [tsum_eq_single r (by intro b hb; rw [if_neg hb])]
    simp

/-! ## Deterministic descent: the residual chain from `r+1` steps down to `r` with certainty. -/

/-- From a positive residual `r+1`, the next state is `r` deterministically: `resStep p (r+1) r = 1`. -/
lemma resStep_succ_self (p : ℕ → ℝ) (r : ℕ) : resStep p (r+1) r = 1 := by
  rw [resStep_succ, if_pos rfl]

/-- From a positive residual `r+1`, no other next state is reached. -/
lemma resStep_succ_of_ne (p : ℕ → ℝ) {r r' : ℕ} (h : r' ≠ r) : resStep p (r+1) r' = 0 := by
  rw [resStep_succ, if_neg h]

/-! ## The increment-`1` minorization: an increment of `1` from residual `0` returns to `0`. -/

/-- The single fact powering the Doeblin coupling: from residual `0`, drawing increment `1`
(probability `p 1`) lands back at residual `0`.  Together with the deterministic descent, this gives
a uniform positive probability of being at `0` at a controlled time. -/
lemma resStep_zero_to_zero (p : ℕ → ℝ) : resStep p 0 0 = p 1 := by
  rw [resStep_zero]

/-! ## The `n`-step residual kernel. -/

/-- `n`-step residual kernel.  `resKer p n r r'` = probability the residual chain moves from `r` to
`r'` in `n` unit-level steps. -/
noncomputable def resKer (p : ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun r r' => if r' = r then 1 else 0
  | (n+1) => fun r r' => ∑' m, resStep p r m * resKer p n m r'

@[simp] lemma resKer_zero (p : ℕ → ℝ) (r r' : ℕ) :
    resKer p 0 r r' = if r' = r then 1 else 0 := rfl

lemma resKer_succ (p : ℕ → ℝ) (n r r' : ℕ) :
    resKer p (n+1) r r' = ∑' m, resStep p r m * resKer p n m r' := rfl

/-- **Deterministic descent.**  Starting at residual `r`, after exactly `r` unit-level steps the
chain is at residual `0` with probability `1`: `resKer p r r 0 = 1`.  Each step from a positive
residual `s+1` goes deterministically to `s`, so the path `r → r−1 → … → 0` carries all the mass. -/
lemma resKer_descent (p : ℕ → ℝ) (r : ℕ) : resKer p r r 0 = 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [resKer_succ]
    -- from r+1 the only one-step move is to r (mass 1); recurse with ih
    rw [tsum_eq_single r (by
      intro m hm
      rw [resStep_succ_of_ne p hm, zero_mul])]
    rw [resStep_succ_self, one_mul, ih]

/-- `resKer` is nonnegative. -/
lemma resKer_nonneg {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (n r r' : ℕ) : 0 ≤ resKer p n r r' := by
  induction n generalizing r with
  | zero => rw [resKer_zero]; split <;> norm_num
  | succ n ih =>
    rw [resKer_succ]
    exact tsum_nonneg (fun m => mul_nonneg (resStep_nonneg hp r m) (ih m))

/-- After descending to `0` (in `r` steps) then taking one increment step, the chain is at residual
`r'` with probability `p (r'+1)`: `resKer p (r+1) r r' = p (r'+1)`.  This carries the aperiodicity
minorization (`r' = 0 ↦ p 1`, `r' = 1 ↦ p 2`). -/
lemma resKer_descent_then_step (p : ℕ → ℝ) (r r' : ℕ) :
    resKer p (r+1) r r' = p (r' + 1) := by
  induction r with
  | zero =>
    -- one increment step from 0 lands at r' with prob p (r'+1)
    rw [resKer_succ]
    rw [tsum_eq_single r' (by
      intro m hm
      rw [resKer_zero, if_neg (by omega : ¬ r' = m), mul_zero])]
    rw [resStep_zero, resKer_zero, if_pos rfl, mul_one]
  | succ s ih =>
    -- from s+1 the only one-step move is deterministically to s, then recurse via ih
    rw [resKer_succ]
    rw [tsum_eq_single s (by
      intro m hm
      rw [resStep_succ_of_ne p hm, zero_mul])]
    rw [resStep_succ_self, one_mul, ih]

#print axioms resKer_descent
#print axioms resKer_descent_then_step
#print axioms resStep_tsum

end AnalyticCombinatorics.Ch8.Partitions.Renewal
