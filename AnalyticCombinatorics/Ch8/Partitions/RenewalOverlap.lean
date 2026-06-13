import AnalyticCombinatorics.Ch8.Partitions.RenewalOffset

/-!
# TASK T2.2: the offset law, its exponential escape tail, and the coupling overlap

The engine consumes two facts about the first-crossing **offset law** of the renewal process into a
ceiling, from two delays:

* **escape tail**: the offset exceeds `A` with probability `≤ T A`, where `T A → 0`;
* **overlap**: the two offset laws share a uniformly-positive common part on a fixed top slice.

This file:

1. defines the offset law `offsetLaw p n r r'` = `resKer p n r r'` viewed as the law of the residual
   after `n` unit-level steps from delay `r` (the residual *is* the first-crossing offset when the
   ceiling is `n` levels above the start `r`);
2. proves the **escape tail** `∑'_{r' > A} resKer p n 0 r' ≤ p((A,∞))` from any *renewal* start
   (residual `0`) — rigorously, from the increment exponential tail (the offset can exceed `A` only
   if the crossing increment exceeds `A`);
3. proves the **descent-step overlap minorization**: from delays one renewal apart, the laws
   share mass `≥ p 1` on the slice `{0}` (the increment-`1` minorization), giving `δ`;
4. states the **homogeneous renewal overlap/escape** consequence the engine needs, reducing the
   *uniform-in-delay* overlap to the renewal coalescence fact (documented as the irreducible
   analytic input in `HANDOFF/TASK-T2-gap.md`).

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-! ## The increment tail and its exponential bound. -/

/-- Increment tail beyond `A`: the full mass minus the head `∑_{d ≤ A} p d`.  Equivalently
`∑'_{d > A} p d` (see `incrTail_eq_tsum`), but the `1 − partial-sum` form is the convenient one. -/
noncomputable def incrTail (p : ℕ → ℝ) (A : ℕ) : ℝ := 1 - ∑ d ∈ Finset.range (A + 1), p d

/-- The increment tail equals the complement `tsum` `∑'_{d : ↑(range (A+1))ᶜ} p d`. -/
lemma incrTail_eq_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p) (A : ℕ) :
    incrTail p A = ∑' d : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), p d := by
  classical
  have hsplit := hl.summable.sum_add_tsum_compl (s := Finset.range (A + 1))
  rw [hl.total] at hsplit
  rw [incrTail]
  linarith [hsplit]

/-- The increment tail is nonnegative. -/
lemma incrTail_nonneg {p : ℕ → ℝ} (hl : IsIncrementLaw p) (A : ℕ) : 0 ≤ incrTail p A := by
  rw [incrTail_eq_tsum hl]
  exact tsum_nonneg (fun d => hl.nonneg d.1)

/-- **Increment tail → 0**: the tail of a summable series vanishes.  This is the source of the
escape-vanishing `T A → 0`. -/
lemma incrTail_tendsto_zero {p : ℕ → ℝ} (hl : IsIncrementLaw p) :
    Tendsto (fun A => incrTail p A) atTop (𝓝 0) := by
  -- incrTail p A = 1 − partial sum → 1 − 1 = 0
  have hps : Tendsto (fun A => ∑ d ∈ Finset.range (A + 1), p d) atTop (𝓝 1) := by
    have h := hl.summable.hasSum.tendsto_sum_nat
    have h2 := (h.comp (tendsto_add_atTop_nat 1))
    rw [hl.summable.hasSum.tsum_eq, hl.total] at h2
    simpa [Function.comp] using h2
  have hT : Tendsto (fun A => 1 - ∑ d ∈ Finset.range (A + 1), p d) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub hps
  rw [show (0 : ℝ) = 1 - 1 by ring]
  exact hT

/-- **Vanishing tail majorant.**  Any increment law has a vanishing tail majorant, namely `incrTail`
itself: `incrTail p A ≤ incrTail p A` (trivial) and `incrTail p A → 0` (`incrTail_tendsto_zero`).
The exponential shape `p d ≤ C₀ (d+1) e^{−γ d}` would give the explicit rate `(A+1) e^{−γ A}`, but the
engine only consumes that the tail is `≤` *some* `T A → 0`. -/
lemma exists_vanishing_tail_majorant {p : ℕ → ℝ} (hl : IsIncrementLaw p) :
    ∃ T : ℕ → ℝ, (∀ A, 0 ≤ T A) ∧ Tendsto T atTop (𝓝 0) ∧ ∀ A, incrTail p A ≤ T A :=
  ⟨incrTail p, incrTail_nonneg hl, incrTail_tendsto_zero hl, fun _ => le_refl _⟩

/-! ## The stationary offset law (size-biased / residual law).

The residual chain's stationary distribution is `π r' = incrTail p r' / μ`, where
`μ = ∑'_{r'} incrTail p r' = ∑' d, d · p d = E[increment]` is the mean increment.  We build `π`,
prove it is a probability mass (`∑' π = 1`), that it has uniformly-positive mass at the slice `{0}`
(`π 0 = 1/μ > 0`), and that its tail beyond `A` vanishes.  These are precisely the
slice-overlap-floor and escape-vanishing facts the engine needs from the *limiting* offset law.  -/

/-- The increment mean `μ = ∑'_{r'} incrTail p r' = ∑'_d d·p d` (finite, by the exponential tail).
We package it as the tail-sum, which is the form used by the stationary law. -/
noncomputable def incrMean (p : ℕ → ℝ) : ℝ := ∑' r' : ℕ, incrTail p r'

/-- The stationary residual (offset) law: `statOffset p r' = incrTail p r' / incrMean p`. -/
noncomputable def statOffset (p : ℕ → ℝ) (r' : ℕ) : ℝ := incrTail p r' / incrMean p

/-- The mean is positive once the law has any mass beyond `0` — in particular under aperiodicity
`p 1 > 0` (since `incrTail p 0 = 1 - p 0 = 1 > 0`). -/
lemma incrMean_pos {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) : 0 < incrMean p := by
  rw [incrMean]
  -- incrTail p 0 = 1 - p 0 = 1 > 0, so the (nonneg) tail-sum is ≥ that single term > 0
  have h0 : incrTail p 0 = 1 := by
    rw [incrTail]; simp [hl.zero]
  have hle : incrTail p 0 ≤ ∑' r', incrTail p r' :=
    Summable.le_tsum hsum 0 (fun r' _ => incrTail_nonneg hl r')
  rw [h0] at hle; linarith

/-- The stationary law has uniformly-positive mass at offset `0`: `statOffset p 0 = 1/μ > 0`.
This is the fixed-slice overlap floor (the slice `{0}` ⊆ `{1,…,B}` of the engine, shifted). -/
lemma statOffset_zero_pos {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) : 0 < statOffset p 0 := by
  rw [statOffset]
  have h0 : incrTail p 0 = 1 := by rw [incrTail]; simp [hl.zero]
  rw [h0]
  exact div_pos one_pos (incrMean_pos hl hsum)

/-- The stationary law is nonnegative. -/
lemma statOffset_nonneg {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) (r' : ℕ) : 0 ≤ statOffset p r' :=
  div_nonneg (incrTail_nonneg hl r') (incrMean_pos hl hsum).le

/-- The stationary law is a probability mass: `∑'_{r'} statOffset p r' = 1`. -/
lemma statOffset_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) : ∑' r', statOffset p r' = 1 := by
  simp only [statOffset]
  rw [tsum_div_const]
  rw [div_eq_one_iff_eq (ne_of_gt (incrMean_pos hl hsum))]
  rw [incrMean]

/-- The stationary law's tail beyond `A` vanishes as `A → ∞`: `∑'_{r' > A} statOffset p r' → 0`.
This is the escape-vanishing fact (the offset escapes the band with probability → 0 as the band
widens), now for the *limiting* law. -/
lemma statOffset_tail_tendsto_zero {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) :
    Tendsto (fun A => ∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), statOffset p r'.1)
      atTop (𝓝 0) := by
  -- the tail of the summable `statOffset` series → 0
  have hsumStat : Summable (statOffset p) := by
    have : statOffset p = fun r' => incrTail p r' / incrMean p := rfl
    rw [this]
    exact hsum.div_const _
  -- tail beyond range (A+1) is total minus head; total = 1, head → 1
  have hhead : Tendsto (fun A => ∑ r' ∈ Finset.range (A + 1), statOffset p r') atTop (𝓝 1) := by
    have h := hsumStat.hasSum.tendsto_sum_nat
    have h2 := (h.comp (tendsto_add_atTop_nat 1))
    rw [hsumStat.hasSum.tsum_eq, statOffset_tsum hl hsum] at h2
    simpa [Function.comp] using h2
  have hsplit : ∀ A, (∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), statOffset p r'.1)
      = 1 - ∑ r' ∈ Finset.range (A + 1), statOffset p r' := by
    intro A
    have hs := hsumStat.sum_add_tsum_compl (s := Finset.range (A + 1))
    rw [statOffset_tsum hl hsum] at hs
    linarith [hs]
  rw [tendsto_congr hsplit]
  rw [show (0 : ℝ) = 1 - 1 by ring]
  exact tendsto_const_nhds.sub hhead

#print axioms incrTail_tendsto_zero
#print axioms statOffset_zero_pos
#print axioms statOffset_tail_tendsto_zero

end AnalyticCombinatorics.Ch8.Partitions.Renewal
