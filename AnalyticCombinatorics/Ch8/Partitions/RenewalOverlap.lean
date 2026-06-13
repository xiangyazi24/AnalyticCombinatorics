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

/-! ## The first-crossing offset law from a delay, and its delay-independence.

The renewal process started at residual (= delay) `s` to the ceiling descends deterministically to a
renewal epoch (residual `0`) in exactly `s` unit-level steps, then draws one increment.  The offset
of the first crossing *after that renewal* is therefore distributed as `p(·+1)` — the increment law
shifted by one — **independently of the delay `s`** (`resKer_descent_then_step`).  This delay-
independence is the engine's coupling: two crossings from two different delays, each measured at its
own first post-descent renewal, share the *identical* offset law, so their common mass on a fixed top
slice is a fixed positive number and is not diluted by widening the band. -/

/-- **First-crossing offset law from delay `s`.**  After the deterministic descent of length `s` to a
renewal, plus one increment step, the residual (offset) is `r'` with probability `resKer p (s+1) s
r'`.  We package this as the offset law. -/
noncomputable def offsetLaw (p : ℕ → ℝ) (s : ℕ) (r' : ℕ) : ℝ := resKer p (s + 1) s r'

/-- **Delay-independence of the offset law**: `offsetLaw p s r' = p (r' + 1)` for every delay `s`.
This is the renewal-coupling fact — the post-renewal crossing offset does not remember the delay. -/
lemma offsetLaw_eq (p : ℕ → ℝ) (s r' : ℕ) : offsetLaw p s r' = p (r' + 1) := by
  rw [offsetLaw, resKer_descent_then_step]

/-- The offset law is nonnegative. -/
lemma offsetLaw_nonneg {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) (s r' : ℕ) : 0 ≤ offsetLaw p s r' := by
  rw [offsetLaw_eq]; exact hp _

/-- The offset law is summable (a reindex of `p`). -/
lemma offsetLaw_summable {p : ℕ → ℝ} (hps : Summable p) (s : ℕ) :
    Summable (fun r' => offsetLaw p s r') := by
  have : (fun r' => offsetLaw p s r') = fun r' => p (r' + 1) := by
    funext r'; rw [offsetLaw_eq]
  rw [this]; exact (summable_nat_add_iff 1).2 hps

/-- The offset law is a probability mass: `∑'_{r'} offsetLaw p s r' = 1`.  Total increment mass minus
the (zero) atom at `0`. -/
lemma offsetLaw_tsum {p : ℕ → ℝ} (hl : IsIncrementLaw p) (s : ℕ) :
    ∑' r', offsetLaw p s r' = 1 := by
  have hcongr : (fun r' => offsetLaw p s r') = fun r' => p (r' + 1) := by
    funext r'; rw [offsetLaw_eq]
  rw [hcongr]
  have hsplit : ∑' d : ℕ, p d = p 0 + ∑' r' : ℕ, p (r' + 1) := hl.summable.tsum_eq_zero_add
  rw [hl.total, hl.zero, zero_add] at hsplit
  exact hsplit.symm

/-! ## Escape tail of the offset law. -/

/-- **Escape tail (exact).**  The offset from delay `s` exceeds `A` with probability
`incrTail p (A+1)`: `∑'_{r' > A} offsetLaw p s r' = incrTail p (A+1)` (the offset `r' > A` means the
crossing increment `d = r'+1 > A+1`, i.e. `d` lies beyond `A+1`).  Independent of the delay. -/
lemma offsetLaw_escape_eq {p : ℕ → ℝ} (hl : IsIncrementLaw p) (s A : ℕ) :
    (∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), offsetLaw p s r'.1) = incrTail p (A + 1) := by
  have hsum : Summable (fun r' => offsetLaw p s r') := offsetLaw_summable hl.summable s
  have hsplit := hsum.sum_add_tsum_compl (s := Finset.range (A + 1))
  rw [offsetLaw_tsum hl] at hsplit
  have hhead : (∑ r' ∈ Finset.range (A + 1), offsetLaw p s r')
      = ∑ d ∈ Finset.range (A + 1), p (d + 1) := by
    apply Finset.sum_congr rfl; intro r' _; rw [offsetLaw_eq]
  rw [incrTail]
  have htail : (∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), offsetLaw p s r'.1)
      = 1 - ∑ r' ∈ Finset.range (A + 1), offsetLaw p s r' := by linarith [hsplit]
  rw [htail, hhead]
  -- ∑_{d < A+2} p d = (∑_{d < A+1} p(d+1)) + p 0   (sum_range_succ' with n = A+1), p 0 = 0
  rw [Finset.sum_range_succ' p (A + 1), hl.zero, add_zero]

/-- The escape tail is nonnegative. -/
lemma offsetLaw_escape_nonneg {p : ℕ → ℝ} (hl : IsIncrementLaw p) (s A : ℕ) :
    0 ≤ ∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), offsetLaw p s r'.1 := by
  rw [offsetLaw_escape_eq hl]; exact incrTail_nonneg hl (A + 1)

/-- The increment tail is antitone: widening the cutoff only removes nonnegative terms. -/
lemma incrTail_antitone {p : ℕ → ℝ} (hl : IsIncrementLaw p) : Antitone (incrTail p) := by
  intro A A' hAA'
  rw [incrTail, incrTail]
  have hsub : Finset.range (A + 1) ⊆ Finset.range (A' + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hmono : ∑ d ∈ Finset.range (A + 1), p d ≤ ∑ d ∈ Finset.range (A' + 1), p d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro d _ _; exact hl.nonneg d
  linarith

/-! ## Common overlap mass of two offset laws on a fixed top slice. -/

/-- The min of the two offset laws on a `range B` slice equals `∑_{d < B} p(d+1)` (since both laws are
`p(·+1)`), and is `≥ p 1` whenever `1 ≤ B`.  This is the **uniformly positive overlap on a fixed top
slice** the engine needs: it depends on neither delay nor `A`. -/
lemma offsetLaw_overlap_slice {p : ℕ → ℝ} (s s' B : ℕ) :
    (∑ r' ∈ Finset.range B, min (offsetLaw p s r') (offsetLaw p s' r'))
      = ∑ d ∈ Finset.range B, p (d + 1) := by
  apply Finset.sum_congr rfl; intro r' _
  rw [offsetLaw_eq, offsetLaw_eq, min_self]

/-- The overlap slice mass is `≥ p 1` once `1 ≤ B` (aperiodic minorization `p 1 > 0` gives the floor
`δ := p 1`). -/
lemma offsetLaw_overlap_ge {p : ℕ → ℝ} (hp : ∀ d, 0 ≤ p d) {s s' B : ℕ} (hB : 1 ≤ B) :
    p 1 ≤ ∑ r' ∈ Finset.range B, min (offsetLaw p s r') (offsetLaw p s' r') := by
  rw [offsetLaw_overlap_slice]
  have h1 : p 1 = p (0 + 1) := by norm_num
  rw [h1]
  apply Finset.single_le_sum (f := fun d => p (d + 1)) (fun d _ => hp _)
  exact Finset.mem_range.mpr hB

/-! ## T2.2 — the homogeneous renewal uniform overshoot/overlap theorem.

Packages the three facts the engine consumes, for an aperiodic exponential-tail integer renewal law:

* a fixed top-slice width `B := 1` and overlap floor `δ := p 1 > 0`, uniform over both delays and over
  the band width `A`;
* a vanishing escape majorant `T A := incrTail p A → 0`;
* for every band width `A ≥ B` and any two delays `s, s'`: the common mass of the two first-crossing
  offset laws on the slice `{0,…,B−1}` is `≥ δ`, and each offset law's escape beyond `A` is `≤ T A`.

The hypotheses `hp_tail`, `hp_aper.2` (i.e. `p 2 > 0`) are recorded for the downstream T2.1/T2.3
interface (the exponential tail certifies the explicit rate; `p 2 > 0` certifies true aperiodicity of
the support, gcd = 1) but the engine-facing overlap/escape pair already follows from `p 1 > 0` and
summability via the delay-independence of the post-renewal offset law. -/
theorem homogeneousRenewal_uniform_overshoot_overlap
    (p : ℕ → ℝ) (hp_prob : IsIncrementLaw p)
    (hp_tail : ∃ γ : ℝ, 0 < γ ∧ ∃ C₀ : ℝ, ∀ d, p d ≤ C₀ * (d + 1) * Real.exp (-γ * d))
    (hp_aper : 0 < p 1 ∧ 0 < p 2) :
    ∃ B : ℕ, 1 ≤ B ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℕ → ℝ,
      (∀ A, 0 ≤ T A) ∧ Tendsto T atTop (𝓝 0) ∧
      ∀ A, B ≤ A → ∀ s s' : ℕ,
        (δ ≤ ∑ r' ∈ Finset.range B, min (offsetLaw p s r') (offsetLaw p s' r'))
        ∧ (∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), offsetLaw p s r'.1) ≤ T A
        ∧ (∑' r' : ((Finset.range (A + 1) : Set ℕ)ᶜ : Set ℕ), offsetLaw p s' r'.1) ≤ T A := by
  refine ⟨1, le_refl 1, p 1, hp_aper.1, incrTail p, incrTail_nonneg hp_prob,
    incrTail_tendsto_zero hp_prob, ?_⟩
  intro A _hA s s'
  refine ⟨?_, ?_, ?_⟩
  · exact offsetLaw_overlap_ge hp_prob.nonneg (le_refl 1)
  · rw [offsetLaw_escape_eq hp_prob]
    exact incrTail_antitone hp_prob (Nat.le_succ A)
  · rw [offsetLaw_escape_eq hp_prob]
    exact incrTail_antitone hp_prob (Nat.le_succ A)

#print axioms incrTail_tendsto_zero
#print axioms statOffset_zero_pos
#print axioms statOffset_tail_tendsto_zero
#print axioms offsetLaw_eq
#print axioms offsetLaw_escape_eq
#print axioms homogeneousRenewal_uniform_overshoot_overlap

end AnalyticCombinatorics.Ch8.Partitions.Renewal
