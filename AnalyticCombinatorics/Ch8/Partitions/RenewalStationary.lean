import AnalyticCombinatorics.Ch8.Partitions.RenewalOverlap

/-!
# The reference measure π for the renewal residual chain (sector route)

The sector/Dirichlet route to the renewal Green lower bound needs a reference measure `π` on the
residual chain `resStep p` (RenewalOffset) for which the antisymmetric cut-flux is controlled.  The
crucial structural property is **stationarity**: for a stationary `π`, the cut-flux *divergence*
`divJ(x) = π_x·rowsum − ∑_y π_y K(y,x)` vanishes identically, so the divergence term of the exact cut
identity `aAnti = −½∑ divJ·f·g − ∑ Hcut·grad` drops and the sector reduces to the genuine crossing
variation.

This file constructs that reference measure as the already-built size-biased offset law
`statOffset p = incrTail p / incrMean p` (RenewalOverlap) and proves it is **stationary** for the
residual chain:

  `∑'_r statOffset p r · resStep p r r' = statOffset p r'`.

The residual row `r ↦ resStep p r r'` is supported on exactly `{0, r'+1}` (jump from `0`, or
deterministic descent from `r'+1`), so the `tsum` is a two-term sum; stationarity then follows from
the tail recurrence `incrTail p r' = p(r'+1) + incrTail p (r'+1)` and `statOffset p 0 = 1/μ`.

This is the reference-measure half of `erdos_rankdiff_sector_input`; the remaining sector input is the
quantitative crossing-variation (cut-flux) bound, which the sector route needs *instead* of a
rank-drop local limit (the latter being the documented floor-rank `⌊3√n⌋` obstruction in
`HANDOFF/TASK-T2-gap.md`).
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- **Tail recurrence**: `incrTail p A = p(A+1) + incrTail p (A+1)`. -/
lemma incrTail_succ (p : ℕ → ℝ) (A : ℕ) :
    incrTail p A = p (A + 1) + incrTail p (A + 1) := by
  have hss : (∑ d ∈ Finset.range (A + 1 + 1), p d)
      = (∑ d ∈ Finset.range (A + 1), p d) + p (A + 1) := Finset.sum_range_succ p (A + 1)
  unfold incrTail
  rw [hss]; ring

/-- **The reference measure is stationary**: the size-biased offset law `statOffset p` is invariant
under the residual chain `resStep p`,
`∑'_r statOffset p r · resStep p r r' = statOffset p r'`.

Hence (`divJ ≡ 0`) it is a divergence-free reference measure for the sector cut identity. -/
lemma statOffset_stationary {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) (r' : ℕ) :
    ∑' r, statOffset p r * resStep p r r' = statOffset p r' := by
  classical
  have hμ : 0 < incrMean p := incrMean_pos hl hsum
  -- the residual row in `r` is supported on `{0, r'+1}`
  have hsupp : ∀ r ∉ ({0, r' + 1} : Finset ℕ), statOffset p r * resStep p r r' = 0 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
    obtain ⟨hr0, hr1⟩ := hr
    obtain _ | m := r
    · exact absurd rfl hr0
    · rw [resStep_succ, if_neg (by omega : ¬ r' = m), mul_zero]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by omega : (0 : ℕ) ≠ r' + 1)]
  rw [resStep_zero, resStep_succ, if_pos rfl, mul_one]
  -- goal: statOffset p 0 * p (r'+1) + statOffset p (r'+1) = statOffset p r'
  have h0 : incrTail p 0 = 1 := by unfold incrTail; simp [hl.zero]
  have htail := incrTail_succ p r'
  unfold statOffset
  rw [h0, htail]
  field_simp

end AnalyticCombinatorics.Ch8.Partitions.Renewal
