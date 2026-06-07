import AnalyticCombinatorics.Ch8.Partitions.RenewalAssembly
import AnalyticCombinatorics.Ch8.Partitions.DoeblinOverlap

/-!
# R7 Fact B via Doeblin: the renewal-alignment capstone (correct convergence)

The all-pairs single-step overlap is false for the Erdős kernel (far-rank pairs have disjoint one-step
laws).  The correct deterministic input — per the renewal structure — is the **alignment** of the
`m`-step terminal laws: as two high-rank chains descend, they pass through shared lower rank levels and
synchronize, so for any `m, ε` and high enough starts `i, j`,

  `overlap(P̃^m(i,·), P̃^m(j,·)) ≥ 1 − (1−δ*)^m − ε`.

Given this, convergence is a one-liner: `h` is harmonic for every power (`h = P̃^m h`), so
`|h i − h j| = |∑(P̃^m(i,·)−P̃^m(j,·))·h| ≤ 2M·(1 − overlap) ≤ 2M((1−δ*)^m + ε)`, whence the tail
oscillation `→ 0` and `h` converges.  All of this is the finite-kernel overlap algebra
(`doeblin_average_diff_bound` with band `[−M, M]`, `W = 2M`) + an antitone squeeze; the single hard
analytic input is the alignment hypothesis.  Opus-authored (design cross-checked with ChatGPT R2).
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Renewal-alignment capstone.** A bounded function harmonic for every power of the killed kernel,
whose `m`-step terminal laws align (`overlap ≥ 1 − (1−δ*)^m − ε` for high starts), converges. -/
theorem tendsto_of_renewal_alignment {h : ℕ → ℝ} {rank : ℕ → ℕ} {Pt : ℕ → ℕ → ℝ} {M δ : ℝ}
    (hM : ∀ n, |h n| ≤ M)
    (hrank : Tendsto rank atTop atTop)
    (hPtnn : ∀ n k, 0 ≤ Pt n k)
    (hPtrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Pt m k = 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hharm : ∀ (m n : ℕ), h n = ∑ k ∈ Finset.range (n + 1), KPowK m Pt n k * h k)
    (halign : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ i j, R₀ ≤ rank i → R₀ ≤ rank j →
        1 - (1 - δ) ^ m - ε ≤
          ∑ k ∈ Finset.range (max i j + 1), min (KPowK m Pt i k) (KPowK m Pt j k)) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (h 0)) (hM 0)
  -- per (m,ε,R₀) pairwise bound  |h i − h j| ≤ 2M((1−δ)^m + ε)
  have hpair : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∀ R₀ : ℕ,
      (∀ i j, R₀ ≤ rank i → R₀ ≤ rank j →
        1 - (1 - δ) ^ m - ε ≤
          ∑ k ∈ Finset.range (max i j + 1), min (KPowK m Pt i k) (KPowK m Pt j k)) →
      ∀ i j, R₀ ≤ rank i → R₀ ≤ rank j →
        h i - h j ≤ 2 * M * ((1 - δ) ^ m + ε) := by
    intro m ε hε R₀ hov i j hi hj
    have hPpownn : ∀ n k, 0 ≤ KPowK m Pt n k := KPowK_nonneg hPtnn m
    have hPprow : ∀ n, ∑ k ∈ Finset.range (n + 1), KPowK m Pt n k = 1 := KPowK_row_sum hPtrow m
    have hPpsupp : ∀ a b, a < b → KPowK m Pt a b = 0 := fun a b hab => KPowK_support m hab
    set s := Finset.range (max i j + 1) with hs
    have hsub_i : Finset.range (i + 1) ⊆ s := by
      rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_left i j))
    have hsub_j : Finset.range (j + 1) ⊆ s := by
      rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_right i j))
    have hext_i : h i = ∑ k ∈ s, KPowK m Pt i k * h k := by
      rw [hharm m i]; refine Finset.sum_subset hsub_i (fun k _ hk => ?_)
      rw [Finset.mem_range] at hk; rw [hPpsupp i k (Nat.not_lt.mp hk), zero_mul]
    have hext_j : h j = ∑ k ∈ s, KPowK m Pt j k * h k := by
      rw [hharm m j]; refine Finset.sum_subset hsub_j (fun k _ hk => ?_)
      rw [Finset.mem_range] at hk; rw [hPpsupp j k (Nat.not_lt.mp hk), zero_mul]
    have hpm_i : ∑ k ∈ s, KPowK m Pt i k = 1 := by
      rw [← hPprow i]; refine (Finset.sum_subset hsub_i (fun k _ hk => ?_)).symm
      rw [Finset.mem_range] at hk; exact hPpsupp i k (Nat.not_lt.mp hk)
    have hpm_j : ∑ k ∈ s, KPowK m Pt j k = 1 := by
      rw [← hPprow j]; refine (Finset.sum_subset hsub_j (fun k _ hk => ?_)).symm
      rw [Finset.mem_range] at hk; exact hPpsupp j k (Nat.not_lt.mp hk)
    have hband : ∀ k ∈ s, -M ≤ h k ∧ h k ≤ -M + 2 * M := fun k _ =>
      ⟨neg_le_of_abs_le (hM k), by have := (abs_le.mp (hM k)).2; linarith⟩
    set ov := ∑ k ∈ s, min (KPowK m Pt i k) (KPowK m Pt j k) with hov_def
    have hdoeb := doeblin_average_diff_bound (s := s) (p := KPowK m Pt i) (q := KPowK m Pt j)
      (f := h) (δ := ov) (lo := -M) (W := 2 * M)
      hpm_i hpm_j (le_of_eq hov_def.symm) hband (by linarith)
    rw [← hext_i, ← hext_j] at hdoeb
    -- |h i − h j| ≤ (1 − ov)·2M ;  ov ≥ 1 − (1−δ)^m − ε  ⟹  1 − ov ≤ (1−δ)^m + ε
    have hovlb : 1 - (1 - δ) ^ m - ε ≤ ov := hov i j hi hj
    calc h i - h j ≤ |h i - h j| := le_abs_self _
      _ ≤ (1 - ov) * (2 * M) := hdoeb
      _ ≤ 2 * M * ((1 - δ) ^ m + ε) := by nlinarith [hMnn, hovlb]
  -- tail oscillation bound from each (m,ε)
  have hVle : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ,
      tailOsc h rank R₀ ≤ 2 * M * ((1 - δ) ^ m + ε) := by
    intro m ε hε
    obtain ⟨R₀, hov⟩ := halign m ε hε
    exact ⟨R₀, tailOsc_le_of_pairwise hrank (fun i j hi hj => hpair m ε hε R₀ hov i j hi hj)⟩
  -- tailOsc → 0  (antitone + a vanishing family of bounds)
  have hpow : Tendsto (fun m : ℕ => 2 * M * ((1 - δ) ^ m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (1 - δ) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
    have := h1.const_mul (2 * M)
    simpa using this
  have hVtend : Tendsto (fun R => tailOsc h rank R) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨m, hm⟩ := (hpow.eventually (gt_mem_nhds (show (0:ℝ) < η / 2 by linarith))).exists
    obtain ⟨R₀, hR₀⟩ := hVle m (η / (4 * M + 4)) (by positivity)
    refine ⟨R₀, fun R hR => ?_⟩
    have hanti : tailOsc h rank R ≤ tailOsc h rank R₀ := tailOsc_antitone hrank hM hR
    have hnn : 0 ≤ tailOsc h rank R := tailOsc_nonneg hrank hM R
    have hεbound : 2 * M * (η / (4 * M + 4)) ≤ η / 2 := by
      have h4 : (0:ℝ) < 4 * M + 4 := by linarith
      rw [show 2 * M * (η / (4 * M + 4)) = 2 * M * η / (4 * M + 4) by ring,
        div_le_div_iff₀ h4 (by norm_num : (0:ℝ) < 2)]
      nlinarith [hMnn, hη.le]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hle : tailOsc h rank R ≤ 2 * M * ((1 - δ) ^ m + η / (4 * M + 4)) := le_trans hanti hR₀
    have hexpand : 2 * M * ((1 - δ) ^ m + η / (4 * M + 4))
        = 2 * M * (1 - δ) ^ m + 2 * M * (η / (4 * M + 4)) := by ring
    rw [hexpand] at hle
    linarith [hle, hm, hεbound]
  exact tendsto_of_tail_osc_to_zero hrank hVtend (fun R i j hi hj => tailOsc_abs_le hM hi hj)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
