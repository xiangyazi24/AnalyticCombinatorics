import AnalyticCombinatorics.Ch8.Partitions.TailBand
import AnalyticCombinatorics.Ch8.Partitions.DoeblinEscape
import AnalyticCombinatorics.Ch8.Partitions.KilledStochastic
import AnalyticCombinatorics.Ch8.Partitions.StepContraction
import AnalyticCombinatorics.Ch8.Partitions.TailOscConverge

/-!
# R7 Fact B via Doeblin: the §9 final assembly

The capstone of the §9 renewal route.  A bounded function `h` that is `KPowK L P̃`-harmonic for a
row-stochastic killed kernel `P̃` (the exact-harmonicity supplied by `killed_harmonic_pow`) converges,
provided two analytic facts about the kernel:

* **overlap** `δ > 0`: for `rank i, rank j ≥ R` the `L`-step laws share mass `≥ δ` on the high-rank band
  `{rank ≥ R − B}` (a finite-time Doeblin condition), and
* **escape** `η(R) → 0`: the `L`-step law from a high-rank start puts vanishing mass below the band.

The escape-split Doeblin inequality then gives the tail-oscillation step contraction
`V(R) ≤ (1−δ)·V(R−B) + 3·M·η(R)`, which `tendsto_zero_of_step_contraction` drives to `V → 0`, and
`tendsto_of_tail_osc_to_zero` turns into `h → L`.  Everything here is mechanical; the two facts
`overlap`/`escape` are the only remaining analytic content (the `Γ`-convolution local-limit wall).
Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **§9 final assembly.** A bounded `KPowK L P̃`-harmonic function converges, given the finite-time
Doeblin overlap `δ` on the high-rank band and vanishing escape mass `e`. -/
theorem tendsto_of_killed_doeblin {h : ℕ → ℝ} {rank : ℕ → ℕ} {Pt : ℕ → ℕ → ℝ}
    {M δ : ℝ} {B R₀ L : ℕ} {e : ℕ → ℝ}
    (hM : ∀ n, |h n| ≤ M)
    (hrank : Tendsto rank atTop atTop)
    (hPtnn : ∀ n k, 0 ≤ Pt n k)
    (hPtrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Pt m k = 1)
    (hharm : ∀ n, h n = ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k * h k)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (he0 : ∀ n, 0 ≤ e n) (hetend : Tendsto e atTop (𝓝 0))
    (hoverlap : ∀ R, R₀ ≤ R → ∀ i j, R ≤ rank i → R ≤ rank j →
       δ ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rank k),
              min (KPowK L Pt i k) (KPowK L Pt j k))
    (hescape : ∀ R, R₀ ≤ R → ∀ i, R ≤ rank i →
       ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)),
              KPowK L Pt i k ≤ e R) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  classical
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (h 0)) (hM 0)
  -- the power kernel is nonneg, row-stochastic over `range (n+1)`, and supported on `k ≤ n`
  have hPpownn : ∀ n k, 0 ≤ KPowK L Pt n k := KPowK_nonneg hPtnn L
  have hPprow : ∀ n, ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k = 1 := KPowK_row_sum hPtrow L
  have hPpsupp : ∀ a b, a < b → KPowK L Pt a b = 0 := fun a b hab => KPowK_support L hab
  -- the pairwise contraction `h i − h j ≤ (1−δ)·V(R−B) + 3·(e R)·M` for `R ≥ R₀`
  have hpair : ∀ R, R₀ ≤ R → ∀ i j, R ≤ rank i → R ≤ rank j →
      h i - h j ≤ (1 - δ) * tailOsc h rank (R - B) + 3 * e R * M := by
    intro R hR i j hi hj
    set s := Finset.range (max i j + 1) with hs
    have hsub_i : Finset.range (i + 1) ⊆ s := by
      rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_left i j))
    have hsub_j : Finset.range (j + 1) ⊆ s := by
      rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
      exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_right i j))
    -- extend the harmonic identity to the common finset `s`
    have hext_i : h i = ∑ k ∈ s, KPowK L Pt i k * h k := by
      rw [hharm i]
      refine Finset.sum_subset hsub_i (fun k _ hk => ?_)
      rw [Finset.mem_range] at hk
      rw [hPpsupp i k (Nat.not_lt.mp hk), zero_mul]
    have hext_j : h j = ∑ k ∈ s, KPowK L Pt j k * h k := by
      rw [hharm j]
      refine Finset.sum_subset hsub_j (fun k _ hk => ?_)
      rw [Finset.mem_range] at hk
      rw [hPpsupp j k (Nat.not_lt.mp hk), zero_mul]
    -- row sums over `s`
    have hpm_i : ∑ k ∈ s, KPowK L Pt i k = 1 := by
      rw [← hPprow i]
      refine (Finset.sum_subset hsub_i (fun k _ hk => ?_)).symm
      rw [Finset.mem_range] at hk
      exact hPpsupp i k (Nat.not_lt.mp hk)
    have hpm_j : ∑ k ∈ s, KPowK L Pt j k = 1 := by
      rw [← hPprow j]
      refine (Finset.sum_subset hsub_j (fun k _ hk => ?_)).symm
      rw [Finset.mem_range] at hk
      exact hPpsupp j k (Nat.not_lt.mp hk)
    -- bad-mass bounds over `s` reduce (zero extension) to the escape hypothesis
    have hbad_i : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k ≤ e R := by
      have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k
          = ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k := by
        refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_i) (fun k hk hk2 => ?_)).symm
        have hk2' : k ∉ Finset.range (i + 1) := fun hc =>
          hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
        rw [Finset.mem_range] at hk2'
        exact hPpsupp i k (Nat.not_lt.mp hk2')
      rw [heq]; exact hescape R hR i hi
    have hbad_j : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k ≤ e R := by
      have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k
          = ∑ k ∈ (Finset.range (j + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k := by
        refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_j) (fun k hk hk2 => ?_)).symm
        have hk2' : k ∉ Finset.range (j + 1) := fun hc =>
          hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
        rw [Finset.mem_range] at hk2'
        exact hPpsupp j k (Nat.not_lt.mp hk2')
      rw [heq]; exact hescape R hR j hj
    -- the band: every good index lands in `[d(R−B), d(R−B)+V(R−B)]`
    have hfband : ∀ k ∈ s.filter (fun k => R - B ≤ rank k),
        tailInf h rank (R - B) ≤ h k ∧ h k ≤ tailInf h rank (R - B) + tailOsc h rank (R - B) := by
      intro k hk
      have hGk : R - B ≤ rank k := (Finset.mem_filter.mp hk).2
      obtain ⟨hb1, hb2⟩ := tail_band hM hGk
      refine ⟨hb1, ?_⟩
      rw [tailOsc]; linarith
    -- apply the escape-split Doeblin contraction
    have hdoeb := doeblin_escape_bound (s := s) (p := KPowK L Pt i) (q := KPowK L Pt j)
      (f := h) (δ := δ) (η := e R) (lo := tailInf h rank (R - B)) (W := tailOsc h rank (R - B))
      (M := M) (fun k => R - B ≤ rank k)
      (fun k _ => hPpownn i k) (fun k _ => hPpownn j k)
      hpm_i hpm_j (hoverlap R hR i j hi hj) hbad_i hbad_j hfband
      (tailOsc_nonneg hrank hM (R - B)) (fun k _ => hM k)
      (tailInf_abs_le hrank hM (R - B)) (he0 R)
    rw [← hext_i, ← hext_j] at hdoeb
    calc h i - h j ≤ |h i - h j| := le_abs_self _
      _ ≤ (1 - δ) * tailOsc h rank (R - B) + 3 * e R * M := hdoeb
  -- lift the pairwise bound to the tail-oscillation step contraction
  have hVcontract : ∀ R, R₀ ≤ R →
      tailOsc h rank R ≤ (1 - δ) * tailOsc h rank (R - B) + 3 * e R * M := fun R hR =>
    tailOsc_le_of_pairwise hrank (fun i j hi hj => hpair R hR i j hi hj)
  -- the forcing term vanishes
  have he_step : Tendsto (fun n => 3 * e (n + B) * M) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => e (n + B)) atTop (𝓝 0) := hetend.comp (tendsto_add_atTop_nat B)
    have h2 : Tendsto (fun n => 3 * e (n + B) * M) atTop (𝓝 (3 * 0 * M)) :=
      (h1.const_mul 3).mul_const M
    simpa using h2
  -- drive the tail oscillation to zero
  have hWnn : ∀ n, 0 ≤ tailOsc h rank n := fun n => tailOsc_nonneg hrank hM n
  have hWbd : BddAbove (Set.range (fun R => tailOsc h rank R)) :=
    ⟨2 * M, by rintro _ ⟨n, rfl⟩; exact tailOsc_le_two_M hrank hM n⟩
  have hrec : ∀ᶠ n in atTop,
      tailOsc h rank (n + B) ≤ (1 - δ) * tailOsc h rank n + 3 * e (n + B) * M := by
    filter_upwards [eventually_ge_atTop R₀] with n hn
    have hge : R₀ ≤ n + B := le_trans hn (Nat.le_add_right n B)
    have hc := hVcontract (n + B) hge
    rwa [Nat.add_sub_cancel] at hc
  have hWtend : Tendsto (fun R => tailOsc h rank R) atTop (𝓝 0) :=
    tendsto_zero_of_step_contraction (q := 1 - δ) (L := B)
      (by linarith) (by linarith) hWnn hWbd he_step hrec
  -- tail oscillation → 0 ⟹ `h` converges
  exact tendsto_of_tail_osc_to_zero hrank hWtend
    (fun R i j hi hj => tailOsc_abs_le hM hi hj)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
