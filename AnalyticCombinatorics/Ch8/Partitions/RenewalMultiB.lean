import AnalyticCombinatorics.Ch8.Partitions.RenewalAssembly
import AnalyticCombinatorics.Ch8.Partitions.StepContractionConst

/-!
# R7 Fact B via Doeblin: the multi-scale §9 assembly (correct for the Erdős kernel)

The escape-split capstone `tendsto_of_killed_doeblin` needs escape mass `→ 0` at a *fixed* band width,
which the Erdős kernel does not satisfy (the escape below a fixed band is `~ e^{−cB}`, constant in `R`).
The correct assembly is multi-scale: for each band width `B` the tail oscillation obeys
`V(R) ≤ (1−δ_B)·V(R−B) + δ_B·bnd B` (`R ≥ R₀(B)`), giving `limsup V ≤ bnd B`; letting `bnd B → 0`
forces `V → 0`, hence `h` converges.  The per-`B` contraction is produced exactly as in
`tendsto_of_killed_doeblin` (overlap `δ_B` on band `B` + escape, via `doeblin_escape_bound`), with
`bnd B = 3·ε_B·M / δ_B`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Multi-scale tail-oscillation engine.** A family of band contractions whose `limsup` bounds vanish
forces `h` to converge. -/
theorem tendsto_of_tailOsc_multiB {h : ℕ → ℝ} {rank : ℕ → ℕ} {M : ℝ} {bnd : ℕ → ℝ}
    (hM : ∀ n, |h n| ≤ M) (hrank : Tendsto rank atTop atTop)
    (hbnd0 : ∀ B, 0 ≤ bnd B) (hbnd : Tendsto bnd atTop (𝓝 0))
    (hcontract : ∀ B : ℕ, ∃ (δ : ℝ) (R₀ : ℕ), 0 < δ ∧ δ ≤ 1 ∧
        ∀ R, R₀ ≤ R → tailOsc h rank R ≤ (1 - δ) * tailOsc h rank (R - B) + δ * bnd B) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  have hWnn : ∀ R, 0 ≤ tailOsc h rank R := fun R => tailOsc_nonneg hrank hM R
  have hWbd : BddAbove (Set.range (fun R => tailOsc h rank R)) :=
    ⟨2 * M, by rintro _ ⟨n, rfl⟩; exact tailOsc_le_two_M hrank hM n⟩
  have hVtend : Tendsto (fun R => tailOsc h rank R) atTop (𝓝 0) := by
    refine tendsto_zero_of_limsup_le_all hWnn hWbd (fun B => ?_) hbnd
    obtain ⟨δ, R₀, hδ0, hδ1, hcon⟩ := hcontract B
    have hrec : ∀ᶠ R in atTop,
        tailOsc h rank (R + B) ≤ (1 - δ) * tailOsc h rank R + δ * bnd B := by
      filter_upwards [eventually_ge_atTop R₀] with R hR
      have hc := hcon (R + B) (le_trans hR (Nat.le_add_right R B))
      rwa [Nat.add_sub_cancel] at hc
    have hls := limsup_le_of_step_contraction_const (W := fun R => tailOsc h rank R)
      (q := 1 - δ) (c := δ * bnd B) (L := B) (by linarith) (by linarith)
      hWnn hWbd hrec
    calc limsup (fun R => tailOsc h rank R) atTop
        ≤ δ * bnd B / (1 - (1 - δ)) := hls
      _ = bnd B := by
          rw [show (1 : ℝ) - (1 - δ) = δ by ring]; field_simp
  exact tendsto_of_tail_osc_to_zero hrank hVtend (fun R i j hi hj => tailOsc_abs_le hM hi hj)

/-- **Multi-scale killed-Doeblin convergence.** A bounded `KPowK L_B P̃`-harmonic `h` converges given,
for each band width `B`, a finite-time overlap `δ_B > 0` on the band `{rnk ≥ R−B}` and escape mass
`≤ ε_B` below it, with `3·ε_B·M / δ_B → 0`. -/
theorem tendsto_of_killed_doeblin_multiB {h : ℕ → ℝ} {rank : ℕ → ℕ} {Pt : ℕ → ℕ → ℝ}
    {M : ℝ} {bnd : ℕ → ℝ}
    (hM : ∀ n, |h n| ≤ M)
    (hrank : Tendsto rank atTop atTop)
    (hPtnn : ∀ n k, 0 ≤ Pt n k)
    (hPtrow : ∀ m, ∑ k ∈ Finset.range (m + 1), Pt m k = 1)
    (hbnd0 : ∀ B, 0 ≤ bnd B) (hbnd : Tendsto bnd atTop (𝓝 0))
    (hwalls : ∀ B : ℕ, ∃ (δ : ℝ) (R₀ L : ℕ),
        0 < δ ∧ δ ≤ 1 ∧
        (∀ n, h n = ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k * h k) ∧
        (∀ R, R₀ ≤ R → ∀ i j, R ≤ rank i → R ≤ rank j →
           δ ≤ ∑ k ∈ (Finset.range (max i j + 1)).filter (fun k => R - B ≤ rank k),
                  min (KPowK L Pt i k) (KPowK L Pt j k)) ∧
        (∀ R, R₀ ≤ R → ∀ i, R ≤ rank i →
           ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)),
                  KPowK L Pt i k ≤ δ * bnd B / (3 * M + 1))) :
    ∃ Lst : ℝ, Tendsto h atTop (𝓝 Lst) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (h 0)) (hM 0)
  refine tendsto_of_tailOsc_multiB hM hrank hbnd0 hbnd (fun B => ?_)
  obtain ⟨δ, R₀, L, hδ0, hδ1, hharm, hoverlap, hescape⟩ := hwalls B
  have hPpownn : ∀ n k, 0 ≤ KPowK L Pt n k := KPowK_nonneg hPtnn L
  have hPprow : ∀ n, ∑ k ∈ Finset.range (n + 1), KPowK L Pt n k = 1 := KPowK_row_sum hPtrow L
  have hPpsupp : ∀ a b, a < b → KPowK L Pt a b = 0 := fun a b hab => KPowK_support L hab
  refine ⟨δ, R₀, hδ0, hδ1, fun R hR => ?_⟩
  -- pairwise bound via doeblin_escape_bound, then tailOsc_le_of_pairwise
  refine tailOsc_le_of_pairwise hrank (fun i j hi hj => ?_)
  set s := Finset.range (max i j + 1) with hs
  have hsub_i : Finset.range (i + 1) ⊆ s := by
    rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
    exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_left i j))
  have hsub_j : Finset.range (j + 1) ⊆ s := by
    rw [hs]; intro x hx; rw [Finset.mem_range] at hx ⊢
    exact Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp hx) (le_max_right i j))
  have hext_i : h i = ∑ k ∈ s, KPowK L Pt i k * h k := by
    rw [hharm i]; refine Finset.sum_subset hsub_i (fun k _ hk => ?_)
    rw [Finset.mem_range] at hk; rw [hPpsupp i k (Nat.not_lt.mp hk), zero_mul]
  have hext_j : h j = ∑ k ∈ s, KPowK L Pt j k * h k := by
    rw [hharm j]; refine Finset.sum_subset hsub_j (fun k _ hk => ?_)
    rw [Finset.mem_range] at hk; rw [hPpsupp j k (Nat.not_lt.mp hk), zero_mul]
  have hpm_i : ∑ k ∈ s, KPowK L Pt i k = 1 := by
    rw [← hPprow i]; refine (Finset.sum_subset hsub_i (fun k _ hk => ?_)).symm
    rw [Finset.mem_range] at hk; exact hPpsupp i k (Nat.not_lt.mp hk)
  have hpm_j : ∑ k ∈ s, KPowK L Pt j k = 1 := by
    rw [← hPprow j]; refine (Finset.sum_subset hsub_j (fun k _ hk => ?_)).symm
    rw [Finset.mem_range] at hk; exact hPpsupp j k (Nat.not_lt.mp hk)
  -- bad-mass bounds (reduce to escape over range(i+1)) — bounded by δ·bnd B/(3M+1)
  have hbad_i : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k
      ≤ δ * bnd B / (3 * M + 1) := by
    have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k
        = ∑ k ∈ (Finset.range (i + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt i k := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_i) (fun k hk hk2 => ?_)).symm
      have hk2' : k ∉ Finset.range (i + 1) := fun hc =>
        hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
      rw [Finset.mem_range] at hk2'; exact hPpsupp i k (Nat.not_lt.mp hk2')
    rw [heq]; exact hescape R hR i hi
  have hbad_j : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k
      ≤ δ * bnd B / (3 * M + 1) := by
    have heq : ∑ k ∈ s.filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k
        = ∑ k ∈ (Finset.range (j + 1)).filter (fun k => ¬ (R - B ≤ rank k)), KPowK L Pt j k := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hsub_j) (fun k hk hk2 => ?_)).symm
      have hk2' : k ∉ Finset.range (j + 1) := fun hc =>
        hk2 (Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hk).2⟩)
      rw [Finset.mem_range] at hk2'; exact hPpsupp j k (Nat.not_lt.mp hk2')
    rw [heq]; exact hescape R hR j hj
  have hfband : ∀ k ∈ s.filter (fun k => R - B ≤ rank k),
      tailInf h rank (R - B) ≤ h k ∧ h k ≤ tailInf h rank (R - B) + tailOsc h rank (R - B) := by
    intro k hk
    have hGk : R - B ≤ rank k := (Finset.mem_filter.mp hk).2
    obtain ⟨hb1, hb2⟩ := tail_band hM hGk
    exact ⟨hb1, by rw [tailOsc]; linarith⟩
  set η := δ * bnd B / (3 * M + 1) with hη
  have hη0 : 0 ≤ η := by
    rw [hη]; apply div_nonneg (mul_nonneg hδ0.le (hbnd0 B)); linarith
  have hdoeb := doeblin_escape_bound (s := s) (p := KPowK L Pt i) (q := KPowK L Pt j)
    (f := h) (δ := δ) (η := η) (lo := tailInf h rank (R - B)) (W := tailOsc h rank (R - B))
    (M := M) (fun k => R - B ≤ rank k)
    (fun k _ => hPpownn i k) (fun k _ => hPpownn j k)
    hpm_i hpm_j (hoverlap R hR i j hi hj) hbad_i hbad_j hfband
    (tailOsc_nonneg hrank hM (R - B)) (fun k _ => hM k)
    (tailInf_abs_le hrank hM (R - B)) hη0
  rw [← hext_i, ← hext_j] at hdoeb
  -- |h i − h j| ≤ (1−δ)·V(R−B) + 3·η·M ;  3·η·M ≤ δ·bnd B
  have hP : 0 ≤ δ * bnd B := mul_nonneg hδ0.le (hbnd0 B)
  have hden : (0 : ℝ) < 3 * M + 1 := by linarith
  have h3ηM : 3 * η * M ≤ δ * bnd B := by
    rw [hη, show 3 * (δ * bnd B / (3 * M + 1)) * M = 3 * M * (δ * bnd B) / (3 * M + 1) by ring,
      div_le_iff₀ hden]
    nlinarith [hP, hMnn]
  calc h i - h j ≤ |h i - h j| := le_abs_self _
    _ ≤ (1 - δ) * tailOsc h rank (R - B) + 3 * η * M := hdoeb
    _ ≤ (1 - δ) * tailOsc h rank (R - B) + δ * bnd B := by linarith [h3ηM]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
