import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LocalLower
import AnalyticCombinatorics.Ch8.Partitions.BarrierInduction

/-!
# Record extrema and the convergence assembly (R7 route, kernel-free layers)

The corrected Erdős convergence route (R7; replaces the refuted finite-renewal lemma)
runs through *record extrema*: if high records cover their tail within `ε` and low records
do likewise, then `u` is Cauchy.  This file banks the kernel-free layers:

* records and their existence on finite intervals;
* the assembly `record covers ⟹ CauchySeq ⟹ ∃ limit > 0`;
* the local monotone forward fill `u n − ε ≤ u (n+r)` for `r ≤ h√n`.

The cover hypotheses are taken in the threshold-monotone form (`∀ N₀' ≥ N₀`), which the
forthcoming shell-error proofs deliver naturally.  The kernel-dependent record pullback /
percolation bricks remain (they need the mass-rate brick).  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `N` is a running maximum of `u` on `[N₀, N]`. -/
def highRecordFrom (N₀ N : ℕ) : Prop :=
  N₀ ≤ N ∧ ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u N

/-- `N` is a running minimum of `u` on `[N₀, N]`. -/
def lowRecordFrom (N₀ N : ℕ) : Prop :=
  N₀ ≤ N ∧ ∀ k : ℕ, N₀ ≤ k → k ≤ N → u N ≤ u k

/-- High records exist on every finite interval. -/
lemma exists_highRecordFrom (N₀ N : ℕ) (hN : N₀ ≤ N) :
    ∃ R : ℕ, N₀ ≤ R ∧ R ≤ N ∧ highRecordFrom N₀ R ∧
      ∀ k : ℕ, N₀ ≤ k → k ≤ N → u k ≤ u R := by
  classical
  have hne : (Finset.Icc N₀ N).Nonempty := ⟨N₀, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image (Finset.Icc N₀ N) u hne
  obtain ⟨hR1, hR2⟩ := Finset.mem_Icc.mp hRmem
  refine ⟨R, hR1, hR2, ⟨hR1, ?_⟩, ?_⟩
  · intro k hk1 hk2
    exact hRmax k (Finset.mem_Icc.mpr ⟨hk1, le_trans hk2 hR2⟩)
  · intro k hk1 hk2
    exact hRmax k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)

/-- Low records exist on every finite interval. -/
lemma exists_lowRecordFrom (N₀ N : ℕ) (hN : N₀ ≤ N) :
    ∃ R : ℕ, N₀ ≤ R ∧ R ≤ N ∧ lowRecordFrom N₀ R ∧
      ∀ k : ℕ, N₀ ≤ k → k ≤ N → u R ≤ u k := by
  classical
  have hne : (Finset.Icc N₀ N).Nonempty := ⟨N₀, Finset.mem_Icc.mpr ⟨le_refl _, hN⟩⟩
  obtain ⟨R, hRmem, hRmin⟩ := Finset.exists_min_image (Finset.Icc N₀ N) u hne
  obtain ⟨hR1, hR2⟩ := Finset.mem_Icc.mp hRmem
  refine ⟨R, hR1, hR2, ⟨hR1, ?_⟩, ?_⟩
  · intro k hk1 hk2
    exact hRmin k (Finset.mem_Icc.mpr ⟨hk1, le_trans hk2 hR2⟩)
  · intro k hk1 hk2
    exact hRmin k (Finset.mem_Icc.mpr ⟨hk1, hk2⟩)

/--
**Convergence assembly** (R7 §9): threshold-monotone record covers force `u` to converge.
-/
theorem u_tendsto_of_record_covers
    (hhigh : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N₀' : ℕ, N₀ ≤ N₀' →
      ∀ N : ℕ, highRecordFrom N₀' N →
        ∀ k : ℕ, N₀' ≤ k → k ≤ N → u N - ε ≤ u k)
    (hlow : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N₀' : ℕ, N₀ ≤ N₀' →
      ∀ N : ℕ, lowRecordFrom N₀' N →
        ∀ k : ℕ, N₀' ≤ k → k ≤ N → u k ≤ u N + ε) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε4 : 0 < ε / 4 := by linarith
    obtain ⟨N₁, hN₁⟩ := hhigh (ε / 4) hε4
    obtain ⟨N₂, hN₂⟩ := hlow (ε / 4) hε4
    set N₀ : ℕ := max N₁ N₂ with hN₀def
    refine ⟨N₀, ?_⟩
    intro p hp q hq
    set Q : ℕ := max p q with hQdef
    have hN₀Q : N₀ ≤ Q := le_trans hp (le_max_left _ _)
    obtain ⟨H, hH1, hH2, hHrec, hHmax⟩ := exists_highRecordFrom N₀ Q hN₀Q
    obtain ⟨Lo, hLo1, hLo2, hLorec, hLomin⟩ := exists_lowRecordFrom N₀ Q hN₀Q
    -- records from N₀ are admissible for both covers (N₀ ≥ N₁, N₂)
    have hcoverH := hN₁ N₀ (le_max_left _ _) H hHrec
    have hcoverL := hN₂ N₀ (le_max_right _ _) Lo hLorec
    -- u H − u Lo ≤ ε/4, by cases on the order of H and Lo
    have hHLo : u H - u Lo ≤ ε / 4 := by
      rcases le_total Lo H with hord | hord
      · -- Lo ∈ [N₀, H]: high cover at k = Lo
        have := hcoverH Lo hLo1 hord
        linarith
      · -- H ∈ [N₀, Lo]: low cover at k = H
        have := hcoverL H hH1 hord
        linarith
    -- both p and q sit between the record extrema on [N₀, Q]
    have hpQ : p ≤ Q := le_max_left _ _
    have hqQ : q ≤ Q := le_max_right _ _
    have hup : u p ≤ u H := hHmax p hp hpQ
    have huq : u q ≤ u H := hHmax q hq hqQ
    have hlp : u Lo ≤ u p := hLomin p hp hpQ
    have hlq : u Lo ≤ u q := hLomin q hq hqQ
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact cauchySeq_tendsto_of_complete hcauchy

/-- The limit is positive given the (conditional) liminf bound. -/
theorem erdos_limit_pos_of_tendsto {L c : ℝ} (hc : 0 < c)
    (htend : Tendsto u atTop (𝓝 L))
    (hlim : ∀ᶠ n : ℕ in atTop, c ≤ u n) :
    0 < L := by
  have hcL : c ≤ L := ge_of_tendsto htend hlim
  linarith

/--
**Local monotone forward fill** (R7 §4): with an eventual upper bound, a high value fills
forward additively: for every `ε > 0` there is `h > 0` with
`u n − ε ≤ u (n+r)` for all `r ≤ h√n`, eventually in `n`.
-/
theorem u_local_high_forward_fill {M : ℝ} (hM : 0 < M)
    (hupper : ∀ᶠ n : ℕ in atTop, u n ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ,
        (r : ℝ) ≤ h * Real.sqrt (n : ℝ) → u n - ε ≤ u (n + r) := by
  intro ε hε
  have hC := C_pos
  refine ⟨2 * ε / (C * M), by positivity, ?_⟩
  filter_upwards [hupper, eventually_ge_atTop 1] with n hub hn1
  intro r hr
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hu_pos : 0 < u n := u_pos hn1
  -- the propagation multiplier
  have hprop := u_local_lower_from_monotone (n := n) r hn1
  -- Δ = √(n+r) − √n ≤ r/(2√n) ≤ h/2
  have hsum_ge : Real.sqrt (n : ℝ) + Real.sqrt ((n + r : ℕ) : ℝ)
      ≥ 2 * Real.sqrt (n : ℝ) := by
    have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + r : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.le_add_right n r
    linarith
  have hdrop_le : Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)
      ≤ (r : ℝ) / (2 * Real.sqrt (n : ℝ)) := by
    have hfact : (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)) *
        (Real.sqrt ((n + r : ℕ) : ℝ) + Real.sqrt (n : ℝ)) = (r : ℝ) := by
      have h1 : Real.sqrt ((n + r : ℕ) : ℝ) * Real.sqrt ((n + r : ℕ) : ℝ)
          = ((n + r : ℕ) : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
      have h2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      have h3 : ((n + r : ℕ) : ℝ) = (n : ℝ) + (r : ℝ) := by push_cast; ring
      nlinarith [h1, h2]
    have hX : 0 ≤ Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ) := by
      have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + r : ℕ) : ℝ) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast Nat.le_add_right n r
      linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (n : ℝ))]
    nlinarith [hfact, hsum_ge, hX,
      mul_nonneg hX (by linarith [hsum_ge] :
        (0 : ℝ) ≤ Real.sqrt ((n + r : ℕ) : ℝ) + Real.sqrt (n : ℝ)
          - 2 * Real.sqrt (n : ℝ))]
  have hdrop_half : Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)
      ≤ ε / (C * M) := by
    have h2 : (r : ℝ) / (2 * Real.sqrt (n : ℝ))
        ≤ (2 * ε / (C * M)) * Real.sqrt (n : ℝ) / (2 * Real.sqrt (n : ℝ)) := by
      gcongr
    have h3 : (2 * ε / (C * M)) * Real.sqrt (n : ℝ) / (2 * Real.sqrt (n : ℝ))
        = ε / (C * M) := by
      field_simp
    calc Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)
        ≤ (r : ℝ) / (2 * Real.sqrt (n : ℝ)) := hdrop_le
      _ ≤ ε / (C * M) := by rw [← h3]; exact h2
  -- e^{−CΔ} ≥ 1 − CΔ ≥ 1 − ε/M
  have hexp_ge : Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)))
      ≥ 1 - ε / M := by
    have h1 := Real.add_one_le_exp
      (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)))
    have h2 : C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)) ≤ ε / M := by
      have := mul_le_mul_of_nonneg_left hdrop_half hC.le
      calc C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))
          ≤ C * (ε / (C * M)) := this
        _ = ε / M := by field_simp
    linarith
  -- multiplier ≥ (1)(1 − ε/M); conclude
  have hmult : ((n + r : ℕ) : ℝ) / (n : ℝ) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ hnpos]
    have : (n : ℝ) ≤ ((n + r : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    linarith
  have hchain : (1 - ε / M) * u n ≤ u (n + r) := by
    by_cases hsign : 0 ≤ 1 - ε / M
    · calc (1 - ε / M) * u n
          ≤ (((n + r : ℕ) : ℝ) / (n : ℝ) *
              Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ)))) * u n := by
            apply mul_le_mul_of_nonneg_right _ hu_pos.le
            calc (1 : ℝ) - ε / M
                = 1 * (1 - ε / M) := (one_mul _).symm
              _ ≤ (((n + r : ℕ) : ℝ) / (n : ℝ)) *
                  Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))) := by
                  apply mul_le_mul hmult hexp_ge hsign
                  linarith [hmult]
        _ ≤ u (n + r) := hprop
    · push_neg at hsign
      have h1 : (1 - ε / M) * u n < 0 := mul_neg_of_neg_of_pos hsign hu_pos
      have h2 : 0 < u (n + r) := u_pos (by omega)
      linarith
  -- u n − ε ≤ (1 − ε/M)·u n  since u n ≤ M
  have hfinal : u n - ε ≤ (1 - ε / M) * u n := by
    have h1 : (1 - ε / M) * u n = u n - (ε / M) * u n := by ring
    rw [h1]
    have h2 : (ε / M) * u n ≤ ε := by
      have := mul_le_mul_of_nonneg_left hub (by positivity : (0:ℝ) ≤ ε / M)
      calc (ε / M) * u n ≤ (ε / M) * M := this
        _ = ε := by field_simp
    linarith
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
