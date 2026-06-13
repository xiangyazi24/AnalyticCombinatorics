import Mathlib

/-!
# R7 Fact B via Doeblin (File C): the oscillation→0 engine

`L`-step geometric contraction with vanishing forcing drives a bounded nonnegative sequence to `0`:
`W(n+L) ≤ q·W(n) + e_n` with `0 ≤ q < 1`, `e_n → 0` ⟹ `W → 0`.  The forcing need only vanish, not be
summable — the geometric factor `q < 1` beats it.  Proof by an `ε`–`N` limsup argument.  This is the
convergence driver for the Doeblin block-oscillation contraction.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem tendsto_zero_of_step_contraction {W e : ℕ → ℝ} {q : ℝ} {L : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hWnn : ∀ n, 0 ≤ W n) (hWbd : BddAbove (Set.range W))
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ᶠ n in atTop, W (n + L) ≤ q * W n + e n) :
    Tendsto W atTop (𝓝 0) := by
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  have hbddU : IsBoundedUnder (· ≤ ·) atTop W := hWbd.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop W := hBB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop W := hbddL.isCoboundedUnder_le
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop W := hbddU.isCoboundedUnder_ge
  set Λ := limsup W atTop with hΛ
  have hΛnn : 0 ≤ Λ := le_limsup_of_frequently_le (Frequently.of_forall hWnn) hbddU
  have hkey : ∀ ε : ℝ, 0 < ε → Λ ≤ q * (Λ + ε) + ε := by
    intro ε hε
    have hWev : ∀ᶠ n in atTop, W n < Λ + ε :=
      eventually_lt_of_limsup_lt (by simp only [hΛ]; linarith) hbddU
    have heev : ∀ᶠ n in atTop, e n < ε := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he ε hε
      filter_upwards [eventually_ge_atTop N] with n hn
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero] at hd
      exact lt_of_le_of_lt (le_abs_self _) hd
    have hcomb : ∀ᶠ n in atTop, W (n + L) ≤ q * (Λ + ε) + ε := by
      filter_upwards [hrec, hWev, heev] with n hr hw he2
      have h1 : q * W n ≤ q * (Λ + ε) := mul_le_mul_of_nonneg_left hw.le hq0
      linarith
    have hshift : ∀ᶠ m in atTop, W m ≤ q * (Λ + ε) + ε := by
      obtain ⟨N, hN⟩ := eventually_atTop.1 hcomb
      filter_upwards [eventually_ge_atTop (N + L)] with m hm
      have hmL : L ≤ m := by omega
      have := hN (m - L) (by omega)
      rwa [Nat.sub_add_cancel hmL] at this
    exact limsup_le_of_le hcobddU hshift
  have hΛq : Λ ≤ q * Λ := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hk := hkey (δ / (q + 1)) (by positivity)
    have hc : (q + 1) * (δ / (q + 1)) = δ := by field_simp
    nlinarith [hk, hc]
  have hΛ0 : Λ = 0 := by nlinarith [hΛnn, hΛq, hq1]
  have hliminf0 : liminf W atTop = 0 := by
    have hge : 0 ≤ liminf W atTop :=
      le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hWnn)
    have hle : liminf W atTop ≤ limsup W atTop := liminf_le_limsup hbddU hbddL
    rw [← hΛ, hΛ0] at hle
    linarith
  exact tendsto_of_liminf_eq_limsup hliminf0 (by rw [← hΛ]; exact hΛ0) hbddU hbddL

/-- **Variable-step contraction (antitone form).**  When `W` is antitone and bounded below by `0`, a
geometric contraction `W(R + A R) ≤ q·W R + e R` with `0 ≤ q < 1`, `e → 0` and `A R → ∞` (so the
contraction couples `W` to its own tail at `R + A R → ∞`) forces `W → 0`.  Much easier than the
fixed-step limsup argument: an antitone `W ≥ 0` converges to `ℓ := ⨅ W ≥ 0`, both sides of the
recursion tend to limits, and passing to the limit gives `ℓ ≤ q·ℓ`, hence `ℓ = 0`. -/
theorem tendsto_zero_of_variable_step_contraction
    {W e : ℕ → ℝ} {q : ℝ} {A : ℕ → ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hWnn : ∀ R, 0 ≤ W R) (hWbd : BddAbove (Set.range W))
    (hWmono : Antitone W)
    (hApos : ∀ᶠ R in atTop, 1 ≤ A R)
    (hAunbounded : Tendsto A atTop atTop)
    (hAsublinear : ∀ᶠ R in atTop, A R ≤ R / 2)
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ᶠ R in atTop, W (R + A R) ≤ q * W R + e R) :
    Tendsto W atTop (𝓝 0) := by
  -- `W` antitone, bounded below by `0` ⟹ converges to `ℓ := ⨅ W ≥ 0`.
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  set ℓ : ℝ := ⨅ R, W R with hℓ
  have hWtend : Tendsto W atTop (𝓝 ℓ) := tendsto_atTop_ciInf hWmono hBB
  -- `ℓ ≥ 0` (infimum of nonnegatives).
  have hℓnn : 0 ≤ ℓ := le_ciInf (fun R => hWnn R)
  -- `R + A R → ∞`, since `A ≥ 0`, so `R ≤ R + A R`.
  have hshiftTop : Tendsto (fun R => R + A R) atTop atTop :=
    tendsto_atTop_mono (fun R => Nat.le_add_right R (A R)) tendsto_id
  -- Hence `W (R + A R) → ℓ` (compose the convergent `W` with `R + A R → ∞`).
  have hWshift : Tendsto (fun R => W (R + A R)) atTop (𝓝 ℓ) := hWtend.comp hshiftTop
  -- RHS `q·W R + e R → q·ℓ + 0 = q·ℓ`.
  have hRHS : Tendsto (fun R => q * W R + e R) atTop (𝓝 (q * ℓ)) := by
    have h1 : Tendsto (fun R => q * W R) atTop (𝓝 (q * ℓ)) := hWtend.const_mul q
    simpa using h1.add he
  -- Pass to the limit in `W (R + A R) ≤ q·W R + e R`: `ℓ ≤ q·ℓ`.
  have hℓle : ℓ ≤ q * ℓ := le_of_tendsto_of_tendsto hWshift hRHS hrec
  -- `(1 − q)·ℓ ≤ 0`, `1 − q > 0`, `ℓ ≥ 0` ⟹ `ℓ = 0`.
  have hℓ0 : ℓ = 0 := by nlinarith [hℓnn, hℓle, hq1]
  rwa [hℓ0] at hWtend

#print axioms tendsto_zero_of_variable_step_contraction

end AnalyticCombinatorics.Ch8.Partitions.Erdos
