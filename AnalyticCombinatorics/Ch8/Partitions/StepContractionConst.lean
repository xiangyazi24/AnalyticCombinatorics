import Mathlib

/-!
# R7 Fact B via Doeblin: the multi-scale step contraction (constant forcing)

The escape-split engine `tendsto_zero_of_step_contraction` needs the forcing `e(R) → 0`.  For the Erdős
kernel the escape mass below a *fixed* band `{rnk ≥ R−B}` is `~ e^{−cB}`, a CONSTANT in `R` (a normalized
tail), so that engine cannot apply with fixed `B`.  The fix is multi-scale: for each band width `B` the
contraction `W(n+L) ≤ q·W n + c` (constant `c = c(B)`) gives only `limsup W ≤ c/(1−q)`, but letting
`B → ∞` drives the bound to `0`.  This file provides the two engine pieces:

* `limsup_le_of_step_contraction_const` — bounded forcing ⟹ bounded `limsup`;
* `tendsto_zero_of_limsup_le_all` — a `limsup` dominated by a null sequence of bounds ⟹ `→ 0`.

Together they drive the tail oscillation to `0` from the *family* of band contractions.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `L`-step contraction with a CONSTANT forcing bounds the `limsup`: `W(n+L) ≤ q·W n + c` ⟹
`limsup W ≤ c/(1−q)`. -/
theorem limsup_le_of_step_contraction_const {W : ℕ → ℝ} {q c : ℝ} {L : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hWnn : ∀ n, 0 ≤ W n) (hWbd : BddAbove (Set.range W))
    (hrec : ∀ᶠ n in atTop, W (n + L) ≤ q * W n + c) :
    limsup W atTop ≤ c / (1 - q) := by
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  have hbddU : IsBoundedUnder (· ≤ ·) atTop W := hWbd.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop W := hBB.isBoundedUnder_of_range
  have hcobddU : IsCoboundedUnder (· ≤ ·) atTop W := hbddL.isCoboundedUnder_le
  set Λ := limsup W atTop with hΛ
  have hkey : ∀ ε : ℝ, 0 < ε → Λ ≤ q * (Λ + ε) + c := by
    intro ε hε
    have hWev : ∀ᶠ n in atTop, W n < Λ + ε :=
      eventually_lt_of_limsup_lt (by simp only [hΛ]; linarith) hbddU
    have hcomb : ∀ᶠ n in atTop, W (n + L) ≤ q * (Λ + ε) + c := by
      filter_upwards [hrec, hWev] with n hr hw
      have h1 : q * W n ≤ q * (Λ + ε) := mul_le_mul_of_nonneg_left hw.le hq0
      linarith
    have hshift : ∀ᶠ m in atTop, W m ≤ q * (Λ + ε) + c := by
      obtain ⟨N, hN⟩ := eventually_atTop.1 hcomb
      filter_upwards [eventually_ge_atTop (N + L)] with m hm
      have hmL : L ≤ m := by omega
      have := hN (m - L) (by omega)
      rwa [Nat.sub_add_cancel hmL] at this
    exact limsup_le_of_le hcobddU hshift
  have hΛq : Λ ≤ q * Λ + c := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hk := hkey (δ / (q + 1)) (by positivity)
    have hcc : (q + 1) * (δ / (q + 1)) = δ := by field_simp
    nlinarith [hk, hcc]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - q)]
  nlinarith [hΛq]

/-- A `limsup` bounded by every term of a null sequence is `0`, so a nonnegative bounded sequence with
this property converges to `0`. -/
theorem tendsto_zero_of_limsup_le_all {W B : ℕ → ℝ}
    (hWnn : ∀ n, 0 ≤ W n) (hWbd : BddAbove (Set.range W))
    (hlimsup : ∀ k : ℕ, limsup W atTop ≤ B k)
    (hB : Tendsto B atTop (𝓝 0)) :
    Tendsto W atTop (𝓝 0) := by
  have hBB : BddBelow (Set.range W) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hWnn n⟩
  have hbddU : IsBoundedUnder (· ≤ ·) atTop W := hWbd.isBoundedUnder_of_range
  have hbddL : IsBoundedUnder (· ≥ ·) atTop W := hBB.isBoundedUnder_of_range
  have hcobddL : IsCoboundedUnder (· ≥ ·) atTop W := hbddU.isCoboundedUnder_ge
  have hΛnn : 0 ≤ limsup W atTop := le_limsup_of_frequently_le (Frequently.of_forall hWnn) hbddU
  have hle : limsup W atTop ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hB (Eventually.of_forall hlimsup)
  have hL0 : limsup W atTop = 0 := le_antisymm hle hΛnn
  have hliminf_nn : 0 ≤ liminf W atTop :=
    le_liminf_of_le hcobddL (Eventually.of_forall hWnn)
  have hliminf_le : liminf W atTop ≤ limsup W atTop := liminf_le_limsup hbddU hbddL
  have hl0 : liminf W atTop = 0 := le_antisymm (by rw [← hL0]; exact hliminf_le) hliminf_nn
  exact tendsto_of_liminf_eq_limsup hl0 hL0 hbddU hbddL

end AnalyticCombinatorics.Ch8.Partitions.Erdos
