import AnalyticCombinatorics.Ch8.Partitions.ErdosMinorization
import AnalyticCombinatorics.Ch8.Partitions.VarianceLower

/-!
# Concrete `v0`: single-chain jump-window mass for the Erdős kernel (renewal route B)

Builds toward the positive local-variance input `v0 > 0`.  `Pker_subwindow_mass` lower-bounds the
single-chain `Pker x ·` mass on a jump sub-window `[a, b] ⊆ [⌊√x⌋, 2⌊√x⌋]` via the banked per-term
`Pker_lower`.  Splitting the window into a LOW and a HIGH jump sub-window gives two separated
ρ-decrement clumps, which `product_locVar_ge` (VarianceLower) turns into `v0 > 0`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Single-chain mass on a jump sub-window `[a,b] ⊆ [s, 2s]` (`s = ⌊√x⌋`), via `Pker_lower`:
each term is `≥ a·e^{-2C}/(2x)`, and there are `b−a+1` of them. -/
lemma Pker_subwindow_mass {x : ℕ} (hx16 : 16 ≤ x)
    (hkmx : kernelMass x ≤ 2) (hkmx0 : 0 < kernelMass x)
    {a b : ℕ} (ha : Nat.sqrt x ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2 * Nat.sqrt x) :
    ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * x))
      ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
  have hCpos := C_pos
  set s := Nat.sqrt x with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; calc 4 = Nat.sqrt 16 := by norm_num
      _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx16
  have hssx : s * s ≤ x := by rw [hs, ← pow_two]; exact Nat.sqrt_le' x
  have h2sx : 2 * s ≤ x := by nlinarith [hssx, hs4]
  have h2s1x : 2 * s + 1 ≤ x := by nlinarith [hssx, hs4]
  have hbx : b ≤ x := le_trans hb2 h2sx
  have hax : a ≤ x := le_trans hab hbx
  have ha1 : 1 ≤ a := le_trans (by omega) ha
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hsqrtx : (0 : ℝ) < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hxpos
  have hsx2 : (s : ℝ) * (s : ℝ) ≤ (x : ℝ) := by exact_mod_cast hssx
  have hsle_sqrt : (s : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (s : ℝ) = Real.sqrt ((s : ℝ) * (s : ℝ)) from (Real.sqrt_mul_self (by positivity)).symm]
    exact Real.sqrt_le_sqrt hsx2
  -- per-term lower bound, uniform over the window
  have hperterm : ∀ k ∈ Finset.Icc (x - b) (x - a),
      (a : ℝ) * Real.exp (-C * 2) / (2 * x) ≤ Pker x k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1', hk2'⟩ := hk
    have hk_lt_x : k < x := by omega
    have hk_ge1 : 1 ≤ k := by omega
    have hxk_cast : ((x - k : ℕ) : ℝ) = (x : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hk_lt_x.le]
    -- jump bounds: a ≤ x - k ≤ b
    have hjlo : a ≤ x - k := by omega
    have hjhi : x - k ≤ b := by omega
    -- J = a ≤ (x-k)
    have hJ : (a : ℝ) ≤ ((x - k : ℕ) : ℝ) := by exact_mod_cast hjlo
    -- T = 2 : √x − √k ≤ 2
    have hT : Real.sqrt (x : ℝ) - Real.sqrt (k : ℝ) ≤ 2 := by
      refine le_trans (sqrt_sub_le hk_ge1 hk_lt_x.le) ?_
      rw [div_le_iff₀ hsqrtx]
      have hxk2s : ((x : ℝ) - (k : ℝ)) ≤ 2 * (s : ℝ) := by
        rw [← hxk_cast]; exact_mod_cast le_trans hjhi hb2
      nlinarith [hxk2s, hsle_sqrt, hsqrtx]
    exact Pker_lower hk_ge1 hk_lt_x hkmx hkmx0 (by positivity) hJ hT
  -- sum ≥ card • perterm
  have hcard : (Finset.Icc (x - b) (x - a)).card = b - a + 1 := by
    rw [Nat.card_Icc]
    omega
  calc ((b - a + 1 : ℕ) : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * x))
      = ((Finset.Icc (x - b) (x - a)).card : ℝ) * ((a : ℝ) * Real.exp (-C * 2) / (2 * x)) := by
        rw [hcard]
    _ ≤ ∑ k ∈ Finset.Icc (x - b) (x - a), Pker x k := by
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ hperterm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
