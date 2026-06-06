import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateRiemann
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentOneAsymp
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwoAsymp

/-!
# Mass-rate campaign: §6 the √n-cancellation in the second-order approximation

`kernelMassApprox2 n = (1/n)·M₀(t) + (1/n²)·M₁(t) − (C/(8n²√n))·M₂(t)` at `t = lam/√n` satisfies
`|kernelMassApprox2 n − 1| ≤ K/n` eventually: the three weak asymptotics give a leading `1`, the
`1/√n` terms cancel exactly (`mass_rate_sqrt_coeff_cancel`, `massLam_sq` i.e. `lam²=π²/6`), and all
remainders are `O(1/n)`.  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The second-order approximation to the kernel mass (R8 §5). -/
noncomputable def kernelMassApprox2 (n : ℕ) : ℝ :=
  let t := massLam / Real.sqrt (n : ℝ)
  (1 / (n : ℝ)) * sigmaMoment 0 t
  + (1 / (n : ℝ) ^ 2) * sigmaMoment 1 t
  - (C / (8 * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ))) * sigmaMoment 2 t

/-- **√n-cancellation** (R8 §6): `|kernelMassApprox2 n − 1| ≤ K/n` eventually. -/
theorem kernelMassApprox2_cancel_sqrt_term :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in Filter.atTop,
      |kernelMassApprox2 n - 1| ≤ K / (n : ℝ) := by
  set Z : ℝ := Real.pi ^ 2 / 6 with hZdef
  set lam : ℝ := massLam with hlamdef
  have hlam0 : 0 < lam := massLam_pos
  have hlam2 : lam ^ 2 = Z := massLam_sq
  set I₀ : ℝ := ∫ x in Set.Ioi (0:ℝ), |boseReg0Deriv x| with hI0def
  have hI0nn : 0 ≤ I₀ := by
    rw [hI0def]; exact MeasureTheory.integral_nonneg (fun x => abs_nonneg _)
  set K₂ : ℝ := (3600 * 2 ^ 3 + (6 / (1 - Real.exp (-1)) ^ 4) * (Nat.factorial 2) * 4 ^ 3 + 2 * 6)
    with hK2def
  have hK2nn : 0 ≤ K₂ := by rw [hK2def]; positivity
  refine ⟨I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1, ?_, ?_⟩
  · have hp1 : (0:ℝ) ≤ 388 / lam ^ 2 := by positivity
    have hp2 : (0:ℝ) ≤ C * K₂ / (8 * lam ^ 3) :=
      div_nonneg (mul_nonneg C_pos.le hK2nn) (by positivity)
    linarith [hI0nn, hp1, hp2]
  -- eventually n ≥ max(1, lam²) so that t = lam/√n ≤ 1 and n ≥ 1
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (1:ℝ) ≤ (n : ℝ) ∧ lam ^ 2 ≤ (n : ℝ) := by
    rw [eventually_atTop]
    refine ⟨max 1 ⌈lam ^ 2⌉₊, fun n hn => ?_⟩
    constructor
    · have : (1:ℕ) ≤ n := le_trans (le_max_left _ _) hn
      exact_mod_cast this
    · have h2 : (⌈lam ^ 2⌉₊ : ℝ) ≤ (n : ℝ) := by
        have : ⌈lam ^ 2⌉₊ ≤ n := le_trans (le_max_right _ _) hn
        exact_mod_cast this
      exact le_trans (Nat.le_ceil _) h2
  filter_upwards [hev] with n hn
  obtain ⟨hn1, hnlam⟩ := hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  set s : ℝ := Real.sqrt (n : ℝ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hnpos
  have hs2 : s ^ 2 = (n : ℝ) := by rw [hsdef, Real.sq_sqrt hnpos.le]
  set t : ℝ := lam / s with htdef
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hs0]
    -- lam ≤ s = √n  ⟺ lam² ≤ n
    rw [← Real.sqrt_sq hlam0.le, hsdef]
    exact Real.sqrt_le_sqrt hnlam
  -- the three asymptotics
  have h0 := sigmaMoment_zero_asymp_weak ht0
  have h1 := sigmaMoment_one_asymp_weak ht0 ht1
  have h2 := sigmaMoment_two_asymp_weak ht0 ht1
  rw [← hI0def] at h0
  rw [← hZdef] at h0 h1 h2
  rw [← hK2def] at h2
  -- abbreviate the three remainders
  set R0 : ℝ := sigmaMoment 0 t - Z / t ^ 2 + 1 / (2 * t) with hR0def
  set R1 : ℝ := sigmaMoment 1 t - 2 * Z / t ^ 3 with hR1def
  set R2 : ℝ := sigmaMoment 2 t - 6 * Z / t ^ 4 with hR2def
  have hR0 : |R0| ≤ I₀ := h0
  have hR1 : |R1| ≤ 388 / t ^ 2 := h1
  have hR2 : |R2| ≤ K₂ / t ^ 3 := h2
  -- powers of t in terms of n
  have htne : t ≠ 0 := ht0.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hlamne : lam ≠ 0 := hlam0.ne'
  have ht2 : t ^ 2 = lam ^ 2 / (n : ℝ) := by rw [htdef, div_pow, ← hs2]
  have ht3 : t ^ 3 = lam ^ 3 / (s * (n : ℝ)) := by
    rw [htdef, div_pow, ← hs2]; field_simp
  have ht4 : t ^ 4 = lam ^ 4 / (n : ℝ) ^ 2 := by rw [htdef, div_pow, ← hs2]; ring
  -- express kernelMassApprox2 n
  have hCval : C = 2 * lam := by rw [hlamdef, massLam]; ring
  have hkey : kernelMassApprox2 n - 1
      = (1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1
        - (C / (8 * (n : ℝ) ^ 2 * s)) * R2
        + ((-(1 / (2 * lam)) + 2 * Z / lam ^ 3 - C * (6 * Z) / (8 * lam ^ 4)) / s) := by
    rw [kernelMassApprox2]
    simp only [← hsdef, ← htdef, ← hlamdef]
    have e0 : sigmaMoment 0 t = R0 + Z / t ^ 2 - 1 / (2 * t) := by rw [hR0def]; ring
    have e1 : sigmaMoment 1 t = R1 + 2 * Z / t ^ 3 := by rw [hR1def]; ring
    have e2 : sigmaMoment 2 t = R2 + 6 * Z / t ^ 4 := by rw [hR2def]; ring
    rw [e0, e1, e2, htdef, hCval, ← hlam2, ← hs2]
    field_simp
    ring
  rw [hkey]
  -- the √n-coefficient vanishes
  have hcancel : -(1 / (2 * lam)) + 2 * Z / lam ^ 3 - C * (6 * Z) / (8 * lam ^ 4) = 0 := by
    rw [hlamdef, hZdef]; exact mass_rate_sqrt_coeff_cancel
  rw [hcancel, zero_div, add_zero]
  -- bound the three remainder terms each by (·)/n
  have hb0 : |(1 / (n : ℝ)) * R0| ≤ I₀ / (n : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (n:ℝ))]
    rw [div_mul_eq_mul_div, one_mul]
    gcongr
  have hb1 : |(1 / (n : ℝ) ^ 2) * R1| ≤ (388 / lam ^ 2) / (n : ℝ) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have : (1 / (n : ℝ) ^ 2) * (388 / t ^ 2) = (388 / lam ^ 2) / (n : ℝ) := by
      rw [ht2]; field_simp
    calc (1 / (n : ℝ) ^ 2) * |R1| ≤ (1 / (n : ℝ) ^ 2) * (388 / t ^ 2) :=
          mul_le_mul_of_nonneg_left hR1 (by positivity)
      _ = (388 / lam ^ 2) / (n : ℝ) := this
  have hb2 : |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| ≤ (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := by
    have hCpos : 0 < C := C_pos
    rw [abs_mul, abs_of_pos (by positivity)]
    have heq : (C / (8 * (n : ℝ) ^ 2 * s)) * (K₂ / t ^ 3) = (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := by
      rw [ht3]; field_simp
    calc (C / (8 * (n : ℝ) ^ 2 * s)) * |R2|
        ≤ (C / (8 * (n : ℝ) ^ 2 * s)) * (K₂ / t ^ 3) :=
          mul_le_mul_of_nonneg_left hR2 (by positivity)
      _ = (C * K₂ / (8 * lam ^ 3)) / (n : ℝ) := heq
  -- assemble
  have htri : |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1 - (C / (8 * (n : ℝ) ^ 2 * s)) * R2|
      ≤ |(1 / (n : ℝ)) * R0| + |(1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
    calc |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1 - (C / (8 * (n : ℝ) ^ 2 * s)) * R2|
        ≤ |(1 / (n : ℝ)) * R0 + (1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      _ ≤ |(1 / (n : ℝ)) * R0| + |(1 / (n : ℝ) ^ 2) * R1| + |(C / (8 * (n : ℝ) ^ 2 * s)) * R2| := by
          gcongr
          exact abs_add_le _ _
  have hsum : I₀ / (n : ℝ) + (388 / lam ^ 2) / (n : ℝ) + (C * K₂ / (8 * lam ^ 3)) / (n : ℝ)
      ≤ (I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1) / (n : ℝ) := by
    have heq : (I₀ + 388 / lam ^ 2 + C * K₂ / (8 * lam ^ 3) + 1) / (n : ℝ)
        = (I₀ / (n : ℝ) + (388 / lam ^ 2) / (n : ℝ) + (C * K₂ / (8 * lam ^ 3)) / (n : ℝ))
          + 1 / (n : ℝ) := by ring
    rw [heq]
    have h1n : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  linarith [htri, hb0, hb1, hb2, hsum]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
