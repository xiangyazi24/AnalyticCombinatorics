import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentTwo
import AnalyticCombinatorics.Ch8.Partitions.MassRateBasel

/-!
# Mass-rate campaign: the Riemann-sum `O(1)` bound for `boseReg0`

`|Σ'_{k≥1} boseReg0(tk) − (−1/2)/t| ≤ ∫₀^∞ |boseReg0′|` — right-endpoint Riemann sums of
`boseReg0` with mesh `t` differ from `(1/t)·∫₀^∞ boseReg0 = −1/(2t)` by at most the total
variation, cell by cell via FTC.  This is the brick-22 engine (replaces the lost R12 draft).
Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Global pointwise bound: `|boseReg0 z| ≤ 4e^{−z} + 4/z²` on `(0,∞)`. -/
lemma boseReg0_abs_le_global {z : ℝ} (hz : 0 < z) :
    |boseReg0 z| ≤ 4 * Real.exp (-z) + 4 / z ^ 2 := by
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 := boseReg0_bdd_near_zero hz hz1
    have h2 : (4:ℝ) ≤ 4 / z ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : 0 < Real.exp (-z) := Real.exp_pos _
    linarith
  · have h1 := boseReg0_tail_bound hz1.le
    have h2 : |boseReg0 z| ≤ 4 * Real.exp (-z) + 1 / z ^ 2 := h1
    have h3 : (1:ℝ) / z ^ 2 ≤ 4 / z ^ 2 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith

/-- Summability of the sample sums `Σ_k boseReg0(t(k+1))`. -/
lemma summable_boseReg0_samples {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ => boseReg0 (t * ((k : ℝ) + 1))) := by
  have hr1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hr0 : (0:ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
  -- dominator: 4e^{−t(k+1)} + 4/(t(k+1))²
  have hgeo : Summable (fun k : ℕ => 4 * Real.exp (-t) ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left 4
    exact (summable_nat_add_iff 1).mpr h
  have hbasel : Summable (fun k : ℕ => 4 / (t * ((k : ℝ) + 1)) ^ 2) := by
    have hb0 : Summable (fun n : ℕ => (((n : ℝ) ^ (2:ℝ))⁻¹)) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hb1 := (summable_nat_add_iff 1).mpr hb0
    have hb : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
      refine hb1.congr fun k => ?_
      have hc : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
      rw [hc, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hb2 := hb.mul_left (4 / t ^ 2)
    refine hb2.congr fun k => ?_
    field_simp
  have hdom := hgeo.add hbasel
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hdom
  have hkpos : (0:ℝ) < t * ((k : ℝ) + 1) := by positivity
  have hglob := boseReg0_abs_le_global hkpos
  rw [Real.norm_eq_abs]
  have hexp : Real.exp (-(t * ((k : ℝ) + 1))) = Real.exp (-t) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc |boseReg0 (t * ((k : ℝ) + 1))|
      ≤ 4 * Real.exp (-(t * ((k : ℝ) + 1))) + 4 / (t * ((k : ℝ) + 1)) ^ 2 := hglob
    _ = 4 * Real.exp (-t) ^ (k + 1) + 4 / (t * ((k : ℝ) + 1)) ^ 2 := by rw [hexp]

/-- The mesh-`t` cell. -/
def cell (t : ℝ) (k : ℕ) : Set ℝ := Set.Ioc (t * (k : ℝ)) (t * ((k : ℝ) + 1))

lemma cell_measurable (t : ℝ) (k : ℕ) : MeasurableSet (cell t k) := measurableSet_Ioc

lemma cell_subset_Ioi {t : ℝ} (ht : 0 < t) (k : ℕ) : cell t k ⊆ Set.Ioi 0 := by
  intro x hx
  have h1 : t * (k : ℝ) < x := hx.1
  have h2 : (0:ℝ) ≤ t * (k : ℝ) := by positivity
  exact Set.mem_Ioi.mpr (lt_of_le_of_lt h2 h1)

lemma cell_pairwise_disjoint {t : ℝ} (ht : 0 < t) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => cell t k)) := by
  have key : ∀ {i j : ℕ}, i < j → Disjoint (cell t i) (cell t j) := by
    intro i j h
    rw [Set.disjoint_left]
    intro x hxi hxj
    have h1 : x ≤ t * ((i : ℝ) + 1) := hxi.2
    have h2 : t * (j : ℝ) < x := hxj.1
    have h3 : (i : ℝ) + 1 ≤ (j : ℝ) := by
      have hn : (i : ℕ) + 1 ≤ j := h
      exact_mod_cast hn
    nlinarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact (key h).symm

lemma iUnion_cell {t : ℝ} (ht : 0 < t) : (⋃ k : ℕ, cell t k) = Set.Ioi 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩
    exact cell_subset_Ioi ht k hk
  · intro hx
    have hxt : 0 < x / t := by positivity
    set n := ⌈x / t⌉₊ with hndef
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
    refine ⟨n - 1, ?_, ?_⟩
    · -- t·(n−1) < x
      have hlt : ((n : ℝ) - 1) < x / t := by
        have h := Nat.ceil_lt_add_one hxt.le
        have h2 : (n : ℝ) < x / t + 1 := by
          rw [hndef]
          exact_mod_cast h
        linarith
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have : (1:ℕ) ≤ n := hn1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      calc t * ((n : ℝ) - 1) < t * (x / t) := by
            apply mul_lt_mul_of_pos_left hlt ht
        _ = x := by field_simp
    · -- x ≤ t·((n−1)+1)
      have hle : x / t ≤ (n : ℝ) := Nat.le_ceil _
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        have : (1:ℕ) ≤ n := hn1
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      calc x = t * (x / t) := by field_simp
        _ ≤ t * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_left hle ht.le

/-- Cell decomposition of `∫ boseReg0`. -/
lemma hasSum_cell_boseReg0 {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ∫ x in cell t k, boseReg0 x)
      (∫ x in Set.Ioi 0, boseReg0 x) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := boseReg0)
    (fun k => cell_measurable t k) (cell_pairwise_disjoint ht)
    (by rw [iUnion_cell ht]; exact boseReg0_integrable_Ioi)
  rwa [iUnion_cell ht] at h

/-- Cell decomposition of `∫ |boseReg0′|`. -/
lemma hasSum_cell_absDeriv {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => ∫ x in cell t k, |boseReg0Deriv x|)
      (∫ x in Set.Ioi 0, |boseReg0Deriv x|) := by
  have h := hasSum_integral_iUnion (μ := volume) (f := fun x => |boseReg0Deriv x|)
    (fun k => cell_measurable t k) (cell_pairwise_disjoint ht)
    (by rw [iUnion_cell ht]; exact boseReg0Deriv_integrable_Ioi.abs)
  rwa [iUnion_cell ht] at h

/-- **Cell FTC error**: right-endpoint sample vs cell integral. -/
lemma cell_error {t : ℝ} (ht : 0 < t) (k : ℕ) :
    |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|
      ≤ t * ∫ x in cell t k, |boseReg0Deriv x| := by
  set a := t * (k : ℝ) with hadef
  set b := t * ((k : ℝ) + 1) with hbdef
  have hab : a < b := by
    rw [hadef, hbdef]
    nlinarith
  have ha0 : 0 ≤ a := by positivity
  have hvol : b - a = t := by
    rw [hadef, hbdef]
    ring
  have hcell : cell t k = Set.Ioc a b := rfl
  -- integrability of boseReg0 and |boseReg0Deriv| on the cell
  have hint_f : IntegrableOn boseReg0 (Set.Ioc a b) :=
    boseReg0_integrable_Ioi.mono_set (by
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_le_of_lt ha0 hx.1))
  have hint_d : IntegrableOn (fun x => |boseReg0Deriv x|) (Set.Ioc a b) :=
    (boseReg0Deriv_integrable_Ioi.mono_set (by
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_le_of_lt ha0 hx.1))).abs
  -- pointwise: |f(b) − f(x)| ≤ ∫_cell |f'| for x in the cell
  have hptwise : ∀ x ∈ Set.Ioc a b,
      |boseReg0 b - boseReg0 x| ≤ ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt ha0 hx.1
    have hxb : x ≤ b := hx.2
    have hftc : ∫ y in x..b, boseReg0Deriv y = boseReg0 b - boseReg0 x := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro y hy
        rw [Set.uIcc_of_le hxb] at hy
        exact boseReg0_hasDerivAt (lt_of_lt_of_le hx0 hy.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxb]
        exact boseReg0Deriv_integrable_Ioi.mono_set (by
          intro y hy
          exact Set.mem_Ioi.mpr (lt_of_lt_of_le hx0 (le_of_lt hy.1)))
    rw [← hftc]
    have h1 : |∫ y in x..b, boseReg0Deriv y| ≤ ∫ y in x..b, |boseReg0Deriv y| := by
      exact intervalIntegral.abs_integral_le_integral_abs hxb
    have h2 : ∫ y in x..b, |boseReg0Deriv y| ≤ ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
      rw [intervalIntegral.integral_of_le hxb]
      apply setIntegral_mono_set hint_d
      · filter_upwards with y
        exact abs_nonneg _
      · apply HasSubset.Subset.eventuallyLE
        intro y hy
        exact ⟨lt_of_le_of_lt hx.1.le hy.1, hy.2⟩
    linarith
  -- t·f(b) = ∫_cell f(b)
  have hvolr : volume.real (Set.Ioc a b) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    exact hvol
  have hconst : ∫ _x in Set.Ioc a b, boseReg0 b = t * boseReg0 b := by
    rw [setIntegral_const, hvolr, smul_eq_mul]
  have hint_c : IntegrableOn (fun _ : ℝ => boseReg0 b) (Set.Ioc a b) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hsub : (∫ x in Set.Ioc a b, (boseReg0 b - boseReg0 x))
      = t * boseReg0 b - ∫ x in Set.Ioc a b, boseReg0 x := by
    rw [integral_sub hint_c hint_f, hconst]
  rw [hcell, ← hsub]
  have habs : |∫ x in Set.Ioc a b, (boseReg0 b - boseReg0 x)|
      ≤ ∫ x in Set.Ioc a b, |boseReg0 b - boseReg0 x| :=
    abs_integral_le_integral_abs
  have hmono : ∫ x in Set.Ioc a b, |boseReg0 b - boseReg0 x|
      ≤ ∫ _x in Set.Ioc a b, (∫ y in Set.Ioc a b, |boseReg0Deriv y|) := by
    apply setIntegral_mono_on
    · exact (hint_c.sub hint_f).abs
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · exact measurableSet_Ioc
    · exact hptwise
  have hconst2 : ∫ _x in Set.Ioc a b, (∫ y in Set.Ioc a b, |boseReg0Deriv y|)
      = t * ∫ y in Set.Ioc a b, |boseReg0Deriv y| := by
    rw [setIntegral_const, hvolr, smul_eq_mul]
  rw [hconst2] at hmono
  linarith

/-- **The Riemann-sum `O(1)` bound** (brick-22 engine):
`|Σ'_{k≥1} boseReg0(tk) − (−1/2)/t| ≤ ∫₀^∞ |boseReg0′|`. -/
theorem riemann_boseReg0_bound {t : ℝ} (ht : 0 < t) :
    |(∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) - (-(1:ℝ)/2) / t|
      ≤ ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
  classical
  set g : ℕ → ℝ := (fun k : ℕ => if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) with hgdef
  have hsamp := summable_boseReg0_samples ht
  have hshift_eq : ∀ k : ℕ, g (k + 1) = boseReg0 (t * ((k : ℝ) + 1)) := by
    intro k
    have hbeta : g (k + 1)
        = if k + 1 = 0 then (0:ℝ) else boseReg0 (t * (((k + 1 : ℕ)) : ℝ)) := rfl
    rw [hbeta, if_neg (Nat.succ_ne_zero k)]
    congr 1
    push_cast
    ring
  have hguard : Summable g := by
    rw [← summable_nat_add_iff 1]
    refine hsamp.congr fun k => ?_
    exact (hshift_eq k).symm
  have htsum_shift : ∑' k : ℕ, g k = ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)) := by
    rw [hguard.tsum_eq_zero_add]
    have hg0 : g 0 = 0 := rfl
    rw [hg0, zero_add]
    exact tsum_congr hshift_eq
  -- the two HasSums
  have hC : HasSum (fun k : ℕ => t * boseReg0 (t * ((k : ℝ) + 1)))
      (t * ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1))) :=
    hsamp.hasSum.mul_left t
  have hD := hasSum_cell_boseReg0 ht
  have hE := hC.sub hD
  have hVsum := hasSum_cell_absDeriv ht
  -- error comparison
  have herr : ∀ k : ℕ,
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|
        ≤ t * ∫ x in cell t k, |boseReg0Deriv x| := fun k => cell_error ht k
  have habs_summable : Summable (fun k : ℕ =>
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) herr (hVsum.summable.mul_left t)
  have hbound : (∑' k : ℕ,
      |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x|)
        ≤ t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
    have h1 := habs_summable.tsum_le_tsum herr (hVsum.summable.mul_left t)
    have h2 : (∑' k : ℕ, t * ∫ x in cell t k, |boseReg0Deriv x|)
        = t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
      rw [tsum_mul_left, hVsum.tsum_eq]
    linarith
  have htri : |t * (∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)))
        - ∫ x in Set.Ioi 0, boseReg0 x|
      ≤ ∑' k : ℕ,
        |t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x| := by
    rw [← hE.tsum_eq]
    have hnorm : |∑' k : ℕ,
        (t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x)|
        = ‖∑' k : ℕ,
        (t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x)‖ :=
      (Real.norm_eq_abs _).symm
    rw [hnorm]
    have hns : Summable (fun k : ℕ =>
        ‖t * boseReg0 (t * ((k : ℝ) + 1)) - ∫ x in cell t k, boseReg0 x‖) := by
      refine habs_summable.congr fun k => ?_
      rw [Real.norm_eq_abs]
    exact le_trans (norm_tsum_le_tsum_norm hns)
      (le_of_eq (tsum_congr fun k => Real.norm_eq_abs _))
  have hfinal : |t * (∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)))
        - ∫ x in Set.Ioi 0, boseReg0 x|
      ≤ t * ∫ x in Set.Ioi 0, |boseReg0Deriv x| := le_trans htri hbound
  -- conclude
  rw [htsum_shift]
  set S := ∑' k : ℕ, boseReg0 (t * ((k : ℝ) + 1)) with hSdef
  have hIval : ∫ x in Set.Ioi (0:ℝ), boseReg0 x = -(1 / 2 : ℝ) := integral_boseReg0_Ioi
  rw [hIval] at hfinal
  have hgoal_eq : S - (-(1:ℝ)/2) / t = (t * S - (-(1 / 2 : ℝ))) / t := by
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  nlinarith [hfinal]

/-- **M₀ weak asymptotics** (brick 22): `|M₀(t) − (π²/6)/t² + 1/(2t)| ≤ ∫₀^∞|boseReg0′|`. -/
theorem sigmaMoment_zero_asymp_weak {t : ℝ} (ht : 0 < t) :
    |sigmaMoment 0 t - (Real.pi ^ 2 / 6) / t ^ 2 + 1 / (2 * t)|
      ≤ ∫ x in Set.Ioi 0, |boseReg0Deriv x| := by
  classical
  have hML := sigmaMoment_zero_lambert ht
  -- summability of the two pieces
  have hsq0 : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / ((k : ℝ)) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    have hb0 : Summable (fun n : ℕ => (((n : ℝ) ^ (2:ℝ))⁻¹)) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hb1 := (summable_nat_add_iff 1).mpr hb0
    refine hb1.congr fun k => ?_
    rw [if_neg (Nat.succ_ne_zero k), show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  have hsq : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else 1 / (t * (k : ℝ)) ^ 2) := by
    have h2 := hsq0.mul_left (1 / t ^ 2)
    refine h2.congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
      field_simp
  have hreg : Summable (fun k : ℕ => if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_boseReg0_samples ht).congr fun k => ?_
    rw [if_neg (Nat.succ_ne_zero k)]
    congr 2
    push_cast
    ring
  -- termwise kernel split
  have hsplit : ∀ k : ℕ, (if k = 0 then (0:ℝ) else boseKernel (t * (k : ℝ)))
      = (if k = 0 then (0:ℝ) else 1 / (t * (k : ℝ)) ^ 2)
        + (if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, if_neg hk, boseKernel_eq_inv_sq_add_reg]
  have hsum_eq : (∑' k : ℕ, if k = 0 then (0:ℝ) else boseKernel (t * (k : ℝ)))
      = (Real.pi ^ 2 / 6) / t ^ 2
        + ∑' k : ℕ, (if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ))) := by
    rw [tsum_congr hsplit, hsq.tsum_add hreg, tsum_if_inv_sq_scaled ht.ne']
  rw [hML, hsum_eq]
  have harr : (Real.pi ^ 2 / 6) / t ^ 2
        + (∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ)))
        - (Real.pi ^ 2 / 6) / t ^ 2 + 1 / (2 * t)
      = (∑' k : ℕ, if k = 0 then (0:ℝ) else boseReg0 (t * (k : ℝ)))
        - (-(1:ℝ)/2) / t := by
    field_simp
    ring
  rw [harr]
  exact riemann_boseReg0_bound ht

end AnalyticCombinatorics.Ch8.Partitions.Erdos
