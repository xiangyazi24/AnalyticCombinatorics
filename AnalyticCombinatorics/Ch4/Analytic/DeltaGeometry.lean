import AnalyticCombinatorics.Ch4.Analytic.DeltaDomain
import Mathlib

open Complex

lemma closedBall_subset_deltaDomain {R φ r : ℝ} (hr1 : r < 1) (hrR : r < R)
    (hφ : 0 < φ) (hφ2 : φ < Real.pi / 2) :
    Metric.closedBall (0 : ℂ) r ⊆ DeltaDomainArg R φ := by
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  rw [delta_arg_eq_geom hφ.le hφπ]
  intro z hz
  unfold DeltaDomainGeom
  have hz_norm_le : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  constructor
  · have hz_norm_lt : ‖z‖ < R := lt_of_le_of_lt hz_norm_le hrR
    simpa [Metric.mem_ball, dist_eq_norm] using hz_norm_lt
  · have hz_re_lt_one : z.re < 1 := by
      exact lt_of_le_of_lt (Complex.re_le_norm z) (lt_of_le_of_lt hz_norm_le hr1)
    have hleft : (z - 1).re < 0 := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ, Real.pi_pos], hφ2⟩
    have hright : 0 ≤ Real.cos φ * ‖z - 1‖ :=
      mul_nonneg hcos_pos.le (norm_nonneg _)
    exact lt_of_lt_of_le hleft hright

lemma sphere_subset_deltaDomain {R φ r : ℝ} (hr1 : r < 1) (hrR : r < R)
    (hφ : 0 < φ) (hφ2 : φ < Real.pi / 2) :
    Metric.sphere (0 : ℂ) r ⊆ DeltaDomainArg R φ := by
  exact Metric.sphere_subset_closedBall.trans
    (closedBall_subset_deltaDomain hr1 hrR hφ hφ2)

lemma one_sub_norm_ge_on_circle {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : ‖z‖ = 1 - (1 : ℝ) / n) :
    (1 : ℝ) / n ≤ ‖1 - z‖ := by
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hrev := abs_norm_sub_norm_le (1 : ℂ) z
  have hdiff : ‖(1 : ℂ)‖ - ‖z‖ = (1 : ℝ) / n := by
    rw [norm_one, hz]
    ring
  have hnonneg : 0 ≤ (1 : ℝ) / n := div_nonneg zero_le_one hn_pos.le
  rwa [hdiff, abs_of_nonneg hnonneg] at hrev

lemma local_disk_norm_comparable {κ : ℝ} {z w : ℂ}
    (hw : w ∈ Metric.ball z (κ * ‖1 - z‖)) :
    (1 - κ) * ‖1 - z‖ ≤ ‖1 - w‖ ∧
      ‖1 - w‖ ≤ (1 + κ) * ‖1 - z‖ := by
  have hdist : ‖w - z‖ < κ * ‖1 - z‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  constructor
  · have hrev : ‖1 - z‖ - ‖w - z‖ ≤ ‖1 - w‖ := by
      have h := norm_sub_norm_le (1 - z) (w - z)
      convert h using 1
      ring_nf
    have hpre : (1 - κ) * ‖1 - z‖ ≤ ‖1 - z‖ - ‖w - z‖ := by
      nlinarith [le_of_lt hdist]
    exact hpre.trans hrev
  · have htri : ‖1 - w‖ ≤ ‖1 - z‖ + ‖w - z‖ := by
      calc
        ‖1 - w‖ = ‖(1 - z) + (z - w)‖ := by ring_nf
        _ ≤ ‖1 - z‖ + ‖z - w‖ := norm_add_le _ _
        _ = ‖1 - z‖ + ‖w - z‖ := by simp [norm_sub_rev z w]
    have hpre : ‖1 - z‖ + ‖w - z‖ ≤ (1 + κ) * ‖1 - z‖ := by
      nlinarith [le_of_lt hdist]
    exact htri.trans hpre

lemma local_disk_norm_comparable_half {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    {z w : ℂ} (hw : w ∈ Metric.ball z (κ * ‖1 - z‖)) :
    (1 / 2) * ‖1 - z‖ ≤ ‖1 - w‖ ∧ ‖1 - w‖ ≤ 2 * ‖1 - z‖ := by
  have hcomp := local_disk_norm_comparable hw
  constructor
  · have hleft : (1 / 2 : ℝ) * ‖1 - z‖ ≤ (1 - κ) * ‖1 - z‖ := by
      nlinarith [norm_nonneg (1 - z)]
    exact hleft.trans hcomp.1
  · have hright : (1 + κ) * ‖1 - z‖ ≤ 2 * ‖1 - z‖ := by
      nlinarith [norm_nonneg (1 - z)]
    exact hcomp.2.trans hright

lemma local_disk_avoids_one {κ : ℝ} (hκ : κ < 1) {z w : ℂ} (hz : z ≠ 1)
    (hw : w ∈ Metric.ball z (κ * ‖1 - z‖)) :
    w ≠ 1 := by
  intro hw_eq
  have hdist : ‖w - z‖ < κ * ‖1 - z‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hzpos : 0 < ‖1 - z‖ := by
    rw [norm_pos_iff]
    simpa [sub_eq_zero] using (Ne.symm hz)
  have hdist_eq : ‖w - z‖ = ‖1 - z‖ := by
    rw [hw_eq]
  nlinarith

lemma local_disk_subset_deltaDomain {R R' φ φ' κ : ℝ} (_hRR : R' < R)
    (hφ : 0 < φ) (hφlt : φ < φ') (hφ'2 : φ' < Real.pi / 2)
    (hκ0 : 0 ≤ κ) (_hκ1 : κ < 1)
    (hκR : κ * (1 + R') ≤ R - R')
    (hκAngle : κ * (1 + Real.cos φ) ≤ Real.cos φ - Real.cos φ') {z : ℂ}
    (hz : z ∈ DeltaDomainArg R' φ') :
    Metric.ball z (κ * ‖1 - z‖) ⊆ DeltaDomainArg R φ := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hz_geom : z ∈ DeltaDomainGeom R' φ' := by
    simpa only [delta_arg_eq_geom hφ'.le hφ'π] using hz
  rcases hz_geom with ⟨hzRball, hzangle⟩
  have hzR : ‖z‖ < R' := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzRball
  rw [delta_arg_eq_geom hφ.le hφπ]
  intro w hw
  unfold DeltaDomainGeom
  have hdist : ‖w - z‖ < κ * ‖1 - z‖ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  constructor
  · have h1z_le : ‖1 - z‖ ≤ 1 + R' := by
      calc
        ‖1 - z‖ = ‖(1 : ℂ) + (-z)‖ := by ring_nf
        _ ≤ ‖(1 : ℂ)‖ + ‖-z‖ := norm_add_le _ _
        _ = 1 + ‖z‖ := by simp
        _ ≤ 1 + R' := by linarith
    have hdist_lt : ‖w - z‖ < κ * (1 + R') :=
      lt_of_lt_of_le hdist (mul_le_mul_of_nonneg_left h1z_le hκ0)
    have hw_norm_le : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      calc
        ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
    have hw_norm_lt : ‖w‖ < R := by
      have hsum : ‖z‖ + ‖w - z‖ < R' + κ * (1 + R') := add_lt_add hzR hdist_lt
      have hpre : ‖w‖ < R' + κ * (1 + R') := lt_of_le_of_lt hw_norm_le hsum
      have hmargin : R' + κ * (1 + R') ≤ R := by linarith
      exact lt_of_lt_of_le hpre hmargin
    simpa [Metric.mem_ball, dist_eq_norm] using hw_norm_lt
  · have hcos_pos : 0 < Real.cos φ := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
    have hzangle' : (z - 1).re < Real.cos φ' * ‖1 - z‖ := by
      simpa [norm_sub_rev z 1] using hzangle
    have hre_le : (w - 1).re ≤ (z - 1).re + ‖w - z‖ := by
      calc
        (w - 1).re = ((z - 1) + (w - z)).re := by ring_nf
        _ = (z - 1).re + (w - z).re := by rw [Complex.add_re]
        _ ≤ (z - 1).re + ‖w - z‖ := by linarith [Complex.re_le_norm (w - z)]
    have hpre_lt : (w - 1).re < (Real.cos φ' + κ) * ‖1 - z‖ := by
      calc
        (w - 1).re ≤ (z - 1).re + ‖w - z‖ := hre_le
        _ < Real.cos φ' * ‖1 - z‖ + κ * ‖1 - z‖ := add_lt_add hzangle' hdist
        _ = (Real.cos φ' + κ) * ‖1 - z‖ := by ring
    have hcoeff : Real.cos φ' + κ ≤ Real.cos φ * (1 - κ) := by
      nlinarith [hκAngle]
    have hcoeff_mul : (Real.cos φ' + κ) * ‖1 - z‖ ≤
        Real.cos φ * ((1 - κ) * ‖1 - z‖) := by
      have h := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (1 - z))
      nlinarith
    have hcomp : (1 - κ) * ‖1 - z‖ ≤ ‖1 - w‖ :=
      (local_disk_norm_comparable hw).1
    have htarget : Real.cos φ * ((1 - κ) * ‖1 - z‖) ≤ Real.cos φ * ‖1 - w‖ :=
      mul_le_mul_of_nonneg_left hcomp hcos_pos.le
    have hfinal : (w - 1).re < Real.cos φ * ‖1 - w‖ :=
      hpre_lt.trans_le (hcoeff_mul.trans htarget)
    simpa [norm_sub_rev w 1] using hfinal

noncomputable def deltaLocalKappa (R R' φ φ' : ℝ) : ℝ :=
  min (1 / 2)
    (min ((R - R') / (2 * (1 + R')))
      ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))))

lemma local_disk_subset_deltaDomain_deltaLocalKappa {R R' φ φ' : ℝ} (hR'0 : 0 < R')
    (hRR : R' < R) (hφ : 0 < φ) (hφlt : φ < φ')
    (hφ'2 : φ' < Real.pi / 2) {z : ℂ} (hz : z ∈ DeltaDomainArg R' φ') :
    Metric.ball z (deltaLocalKappa R R' φ φ' * ‖1 - z‖) ⊆ DeltaDomainArg R φ := by
  have hφ' : 0 < φ' := lt_trans hφ hφlt
  have hφπ : φ < Real.pi := by linarith [hφlt, hφ'2, Real.pi_pos]
  have hφ'π : φ' < Real.pi := by linarith [hφ'2, Real.pi_pos]
  have hcos_lt : Real.cos φ' < Real.cos φ := by
    exact (Real.strictAntiOn_cos.lt_iff_gt
      (Set.mem_Icc.mpr ⟨hφ'.le, hφ'π.le⟩)
      (Set.mem_Icc.mpr ⟨hφ.le, hφπ.le⟩)).2 hφlt
  have hcos_pos : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hφ, Real.pi_pos], by linarith [hφlt, hφ'2]⟩
  have hRdiff_pos : 0 < R - R' := by linarith
  have hdenR_pos : 0 < 2 * (1 + R') := by nlinarith
  have hdenA_pos : 0 < 2 * (1 + Real.cos φ) := by nlinarith
  have hκ0 : 0 ≤ deltaLocalKappa R R' φ φ' := by
    unfold deltaLocalKappa
    apply le_min
    · norm_num
    · apply le_min
      · exact div_nonneg hRdiff_pos.le hdenR_pos.le
      · exact div_nonneg (sub_nonneg.mpr hcos_lt.le) hdenA_pos.le
  have hκ1 : deltaLocalKappa R R' φ φ' < 1 := by
    have hle : deltaLocalKappa R R' φ φ' ≤ 1 / 2 := by
      unfold deltaLocalKappa
      exact min_le_left _ _
    linarith
  have hκR : deltaLocalKappa R R' φ φ' * (1 + R') ≤ R - R' := by
    have hle_rad : deltaLocalKappa R R' φ φ' ≤ (R - R') / (2 * (1 + R')) := by
      unfold deltaLocalKappa
      exact (min_le_right _ _).trans (min_le_left _ _)
    have h1R_pos : 0 < 1 + R' := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle_rad h1R_pos.le
    have hrad_mul : ((R - R') / (2 * (1 + R'))) * (1 + R') = (R - R') / 2 := by
      field_simp [h1R_pos.ne']
    calc
      deltaLocalKappa R R' φ φ' * (1 + R')
          ≤ ((R - R') / (2 * (1 + R'))) * (1 + R') := hmul
      _ = (R - R') / 2 := hrad_mul
      _ ≤ R - R' := by linarith
  have hκAngle : deltaLocalKappa R R' φ φ' * (1 + Real.cos φ) ≤
      Real.cos φ - Real.cos φ' := by
    have hle_ang : deltaLocalKappa R R' φ φ' ≤
        (Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ)) := by
      unfold deltaLocalKappa
      exact (min_le_right _ _).trans (min_le_right _ _)
    have h1cos_pos : 0 < 1 + Real.cos φ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle_ang h1cos_pos.le
    have hang_mul : ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))) *
        (1 + Real.cos φ) = (Real.cos φ - Real.cos φ') / 2 := by
      field_simp [h1cos_pos.ne']
    calc
      deltaLocalKappa R R' φ φ' * (1 + Real.cos φ)
          ≤ ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))) *
              (1 + Real.cos φ) := hmul
      _ = (Real.cos φ - Real.cos φ') / 2 := hang_mul
      _ ≤ Real.cos φ - Real.cos φ' := by linarith
  exact local_disk_subset_deltaDomain hRR hφ hφlt hφ'2 hκ0 hκ1 hκR hκAngle hz
