import Mathlib

open Complex Filter
open scoped Topology

/--
A Δ-domain is the central object of Flajolet--Sedgewick Chapter VI singularity
analysis. This file provides the geometric scaffolding and standard-function
analyticity used by the general transfer theorem (`transfer_theorem` in
`TransferGeneral.lean`), which derives the `(1 - z)^{-α}` coefficient asymptotics
from a Δ-analytic singular expansion via a little-o Darboux estimate.
-/
def DeltaDomainArg (R φ : ℝ) : Set ℂ :=
  { z | ‖z‖ < R ∧ z ≠ 1 ∧ φ < |Complex.arg (z - 1)| }

def DeltaDomainGeom (R φ : ℝ) : Set ℂ :=
  Metric.ball 0 R ∩ { z | (z - 1).re < Real.cos φ * ‖z - 1‖ }

lemma arg_away_iff_re_lt_cos_mul_norm {w : ℂ} (hw : w ≠ 0) {φ : ℝ}
    (hφ0 : 0 ≤ φ) (hφπ : φ < Real.pi) :
    φ < |Complex.arg w| ↔ w.re < Real.cos φ * ‖w‖ := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have harg_mem : |Complex.arg w| ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨abs_nonneg _, Complex.abs_arg_le_pi w⟩
  have hφ_mem : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ0, hφπ.le⟩
  rw [← Complex.norm_mul_cos_arg w, ← Real.cos_abs]
  rw [mul_comm (Real.cos φ) ‖w‖]
  constructor
  · intro h
    have hcos : Real.cos |Complex.arg w| < Real.cos φ :=
      (Real.strictAntiOn_cos.lt_iff_gt harg_mem hφ_mem).2 h
    exact mul_lt_mul_of_pos_left hcos hnorm
  · intro h
    have hcos : Real.cos |Complex.arg w| < Real.cos φ :=
      lt_of_mul_lt_mul_left h hnorm.le
    exact (Real.strictAntiOn_cos.lt_iff_gt harg_mem hφ_mem).1 hcos

lemma isOpen_deltaDomainGeom {R φ : ℝ} : IsOpen (DeltaDomainGeom R φ) := by
  unfold DeltaDomainGeom
  refine Metric.isOpen_ball.inter ?_
  exact isOpen_lt
    ((continuous_re).comp (continuous_id.sub continuous_const))
    (continuous_const.mul ((continuous_id.sub continuous_const).norm))

lemma delta_arg_eq_geom {R φ : ℝ} (hφ0 : 0 ≤ φ) (hφπ : φ < Real.pi) :
    DeltaDomainArg R φ = DeltaDomainGeom R φ := by
  ext z
  unfold DeltaDomainArg DeltaDomainGeom
  constructor
  · intro hz
    rcases hz with ⟨hR, hz_ne, harg⟩
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hR
    · have hw : z - 1 ≠ 0 := by
        simpa [sub_eq_zero] using hz_ne
      exact (arg_away_iff_re_lt_cos_mul_norm hw hφ0 hφπ).mp harg
  · intro hz
    rcases hz with ⟨hR, hgeom⟩
    have hz_ne : z ≠ 1 := by
      intro hz_eq
      subst z
      norm_num at hgeom
    refine ⟨?_, hz_ne, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hR
    · have hw : z - 1 ≠ 0 := by
        simpa [sub_eq_zero] using hz_ne
      exact (arg_away_iff_re_lt_cos_mul_norm hw hφ0 hφπ).mpr hgeom

lemma isOpen_deltaDomainArg {R φ : ℝ} (hφ0 : 0 ≤ φ) (hφπ : φ < Real.pi) :
    IsOpen (DeltaDomainArg R φ) := by
  rw [delta_arg_eq_geom hφ0 hφπ]
  exact isOpen_deltaDomainGeom

lemma zero_mem_deltaDomainArg {R φ : ℝ} (hR : 0 < R) (hφ : φ < Real.pi) :
    (0 : ℂ) ∈ DeltaDomainArg R φ := by
  unfold DeltaDomainArg
  constructor
  · simpa using hR
  constructor
  · norm_num
  · simpa [Complex.arg_neg_one, abs_of_pos Real.pi_pos] using hφ

lemma one_sub_mem_slitPlane_of_mem_delta {R φ : ℝ} {z : ℂ}
    (hφ0 : 0 < φ) (hz : z ∈ DeltaDomainArg R φ) :
    (1 - z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  have harg0 : Complex.arg (z - 1) = 0 := by
    rw [Complex.arg_eq_zero_iff]
    constructor
    · have hre := hnot.1
      simp at hre ⊢
      linarith
    · have him := hnot.2
      simp at him ⊢
      linarith
  have hlt : φ < 0 := by
    simpa [harg0] using hz.2.2
  linarith

lemma analyticOnNhd_one_sub_cpow_deltaDomain {α : ℂ} {R φ : ℝ}
    (hφ0 : 0 < φ) (_hφπ : φ < Real.pi) :
    AnalyticOnNhd ℂ (fun z : ℂ => (1 - z) ^ (-α)) (DeltaDomainArg R φ) := by
  exact (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
    (fun z hz => one_sub_mem_slitPlane_of_mem_delta hφ0 hz)
