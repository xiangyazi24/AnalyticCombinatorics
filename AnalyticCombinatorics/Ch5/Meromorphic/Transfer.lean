import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.CauchyCoeff
import AnalyticCombinatorics.Ch4.Analytic.Rational

open Filter Asymptotics
open scoped BigOperators ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic

private lemma closedBall_subset_eball_of_ofReal_lt_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hRrad : ENNReal.ofReal R < p.radius) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.eball (0 : ℂ) p.radius := by
  intro z hz
  have hdist : dist z (0 : ℂ) ≤ R := by
    simpa [Metric.mem_closedBall] using hz
  have hed : edist z (0 : ℂ) ≤ ENNReal.ofReal R := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist
  exact hed.trans_lt hRrad

private lemma sphere_subset_eball_of_ofReal_lt_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hRrad : ENNReal.ofReal R < p.radius) :
    Metric.sphere (0 : ℂ) R ⊆ Metric.eball (0 : ℂ) p.radius := by
  intro z hz
  exact closedBall_subset_eball_of_ofReal_lt_radius (p := p) hRrad
    (Metric.sphere_subset_closedBall hz)

private lemma exists_norm_bound_on_sphere
    {g : ℂ → ℂ} {R : ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
  have hnorm : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.sphere (0 : ℂ) R) :=
    continuous_norm.comp_continuousOn hg
  have hbdd :
      BddAbove ((fun z : ℂ => ‖g z‖) '' Metric.sphere (0 : ℂ) R) :=
    (isCompact_sphere (0 : ℂ) R).bddAbove_image hnorm
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hM (Set.mem_image_of_mem (fun z : ℂ => ‖g z‖) hz)).trans (le_max_left _ _)

/-- Cauchy's coefficient estimate on a circle gives geometric decay for the coefficients of an
analytic remainder on the closed disk. -/
theorem coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn
    {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt g p 0)
    (hd : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) R)) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hcont_closed : ContinuousOn g (Metric.closedBall (0 : ℂ) R) :=
    hd.continuousOn
  have hcont_sphere : ContinuousOn g (Metric.sphere (0 : ℂ) R) :=
    hcont_closed.mono Metric.sphere_subset_closedBall
  rcases exists_norm_bound_on_sphere (g := g) (R := R) hcont_sphere with
    ⟨M, hM_nonneg, hM⟩
  have hcoeff : ∀ n : ℕ, ‖p.coeff n‖ ≤ M * R⁻¹ ^ n := by
    intro n
    exact norm_coeff_le_of_circleIntegral hR hp hd hM n
  refine isBigO_of_le' (l := atTop) (c := M) ?_
  intro n
  have hpow_nonneg : 0 ≤ R⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hR.le) n
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (p.coeff n)),
    abs_of_nonneg hpow_nonneg, abs_of_nonneg hR.le] using hcoeff n

/-- Radius form of the analytic-remainder estimate for a formal power series. -/
theorem coeff_norm_isBigO_of_radius
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < p.radius) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hpos : 0 < p.radius :=
    (ENNReal.ofReal_pos.mpr hR).trans hRrad
  have hpball : HasFPowerSeriesOnBall p.sum p (0 : ℂ) p.radius :=
    FormalMultilinearSeries.hasFPowerSeriesOnBall p hpos
  have hd_eball : DifferentiableOn ℂ p.sum (Metric.eball (0 : ℂ) p.radius) :=
    hpball.differentiableOn
  have hd_closed : DifferentiableOn ℂ p.sum (Metric.closedBall (0 : ℂ) R) :=
    hd_eball.mono (closedBall_subset_eball_of_ofReal_lt_radius (p := p) hRrad)
  exact coeff_norm_isBigO_of_hasFPowerSeriesAt_differentiableOn hR
    hpball.hasFPowerSeriesAt hd_closed

/-- Radius form specialized to the project's `PowerSeries.toFMLS` bridge. -/
theorem powerSeries_coeff_norm_isBigO_of_radius
    (g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hRrad : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius) :
    (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
      (fun n : ℕ => R⁻¹ ^ n) := by
  simpa using coeff_norm_isBigO_of_radius
    (p := PowerSeries.toFMLS g) hR hRrad

/-- If a power series is a finite simple-pole sum plus a remainder analytic past `R`, then the
coefficient error after subtracting the principal part is geometrically small. -/
theorem coeff_sub_principalPart_isBigO_of_remainder_radius
    (f S g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg : f = S + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
      PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  have hgO :
      (fun n : ℕ => ‖PowerSeries.coeff (R := ℂ) n g‖) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    powerSeries_coeff_norm_isBigO_of_radius g hR hgR
  have hgO_complex :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) =O[atTop]
        (fun n : ℕ => R⁻¹ ^ n) :=
    IsBigO.of_norm_left hgO
  have hcoeff :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =ᶠ[atTop]
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n g) := by
    exact Eventually.of_forall fun n => by
      rw [hfg]
      simp
  exact hcoeff.trans_isBigO hgO_complex

/-- Meromorphic transfer for a finite sum of simple-pole principal parts. -/
theorem meromorphic_coeff_transfer_simplePoleSum
    {ι : Type*} (s : Finset ι) (c a : ι → ℂ)
    (f g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      f =
        (∑ i ∈ s, PowerSeries.C (c i) *
          PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
      ∑ i ∈ s, c i * (a i) ^ n) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by
  let S : PowerSeries ℂ :=
    ∑ i ∈ s, PowerSeries.C (c i) *
      PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))
  have htransfer :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR hfg
  simpa [S, PowerSeries.coeff_simplePoleSum] using htransfer

private lemma inv_lt_inv_of_pos_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    y⁻¹ < x⁻¹ := by
  simpa [one_div] using one_div_lt_one_div_of_lt hx hxy

private lemma inv_radius_pow_isLittleO_simplePole
    {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0) :
    (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  have hR : 0 < R := hρ.trans hρR
  have hinv_lt : R⁻¹ < ‖ρ‖⁻¹ :=
    inv_lt_inv_of_pos_lt hρ hρR
  have hpowLittle :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) :=
    isLittleO_pow_pow_of_lt_left (inv_nonneg.mpr hR.le) hinv_lt
  have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hρnorm : ‖ρ‖ ≠ 0 := ne_of_gt hρ
  have hpowOmain :
      (fun n : ℕ => ‖ρ‖⁻¹ ^ n : ℕ → ℝ) =O[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    refine isBigO_of_le' (l := atTop) (c := (‖c‖ * ‖ρ‖⁻¹)⁻¹) ?_
    intro n
    have hbase_nonneg : 0 ≤ ‖ρ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ρ)
    have hpow_nonneg : 0 ≤ ‖ρ‖⁻¹ ^ n := pow_nonneg hbase_nonneg n
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    apply le_of_eq
    calc
      ‖ρ‖⁻¹ ^ n =
          (‖c‖ * ‖ρ‖⁻¹)⁻¹ * (‖c‖ * (‖ρ‖⁻¹ ^ (n + 1))) := by
        rw [pow_succ]
        field_simp [hcnorm, hρnorm]
      _ = (‖c‖ * ‖ρ‖⁻¹)⁻¹ * ‖c * ρ⁻¹ ^ (n + 1)‖ := by
        rw [norm_mul, norm_pow, norm_inv]
  exact hpowLittle.trans_isBigO hpowOmain

/-- The single-pole principal part with pole at `ρ` has coefficients
`c * (ρ⁻¹)^(n+1)`, matching the normalization of
`PowerSeries.coeff_simplePoleSum`. -/
theorem single_simplePole_principal_isEquivalent
    {ρ c : ℂ} :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C (c * ρ⁻¹) *
        PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)))) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  apply Filter.EventuallyEq.isEquivalent
  exact Eventually.of_forall fun n => by
    calc
      PowerSeries.coeff (R := ℂ) n
          (PowerSeries.C (c * ρ⁻¹) *
            PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))) =
          (c * ρ⁻¹) * ρ⁻¹ ^ n := by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale_invUnitsSub_one]
      _ = c * ρ⁻¹ ^ (n + 1) := by
        rw [pow_succ]
        ring

/-- Dominant simple pole transfer: a single simple pole at `ρ` plus a remainder analytic past `R`
has coefficients asymptotic to the pole contribution. -/
theorem dominant_simplePole_isEquivalent
    (f g : PowerSeries ℂ) {ρ c : ℂ} {R : ℝ}
    (hρ : 0 < ‖ρ‖) (hρR : ‖ρ‖ < R) (hc : c ≠ 0)
    (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      f =
        PowerSeries.C (c * ρ⁻¹) *
          PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ)) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f) ~[atTop]
      (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
  let S : PowerSeries ℂ :=
    PowerSeries.C (c * ρ⁻¹) *
      PowerSeries.rescale ρ⁻¹ (PowerSeries.invUnitsSub (1 : ℂˣ))
  have hR : 0 < R := hρ.trans hρR
  have hremO :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) :=
    coeff_sub_principalPart_isBigO_of_remainder_radius f S g hR hgR hfg
  have hgeom :
      (fun n : ℕ => R⁻¹ ^ n : ℕ → ℝ) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    inv_radius_pow_isLittleO_simplePole hρ hρR hc
  have hremLittle :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
        PowerSeries.coeff (R := ℂ) n S) =o[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hremO.trans_isLittleO hgeom
  have hS :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) := by
    simpa [S] using single_simplePole_principal_isEquivalent
      (ρ := ρ) (c := c)
  have hsum :
      (fun n : ℕ => PowerSeries.coeff (R := ℂ) n S +
        (PowerSeries.coeff (R := ℂ) n f - PowerSeries.coeff (R := ℂ) n S)) ~[atTop]
        (fun n : ℕ => c * ρ⁻¹ ^ (n + 1)) :=
    hS.add_isLittleO hremLittle
  exact hsum.congr_left (Eventually.of_forall fun n => by ring)

end Meromorphic
end Ch5
end AnalyticCombinatorics
