import AnalyticCombinatorics.Ch8.SaddlePoint.GaussianCore
import Mathlib

/-!
# H-admissible saddle-point bridge

This file packages the abstract H-admissible hypotheses needed to feed the
central Gaussian core, the tail estimate, and the Cauchy assembly theorem.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Relative local error after removing the saddle phase and Gaussian. -/
def saddleLocalRatio (f : ℂ → ℂ) (a b : ℝ → ℝ) (r θ : ℝ) : ℂ :=
  (f ((r : ℂ) * Complex.exp (θ * Complex.I)) / f (r : ℂ) *
      Complex.exp (-(a r * θ : ℝ) * Complex.I)) /
    Complex.exp (-(b r * θ ^ 2 / 2 : ℝ))

/-- Abstract H-admissible saddle data for an analytic function. -/
structure HAdmissible (f : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ) where
  ρ : ℝ≥0∞
  radFilter : Filter ℝ
  a : ℝ → ℝ
  b : ℝ → ℝ
  δ : ℝ → ℝ

  hp : HasFPowerSeriesAt f p 0
  radius_eq : p.radius = ρ
  radius_pos : 0 < ρ
  rad_neBot : radFilter.NeBot

  r_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < r
  differentiableOn :
    ∀ᶠ (r : ℝ) in radFilter, DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)
  f_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < (f (r : ℂ)).re
  b_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < b r
  δ_pos : ∀ᶠ (r : ℝ) in radFilter, 0 < δ r
  δ_le_pi : ∀ᶠ (r : ℝ) in radFilter, δ r ≤ Real.pi

  δ_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => δ r * Real.sqrt (b r)) radFilter atTop

  local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in radFilter, ∀ θ : ℝ, |θ| ≤ δ r →
      ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε

  tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in radFilter, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * b r) * E r)
        radFilter (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        δ r ≤ |θ| → |θ| ≤ Real.pi → ‖saddleGAt f r n θ‖ ≤ E r)

/-- A sequence of saddle radii tracking the admissible radius filter. -/
structure SaddleSequence {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) where
  r : ℕ → ℝ
  tendsTo : Tendsto r atTop hf.radFilter
  saddle_eq : ∀ᶠ n in atTop, hf.a (r n) = (n : ℝ)

namespace HAdmissible

/-- Sequence version of the admissible quadratic scale. -/
abbrev B {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.b (hr.r n)

/-- Sequence version of the admissible central window. -/
abbrev Δ {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) : ℕ → ℝ :=
  fun n => hf.δ (hr.r n)

@[simp] theorem B_apply {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) (n : ℕ) :
    B hf hr n = hf.b (hr.r n) := rfl

@[simp] theorem Δ_apply {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) (n : ℕ) :
    Δ hf hr n = hf.δ (hr.r n) := rfl

end HAdmissible

lemma saddleGAt_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r x : ℝ) (n : ℕ)
    (hb : 0 < b r) (ha : a r = (n : ℝ)) :
    saddleGAt f r n (x / Real.sqrt (b r)) =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b r (x / Real.sqrt (b r)) := by
  let θ : ℝ := x / Real.sqrt (b r)
  have hsqrt_pos : 0 < Real.sqrt (b r) := Real.sqrt_pos.mpr hb
  have hsqrt_ne : Real.sqrt (b r) ≠ 0 := hsqrt_pos.ne'
  have hquad : b r * θ ^ 2 / 2 = x ^ 2 / 2 := by
    dsimp [θ]
    rw [div_pow]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hb.le]
    ring
  have hphaseR : (n : ℝ) * θ = a r * θ := by
    rw [ha]
  have hphaseC :
      Complex.exp (-(↑↑n * ↑θ) * I) =
        Complex.exp (-(a r * θ : ℝ) * I) := by
    congr 1
    have hmulC : (n : ℂ) * (θ : ℂ) = ((a r * θ : ℝ) : ℂ) := by
      exact_mod_cast hphaseR
    rw [hmulC]
  have hden :
      Complex.exp (-(b r * θ ^ 2 / 2 : ℝ)) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    exact_mod_cast (by linarith [hquad] :
      -(b r * θ ^ 2 / 2) = -(x ^ 2) / 2)
  have hgauss :
      Complex.exp (-(x ^ 2) / 2) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    norm_num
  dsimp [θ] at hphaseC hden ⊢
  rw [hgauss]
  unfold saddleGAt saddleLocalRatio
  rw [hphaseC, hden]
  field_simp [Complex.exp_ne_zero ((-(x ^ 2) / 2 : ℝ) : ℂ)]

lemma Hfun_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (R δ : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (hb : 0 < b (R n)) (ha : a (R n) = (n : ℝ))
    (hx : |x| ≤ δ n * Real.sqrt (b (R n))) :
    Hfun f R (fun n => b (R n)) δ n x =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) := by
  simpa [Hfun, saddleG, hx] using
    saddleGAt_eq_gaussian_mul_saddleLocalRatio f a b (R n) x n hb ha

lemma theta_mem_local_window_of_scaled_window
    (x δ B : ℝ) (hB : 0 < B)
    (hx : |x| ≤ δ * Real.sqrt B) :
    |x / Real.sqrt B| ≤ δ := by
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [abs_div, abs_of_pos hsqrt]
  exact (div_le_iff₀ hsqrt).mpr hx

lemma saddleLocalRatio_tendsto_one_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ) (x : ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
      atTop (𝓝 (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ ε / 2 :=
    hR.eventually (hlocal (ε / 2) hε2)
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  filter_upwards [hlocR, hBpos, hinside] with n hloc hBn hxn
  have htheta :
      |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
    theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hxn
  have hnorm :
      ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) - 1‖ ≤ ε / 2 :=
    hloc _ htheta
  have hdist :
      dist (saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) 1 ≤ ε / 2 := by
    simpa [dist_eq_norm] using hnorm
  exact lt_of_le_of_lt hdist (half_lt_self hε)

lemma Hfun_pointwise_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop)
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᵐ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x)
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
  refine ae_of_all _ fun x => ?_
  have hratio :=
    saddleLocalRatio_tendsto_one_of_localUniform
      f a b δr R x hR hlocal hBpos hL
  have hmul :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2) * 1)) :=
    tendsto_const_nhds.mul hratio
  have htarget :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa using hmul
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  have heq :
      (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x) =ᶠ[atTop]
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) := by
    filter_upwards [hBpos, hsaddle, hinside] with n hBn han hxn
    exact Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hxn
  exact Tendsto.congr' heq.symm htarget

lemma saddleGAt_continuous_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    Continuous fun θ : ℝ => saddleGAt f r n θ := by
  have hfcirc0 : Continuous fun θ : ℝ => f (circleMap (0 : ℂ) r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap (0 : ℂ) r)
      (fun θ => circleMap_mem_closedBall (0 : ℂ) hr θ)
  have hfcirc :
      Continuous fun θ : ℝ =>
        f ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
    simpa [circleMap_zero] using hfcirc0
  have hphase :
      Continuous fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * I) := by
    fun_prop
  simpa [saddleGAt, div_eq_mul_inv] using
    (hfcirc.mul continuous_const).mul hphase

lemma saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (a b : ℝ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    IntervalIntegrable (saddleGAt f r n) volume a b :=
  (saddleGAt_continuous_of_differentiableOn_closedBall f r n hr hf).intervalIntegrable a b

lemma Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (R B δ : ℕ → ℝ) (n : ℕ)
    (hr : 0 ≤ R n)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R n))) :
    AEStronglyMeasurable (Hfun f R B δ n) volume := by
  classical
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f R n (x / Real.sqrt (B n))
  have hgcont : Continuous g := by
    have h0 := saddleGAt_continuous_of_differentiableOn_closedBall f (R n) n hr hf
    have hdiv : Continuous fun x : ℝ => x / Real.sqrt (B n) := by
      fun_prop
    simpa [g, saddleG] using h0.comp hdiv
  have hsm : StronglyMeasurable (Set.indicator (Set.Icc (-L) L) g) :=
    hgcont.stronglyMeasurable.indicator measurableSet_Icc
  have heq :
      Hfun f R B δ n =
        Set.indicator (Set.Icc (-L) L) g := by
    funext x
    simp [Hfun, Set.indicator, abs_le, L, g]
  rw [heq]
  exact hsm.aestronglyMeasurable

lemma Hfun_aestronglyMeasurable_eventually_of_sequence
    {F : Filter ℝ} (f : ℂ → ℂ) (R B δ : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hrpos : ∀ᶠ r in F, 0 < r)
    (hdiff :
      ∀ᶠ r in F,
        DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    ∀ᶠ n in atTop,
      AEStronglyMeasurable (Hfun f R B δ n) volume := by
  filter_upwards [hR.eventually hrpos, hR.eventually hdiff] with n hrn hdiffn
  exact Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    f R B δ n hrn.le hdiffn

def centralD (x : ℝ) : ℝ := 2 * Real.exp (-(x ^ 2) / 2)

lemma centralD_integrable : Integrable centralD := by
  unfold centralD
  have hbase :
      Integrable
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq
      (by norm_num : 0 < (1 / 2 : ℝ))
  have hconst := hbase.const_mul 2
  convert hconst using 1
  funext x
  congr 1
  ring_nf

lemma saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one
    {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ)) : ‖z‖ ≤ 2 := by
  have hz_eq : z = (z - 1) + 1 := by ring
  calc
    ‖z‖ = ‖(z - 1) + 1‖ := by
      exact congrArg norm hz_eq
    _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add hz (by norm_num)
    _ = 2 := by norm_num

lemma Hfun_dominated_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
      ‖Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x‖
        ≤ centralD x := by
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ (1 : ℝ) :=
    hR.eventually (hlocal 1 (by norm_num))
  filter_upwards [hlocR, hBpos, hsaddle] with n hloc hBn han
  refine ae_of_all _ fun x => ?_
  by_cases hx : |x| ≤ δr (R n) * Real.sqrt (b (R n))
  · rw [Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hx]
    rw [norm_mul]
    have htheta :
        |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
      theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hx
    have hratio :
        ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖ ≤ 2 :=
      saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one (hloc _ htheta)
    have hnormexp :
        ‖Complex.exp (-(x ^ 2) / 2)‖ =
          Real.exp (-(x ^ 2) / 2) := by
      simp [Complex.norm_exp, sq]
    rw [hnormexp]
    calc
      Real.exp (-(x ^ 2) / 2) *
          ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖
          ≤ Real.exp (-(x ^ 2) / 2) * 2 :=
            mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
      _ = centralD x := by
            simp [centralD, mul_comm]
  · simp [Hfun, hx, centralD]
    positivity

theorem central_tendsto_one_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 1) := by
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hL :
      Tendsto
        (fun n : ℕ =>
          HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable
          (Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n) volume :=
    Hfun_aestronglyMeasurable_eventually_of_sequence
      f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
      hr.tendsTo hf.r_pos hf.differentiableOn
  have Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto
          (fun n : ℕ =>
            Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x)
          atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_pointwise_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        (by simpa [HAdmissible.B, HAdmissible.Δ] using hL)
        hr.saddle_eq
  have Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
        ‖Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x‖
          ≤ centralD x := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_dominated_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        hr.saddle_eq
  exact central_tendsto_one_of_dominated_of_aestronglyMeasurable
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hBpos hL Hmeas Hpoint centralD centralD_integrable Hdom

lemma saddleJtAt_norm_le_of_tail_bound
    (f : ℂ → ℂ) (r δ E : ℝ) (n : ℕ)
    (hδ_nonneg : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE_nonneg : 0 ≤ E)
    (htail : ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖saddleGAt f r n θ‖ ≤ E) :
    ‖saddleJtAt f r δ n‖ ≤
      (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
  have hleft :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * |(-δ) - (-Real.pi)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : -Real.pi < θ ∧ θ ≤ -δ := by
      simpa [Set.uIoc_of_le (by linarith : -Real.pi ≤ -δ)] using hθ
    have hθ_nonpos : θ ≤ 0 := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    exact htail θ hδθ hθπ
  have hright :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * |Real.pi - δ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : δ < θ ∧ θ ≤ Real.pi := by
      simpa [Set.uIoc_of_le hδπ] using hθ
    have hθ_nonneg : 0 ≤ θ := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonneg hθ_nonneg]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonneg hθ_nonneg]
      exact hθI.2
    exact htail θ hδθ hθπ
  have hlen_right : |Real.pi - δ| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr hδπ)]
    linarith [Real.pi_pos]
  have hlen_left : |(-δ) - (-Real.pi)| ≤ Real.pi := by
    rw [show (-δ) - (-Real.pi) = Real.pi - δ by ring]
    exact hlen_right
  have hleft_pi :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hleft.trans (mul_le_mul_of_nonneg_left hlen_left hE_nonneg)
  have hright_pi :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hright.trans (mul_le_mul_of_nonneg_left hlen_right hE_nonneg)
  unfold saddleJtAt
  calc
    ‖(2 * Real.pi : ℂ)⁻¹ *
        ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
          ∫ θ in δ..Real.pi, saddleGAt f r n θ)‖
        ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ *
          (‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ +
            ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ * (E * Real.pi + E * Real.pi) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hleft_pi hright_pi) (norm_nonneg _)
    _ = (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
          ring

lemma tail_tendsto_zero_of_tailUniform
    (f : ℂ → ℂ) (R B Δ E : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ Δ n)
    (hδπ : ∀ᶠ n in atTop, Δ n ≤ Real.pi)
    (hE_nonneg : ∀ᶠ n in atTop, 0 ≤ E n)
    (htail : ∀ᶠ n in atTop, ∀ θ : ℝ,
      Δ n ≤ |θ| → |θ| ≤ Real.pi → ‖saddleG f R n θ‖ ≤ E n)
    (hdecay : Tendsto
      (fun n : ℕ => Real.sqrt (2 * Real.pi * B n) * E n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n)
      atTop (𝓝 0) := by
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hdecayK :
      Tendsto (fun n : ℕ => K * (Real.sqrt (2 * Real.pi * B n) * E n))
        atTop (𝓝 0) := by
    simpa using hdecay.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖ ≤
          K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg, htail] with
      n hBn hδn hδπn hEn htailn
    have hJ : ‖saddleJt f R Δ n‖ ≤ K * E n := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (R n) (Δ n) (E n) n
          hδn hδπn hEn (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    calc
      ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖
          = Real.sqrt (2 * Real.pi * B n) * ‖saddleJt f R Δ n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (2 * Real.pi * B n) * (K * E n) :=
            mul_le_mul_of_nonneg_left hJ (Real.sqrt_nonneg _)
      _ = K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
            ring
  have hnorm :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖)
        atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hdecayK
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

theorem tail_tendsto_zero_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 0) := by
  rcases hf.tail_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ HAdmissible.Δ hf hr n := by
    filter_upwards [hr.tendsTo.eventually hf.δ_pos] with n hδn
    exact hδn.le
  have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
  have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
    simpa using hr.tendsTo.eventually hE_nonneg
  have htailSeq :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
    filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
    simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  exact tail_tendsto_zero_of_tailUniform
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) (fun n => E (hr.r n))
    hBpos hδ_nonneg hδπ hE_nonneg_seq htailSeq hdecaySeq

lemma f_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  simp [hzero] at hz

lemma saddleScale_nonzero_of_pos
    (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ)
    (hr : 0 < r n) (hf : 0 < (f (r n : ℂ)).re) (hB : 0 < B n) :
    saddleScale f r B n ≠ 0 := by
  have hfnz : f (r n : ℂ) ≠ 0 := f_ne_zero_of_re_pos hf
  have hrC : (r n : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hpow : (r n : ℂ) ^ n ≠ 0 := pow_ne_zero n hrC
  have hpref : saddlePref f r n ≠ 0 := by
    unfold saddlePref saddlePrefAt
    exact div_ne_zero hfnz hpow
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * B n) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hsqrtC : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_pos.ne'
  unfold saddleScale
  exact div_ne_zero hpref hsqrtC

theorem coeff_isEquivalent_saddle_of_hadmissible_limits
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJc f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) := by
  have hrpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hfnz : ∀ᶠ n in atTop, f (hr.r n : ℂ) ≠ 0 := by
    filter_upwards [hr.tendsTo.eventually hf.f_pos] with n hpos
    exact f_ne_zero_of_re_pos hpos
  have hleft :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-Real.pi) (-(HAdmissible.Δ hf hr n)) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-Real.pi) (-(HAdmissible.Δ hf hr n)) hrn.le hdn
  have hcenter :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) hrn.le hdn
  have hright :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (HAdmissible.Δ hf hr n) Real.pi := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (HAdmissible.Δ hf hr n) Real.pi hrn.le hdn
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz : ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  exact coeff_isEquivalent_saddle_assembly_of_cauchy
    hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hf.hp hrpos hdiff hfnz hleft hcenter hright Hcentral Htail Hnz

theorem coeff_isEquivalent_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) :=
  coeff_isEquivalent_saddle_of_hadmissible_limits hf hr
    (central_tendsto_one_of_hadmissible hf hr)
    (tail_tendsto_zero_of_hadmissible hf hr)
