import AnalyticCombinatorics.Ch8.SaddlePoint.ThirdOrderCore
import AnalyticCombinatorics.Ch8.SaddlePoint.SecondOrderHAdmissible
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Third-order H-admissible wrapper

This is a clean add-on to the second-order `HAdmissible` interface.  It records
the fifth and sixth logarithmic saddle derivatives, the robust third-order
scale, and the local/tail hypotheses used by the third-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Third-order Hayman data over an existing second-order H-admissible instance. -/
structure ThirdOrderHAdmissible {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HAdmissible f p)
    (h2 : SecondOrderHAdmissible hf) where
  b5 : ℝ → ℝ
  b6 : ℝ → ℝ
  corrScale3 : ℝ → ℝ

  corrScale3_pos : ∀ᶠ r : ℝ in hf.radFilter, 0 < corrScale3 r
  corrScale3_tendsto_zero : Tendsto corrScale3 hf.radFilter (𝓝 0)
  corrScale3_dominates_correction :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in hf.radFilter,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 b5 b6 r ≤ K * corrScale3 r

  local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(hf.δ r * Real.sqrt (hf.b r))..(hf.δ r * Real.sqrt (hf.b r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio f hf.a hf.b r (x / Real.sqrt (hf.b r)) -
              saddleThirdPoly hf.b h2.b3 h2.b4 b5 b6 r x)‖) / corrScale3 r)
      hf.radFilter (𝓝 0)

  tail_third_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in hf.radFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * hf.b r) * E r / corrScale3 r)
        hf.radFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in hf.radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        hf.δ r ≤ |θ| → |θ| ≤ Real.pi → ‖saddleGAt f r n θ‖ ≤ E r)

private lemma complex_isLittleO_of_norm_div_tendsto_zero
    (u : ℕ → ℂ) (c : ℕ → ℝ)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (h : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0)) :
    u =o[atTop] (fun n : ℕ => (c n : ℂ)) := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ h
    filter_upwards [hcpos] with n hcn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  · filter_upwards [hcpos] with n hcn hzero
    exact (hcn.ne' (Complex.ofReal_eq_zero.mp hzero)).elim

private lemma third_tail_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
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
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hdecaySeq.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n) ≤
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n)) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg_seq, htailSeq, hCpos] with
      n hBn hδn hδπn hEn htailn hCn
    have hJ : ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤ K * E (hr.r n) := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (hr.r n) (HAdmissible.Δ hf hr n)
          (E (hr.r n)) n hδn hδπn hEn
          (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) :=
      Real.sqrt_nonneg _
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * (K * E (hr.r n)) := by
      calc
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖
            =
              Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hsqrt_nonneg]
        _ ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) :=
              mul_le_mul_of_nonneg_left hJ hsqrt_nonneg
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ / h3.corrScale3 (hr.r n)
          ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) / h3.corrScale3 (hr.r n) := hdiv
      _ = K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤ ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma coeff_ratio_eq_scaled_saddleJ_eventually
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n)
      =ᶠ[atTop]
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)) := by
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
  have Hsplit :
      ∀ᶠ n in atTop,
        p.coeff n =
          saddlePref f hr.r n *
            (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
              saddleJt f hr.r (HAdmissible.Δ hf hr) n) :=
    eventually_coeff_eq_saddle_split
      hr.r (HAdmissible.Δ hf hr) hf.hp hrpos hdiff hfnz hleft hcenter hright
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz :
      ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  filter_upwards [Hsplit, Hnz] with n hsplit hnz
  rw [hsplit]
  dsimp [saddleScale]
  have hS : (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) ≠ 0 := by
    intro hzero
    apply hnz
    simp [hzero, saddleScale]
  have hpref : saddlePref f hr.r n ≠ 0 := by
    intro hpref_zero
    apply hnz
    simp [hpref_zero, saddleScale]
  field_simp [hpref, hS]

private lemma third_central_local_error_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n -
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hRpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hlocalSeq :
      Tendsto
        (fun n : ℕ =>
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) -
                saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
            h3.corrScale3 (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using h3.local_third_L1.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
              h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hlocalSeq.const_mul ‖invG‖
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG *
              ∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2) *
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
            h3.corrScale3 (hr.r n) ≤
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
              h3.corrScale3 (hr.r n)) := by
    filter_upwards [hBpos, hRpos, hδpos, hdiff, hsaddle, hCpos] with
      n hBn hRn hδn hdiffn han hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    let G : ℝ → ℂ := fun x => saddleG f hr.r n (x / Real.sqrt (HAdmissible.B hf hr n))
    let P : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x
    let Err : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio f hf.a hf.b (hr.r n)
          (x / Real.sqrt (HAdmissible.B hf hr n)) -
          saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)
    have hscaled :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n =
          invG * ∫ x in -L..L, G x := by
      simpa [L, G, invG] using
        saddleJc_eq_integral_scaled f hr.r (HAdmissible.Δ hf hr)
          (HAdmissible.B hf hr) n hBn
    have hGcont : Continuous G := by
      have h0 := saddleGAt_continuous_of_differentiableOn_closedBall
        f (hr.r n) n hRn.le hdiffn
      have hdiv : Continuous fun x : ℝ => x / Real.sqrt (HAdmissible.B hf hr n) := by
        fun_prop
      simpa [G, saddleG] using h0.comp hdiv
    have hGint : IntervalIntegrable G volume (-L) L :=
      hGcont.intervalIntegrable _ _
    have hPcont : Continuous P := by
      unfold P saddleThirdPoly saddleSecondPoly
      fun_prop
    have hPint : IntervalIntegrable P volume (-L) L :=
      hPcont.intervalIntegrable _ _
    have hsub :
        (∫ x in -L..L, G x) - (∫ x in -L..L, P x) =
          ∫ x in -L..L, G x - P x := by
      rw [intervalIntegral.integral_sub hGint hPint]
    have hErr :
        (fun x : ℝ => G x - P x) = fun x : ℝ => Err x := by
      funext x
      have hGx :
          G x =
            Complex.exp (-(x ^ 2) / 2) *
              saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) := by
        simpa [G, saddleG, HAdmissible.B] using
          saddleGAt_eq_gaussian_mul_saddleLocalRatio
            f hf.a hf.b (hr.r n) x n hBn han
      rw [hGx]
      simp [P, Err]
      ring
    have hdiff_eq :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x) =
          invG * ∫ x in -L..L, Err x := by
      rw [hscaled]
      rw [← mul_sub]
      rw [hsub]
      rw [hErr]
    have hLnonneg : 0 ≤ L := by
      exact mul_nonneg hδn.le (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hnormInt :
        ‖∫ x in -L..L, Err x‖ ≤
          ∫ x in -L..L, ‖Err x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hle
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x)‖ ≤
          ‖invG‖ * (∫ x in -L..L, ‖Err x‖) := by
      rw [hdiff_eq]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hnormInt (norm_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n -
          invG * (∫ x in -L..L, P x)‖ / h3.corrScale3 (hr.r n)
          ≤ ‖invG‖ * (∫ x in -L..L, ‖Err x‖) / h3.corrScale3 (hr.r n) := hdiv
      _ = ‖invG‖ *
            ((∫ x in -L..L, ‖Err x‖) / h3.corrScale3 (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
              h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
              h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma gaussian_boundary_exp_div_corr_tendsto_zero
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
          h3.corrScale3 (hr.r n))
      atTop (𝓝 0) := by
  rcases h3.tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
  have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
  have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
    simpa using hr.tendsTo.eventually hE_nonneg
  have htailSeq :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
    filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
    simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
  have hlocal :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ HAdmissible.Δ hf hr n →
          ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
    simpa [HAdmissible.Δ] using
      hr.tendsTo.eventually (hf.local_uniform (1 / 2) (by norm_num))
  have hLtop :
      Tendsto
        (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hsqrtFactor_ge_one :
      ∀ᶠ n in atTop, 1 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) := by
    have hLπ : ∀ᶠ n in atTop,
        Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
      hLtop.eventually_ge_atTop Real.pi
    filter_upwards [hLπ, hδπ, hBpos] with n hLn hδπn hBn
    have hsqrtB_nonneg : 0 ≤ Real.sqrt (HAdmissible.B hf hr n) := Real.sqrt_nonneg _
    have hπsqrt :
        Real.pi * Real.sqrt (HAdmissible.B hf hr n) ≥ Real.pi := by
      calc
        Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) := hLn
        _ ≤ Real.pi * Real.sqrt (HAdmissible.B hf hr n) :=
              mul_le_mul_of_nonneg_right hδπn hsqrtB_nonneg
    have hsqrtB_ge_one : 1 ≤ Real.sqrt (HAdmissible.B hf hr n) := by
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      exact (le_mul_iff_one_le_right hpi_pos).mp (by simpa [ge_iff_le] using hπsqrt)
    have hB_ge_one : 1 ≤ HAdmissible.B hf hr n := by
      have hs := Real.sq_sqrt hBn.le
      nlinarith [sq_nonneg (Real.sqrt (HAdmissible.B hf hr n)), hsqrtB_ge_one, hs]
    have harg : 1 ≤ 2 * Real.pi * HAdmissible.B hf hr n := by
      nlinarith [Real.pi_gt_three, hB_ge_one]
    simpa using (Real.one_le_sqrt.mpr harg)
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
            h3.corrScale3 (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
            h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hdecaySeq.const_mul 2
  have hbound :
      ∀ᶠ n in atTop,
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
            h3.corrScale3 (hr.r n) ≤
          2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
            h3.corrScale3 (hr.r n)) := by
    filter_upwards [hBpos, hδpos, hδπ, hsaddle, hCpos, hE_nonneg_seq, htailSeq,
      hlocal, hsqrtFactor_ge_one] with
      n hBn hδn hδπn han hCn hEn htailn hlocaln hsqrt_ge_one
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    let θ : ℝ := HAdmissible.Δ hf hr n
    have hsqrt_pos : 0 < Real.sqrt (HAdmissible.B hf hr n) :=
      Real.sqrt_pos.mpr hBn
    have hθeq : L / Real.sqrt (HAdmissible.B hf hr n) = θ := by
      simp [L, θ, div_eq_mul_inv, hsqrt_pos.ne']
    have htheta_abs : |θ| = θ := abs_of_pos hδn
    have hratio_close :
        ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
      exact hlocaln θ (by simp [htheta_abs, θ])
    have hratio_lower :
        (1 / 2 : ℝ) ≤
          ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
      have hone :
          ‖(1 : ℂ)‖ ≤
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
              ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
        calc
          ‖(1 : ℂ)‖ =
              ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1) +
                saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by ring_nf
          _ ≤ ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1)‖ +
                ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                norm_add_le _ _
          _ = ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
                ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by rw [norm_neg]
      norm_num at hone
      linarith
    have hG :
        saddleG f hr.r n θ =
          Complex.exp (-(L ^ 2) / 2) *
            saddleLocalRatio f hf.a hf.b (hr.r n) θ := by
      rw [← hθeq]
      simpa [L, saddleG, HAdmissible.B] using
        saddleGAt_eq_gaussian_mul_saddleLocalRatio
          f hf.a hf.b (hr.r n) L n hBn han
    have hGnorm :
        ‖saddleG f hr.r n θ‖ =
          Real.exp (-(L ^ 2) / 2) *
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
      rw [hG, norm_mul]
      have hnormexp :
          ‖Complex.exp (-(L ^ 2) / 2)‖ = Real.exp (-(L ^ 2) / 2) := by
        simp [Complex.norm_exp, sq]
      rw [hnormexp]
    have htail_at : ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
      exact htailn θ (by simp [θ, htheta_abs]) (by simpa [θ, htheta_abs] using hδπn)
    have hexp_nonneg : 0 ≤ Real.exp (-(L ^ 2) / 2) := (Real.exp_pos _).le
    have hexp_le : Real.exp (-(L ^ 2) / 2) ≤ 2 * E (hr.r n) := by
      have hhalf :
          Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ) ≤ E (hr.r n) := by
        calc
          Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ)
              ≤ Real.exp (-(L ^ 2) / 2) *
                  ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                    mul_le_mul_of_nonneg_left hratio_lower hexp_nonneg
          _ = ‖saddleG f hr.r n θ‖ := by rw [hGnorm]
          _ ≤ E (hr.r n) := htail_at
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hexp_le hCn.le
    calc
      Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
          h3.corrScale3 (hr.r n)
          = Real.exp (-(L ^ 2) / 2) / h3.corrScale3 (hr.r n) := by simp [L]
      _ ≤ 2 * E (hr.r n) / h3.corrScale3 (hr.r n) := hdiv
      _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
            h3.corrScale3 (hr.r n)) := by
          have hEdiv_nonneg : 0 ≤ E (hr.r n) / h3.corrScale3 (hr.r n) :=
            div_nonneg hEn hCn.le
          have hmul :
              E (hr.r n) / h3.corrScale3 (hr.r n) ≤
                Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                  (E (hr.r n) / h3.corrScale3 (hr.r n)) := by
            simpa using
              mul_le_mul_of_nonneg_right hsqrt_ge_one hEdiv_nonneg
          calc
            2 * E (hr.r n) / h3.corrScale3 (hr.r n)
                = 2 * (E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
            _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                  (E (hr.r n) / h3.corrScale3 (hr.r n))) := by nlinarith
            _ = 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                  E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
            h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (Real.exp_pos _).le (le_of_lt hCn)
  exact squeeze_zero' hnonneg hbound hupper

private lemma third_window_zero_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2)) -
        1)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hLtop :
      Tendsto
        (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hLone :
      ∀ᶠ n in atTop,
        1 ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
    hLtop.eventually_ge_atTop 1
  have hboundary := gaussian_boundary_exp_div_corr_tendsto_zero hf h2 h3 hr
  have hupper :
      Tendsto
        (fun n : ℕ =>
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hboundary.const_mul (2 / Real.sqrt (2 * Real.pi))
  have hbound :
      ∀ᶠ n in atTop,
        ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2)) -
            1‖ / h3.corrScale3 (hr.r n) ≤
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)) := by
    filter_upwards [hLone, hCpos] with n hLn hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    have hineq := gaussian_window_zero_error_norm_le_exp (L := L) hLn
    have hdiv := div_le_div_of_nonneg_right hineq hCn.le
    calc
      ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖ /
          h3.corrScale3 (hr.r n)
          ≤ ((2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2)) /
              h3.corrScale3 (hr.r n) := hdiv
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(L ^ 2) / 2) / h3.corrScale3 (hr.r n)) := by ring
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)) := by simp [L]
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma third_window_quartic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((h2.b4 (hr.r n) : ℂ) /
            (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M4 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let D : ℕ → ℂ := fun n =>
    (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM4_tendsto : Tendsto M4 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_four_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
      tendsto_const_nhds
    simpa [M4] using hwin.sub hconst
  have hM4_little : M4 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM4_tendsto
  have hD_bigO : D =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 24 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hDle :
        ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [D, HAdmissible.B] using
        saddleThirdPoly_quarticCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hDle
      _ ≤ (1 / 24 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 24 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hD_bigO.mul_isLittleO hM4_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [D, M4, L, mul_assoc] using hscaled

private lemma third_window_sextic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
            (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M6 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let E : ℕ → ℂ := fun n =>
    (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
      (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM6_tendsto : Tendsto M6 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_six_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
      tendsto_const_nhds
    simpa [M6] using hwin.sub hconst
  have hM6_little : M6 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM6_tendsto
  have hE_bigO : E =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 72 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hEle :
        ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [E, HAdmissible.B] using
        saddleThirdPoly_sexticB3Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hEle
      _ ≤ (1 / 72 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 72 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hE_bigO.mul_isLittleO hM6_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [E, M6, L, mul_assoc] using hscaled

private lemma third_window_coeff_moment_isLittleO
    (C M scale : ℕ → ℂ)
    (hC : C =O[atTop] scale)
    (hM : Tendsto M atTop (𝓝 0)) :
    (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) * (C n * M n))
      =o[atTop] scale := by
  have hM_little : M =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM
  have hprod := hC.mul_isLittleO hM_little
  simpa [mul_assoc] using
    hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)

private lemma third_window_b6_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((h3.b6 (hr.r n) : ℂ) /
            (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M6 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let C6 : ℕ → ℂ := fun n =>
    (h3.b6 (hr.r n) : ℂ) / (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM6_tendsto : Tendsto M6 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_six_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
      tendsto_const_nhds
    simpa [M6] using hwin.sub hconst
  have hC_bigO : C6 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 720 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C6 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C6, HAdmissible.B] using
        saddleThirdPoly_b6Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C6 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 720 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 720 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C6 M6
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM6_tendsto

private lemma third_window_b3b5_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ((((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
            (720 * (HAdmissible.B hf hr n : ℂ) ^ 4)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M8 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let C8 : ℕ → ℂ := fun n =>
    (((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
      (720 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM8_tendsto : Tendsto M8 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_eight_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
      tendsto_const_nhds
    simpa [M8] using hwin.sub hconst
  have hC_bigO : C8 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 720 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C8 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C8, HAdmissible.B] using
        saddleThirdPoly_b3b5Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C8 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 720 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 720 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C8 M8
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM8_tendsto

private lemma third_window_b4sq_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
            (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M8 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let C8 : ℕ → ℂ := fun n =>
    ((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
      (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM8_tendsto : Tendsto M8 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_eight_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
      tendsto_const_nhds
    simpa [M8] using hwin.sub hconst
  have hC_bigO : C8 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 1152 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C8 n‖ ≤ (1 / 1152 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C8, HAdmissible.B] using
        saddleThirdPoly_b4sqCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C8 n‖ ≤ (1 / 1152 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 1152 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 1152 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C8 M8
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM8_tendsto

private lemma third_window_b3sqb4_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
            (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M10 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  let C10 : ℕ → ℂ := fun n =>
    ((((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
      (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM10_tendsto : Tendsto M10 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_ten_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) :=
      tendsto_const_nhds
    simpa [M10] using hwin.sub hconst
  have hC_bigO : C10 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 1728 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C10 n‖ ≤ (1 / 1728 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C10, HAdmissible.B] using
        saddleThirdPoly_b3sqb4Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C10 n‖ ≤ (1 / 1728 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 1728 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 1728 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C10 M10
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM10_tendsto

private lemma third_window_b3four_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
            (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M12 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  let C12 : ℕ → ℂ := fun n =>
    ((((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
      (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM12_tendsto : Tendsto M12 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_twelve_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) :=
      tendsto_const_nhds
    simpa [M12] using hwin.sub hconst
  have hC_bigO : C12 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 31104 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C12 n‖ ≤ (1 / 31104 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C12, HAdmissible.B] using
        saddleThirdPoly_b3fourCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C12 n‖ ≤ (1 / 31104 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 31104 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 31104 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C12 M12
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM12_tendsto

private lemma third_window_poly_integral_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
          (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  have h0 := third_window_zero_isLittleO hf h2 h3 hr
  have h4 := third_window_quartic_isLittleO hf h2 h3 hr
  have h6 := third_window_sextic_isLittleO hf h2 h3 hr
  have h6b := third_window_b6_isLittleO hf h2 h3 hr
  have h8a := third_window_b3b5_isLittleO hf h2 h3 hr
  have h8b := third_window_b4sq_isLittleO hf h2 h3 hr
  have h10 := third_window_b3sqb4_isLittleO hf h2 h3 hr
  have h12 := third_window_b3four_isLittleO hf h2 h3 hr
  have hsum := (((h0.add ((h4.sub h6).sub h6b)).add h8a).add h8b).sub h10 |>.add h12
  refine hsum.congr_left ?_
  intro n
  let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  let W0 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)
  let W4 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let W6 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let W8 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8
  let W10 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10
  let W12 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12
  let F4 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let F6 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let F8 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8
  let F10 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10
  let F12 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12
  let D : ℂ := (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  let E : ℂ := (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
    (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  let C6 : ℂ := (h3.b6 (hr.r n) : ℂ) / (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  let C8a : ℂ := (((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
    (720 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  let C8b : ℂ := ((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
    (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  let C10 : ℂ := (((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
    (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5)
  let C12 : ℂ := (((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
    (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6)
  have hwin :
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
          saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) =
        W0 + D * W4 - E * W6 - C6 * W6 + C8a * W8 + C8b * W8 -
          C10 * W10 + C12 * W12 := by
    simpa [L, W0, W4, W6, W8, W10, W12, D, E, C6, C8a, C8b, C10, C12,
      HAdmissible.B] using
      gaussian_window_integral_saddleThirdPoly
        hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) L
  have hcorr1 :
      (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) =
        invG * (D * F4 - E * F6) := by
    simpa [invG, D, E, F4, F6, HAdmissible.B] using
      saddleCorrection_eq_gaussian_even_moments
        hf.b h2.b3 h2.b4 (hr.r n)
  have hcorr2 :
      (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ) =
        invG * (-C6 * F6 + C8a * F8 + C8b * F8 - C10 * F10 + C12 * F12) := by
    simpa [invG, C6, C8a, C8b, C10, C12, F6, F8, F10, F12, HAdmissible.B] using
      saddleThirdCorrection_eq_gaussian_even_moments
        hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n)
  calc
    (((((invG * W0 - 1) +
          ((invG * (D * (W4 - F4)) - invG * (E * (W6 - F6))) -
            invG * (C6 * (W6 - F6)))) +
          invG * (C8a * (W8 - F8))) +
          invG * (C8b * (W8 - F8))) -
          invG * (C10 * (W10 - F10))) +
          invG * (C12 * (W12 - F12))
        = invG * (W0 + D * W4 - E * W6 - C6 * W6 + C8a * W8 + C8b * W8 -
            C10 * W10 + C12 * W12) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          rw [hcorr1, hcorr2]
          ring
    _ = invG *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
            saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
            (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          rw [hwin]
    _ =
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) *
                saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
            (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          simp [L, invG]

/-- Abstract third-order saddle ratio theorem. -/
theorem coeff_thirdOrder_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
          (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) :=
  by
    have hcentral := third_central_local_error_isLittleO hf h2 h3 hr
    have hpoly := third_window_poly_integral_isLittleO hf h2 h3 hr
    have htail := third_tail_isLittleO hf h2 h3 hr
    have hcentralCorr :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
      have h := hcentral.add hpoly
      refine h.congr_left ?_
      intro n
      ring
    have hscaled :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
      have h := hcentralCorr.add htail
      refine h.congr_left ?_
      intro n
      ring
    have hratio := coeff_ratio_eq_scaled_saddleJ_eventually hf hr
    have htarget :
        (fun n : ℕ =>
          p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ))) := by
      filter_upwards [hratio] with n hn
      rw [hn]
    exact htarget.trans_isLittleO hscaled
