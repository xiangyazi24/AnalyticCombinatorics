import AnalyticCombinatorics.Ch4.Analytic.PringsheimCore

open Filter
open scoped NNReal ENNReal Topology

noncomputable section

private abbrev pringsheimSeries (a : ℕ → ℝ≥0) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))

private lemma nnreal_quarter_pos {x : ℝ≥0} (hx : 0 < x) :
    0 < x / 4 := by
  positivity

private lemma nnreal_two_mul_quarter_lt {x : ℝ≥0} (hx : 0 < x) :
    x / 4 + x / 4 < x := by
  rw [← NNReal.coe_lt_coe]
  simp
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  nlinarith

private lemma nnreal_quarter_lt {x : ℝ≥0} (hx : 0 < x) :
    x / 4 < x := by
  have h := nnreal_two_mul_quarter_lt (x := x) hx
  exact lt_of_le_of_lt (by simp) h

private lemma sub_lt_self_nnreal {R ε : ℝ≥0} (hR : 0 < R) (hε : 0 < ε) :
    R - ε < R := by
  rw [← NNReal.coe_lt_coe]
  by_cases hεR : ε ≤ R
  · rw [NNReal.coe_sub hεR]
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    linarith
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have hsub : R - ε = 0 := tsub_eq_zero_of_le (le_of_not_ge hεR)
    simp [hsub, hR']

private lemma add_sub_cancel_nnreal {R ε : ℝ≥0} (hεR : ε ≤ R) :
    ε + (R - ε) = R := by
  rw [← NNReal.coe_inj]
  rw [NNReal.coe_add, NNReal.coe_sub hεR]
  linarith

private lemma radius_pos_of_radius_eq
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞)) :
    0 < (pringsheimSeries a).radius := by
  rw [hR]
  exact ENNReal.coe_pos.2 hRpos

private lemma shifted_radius_gt
    (a : ℕ → ℝ≥0) {R ε : ℝ≥0} {g : ℂ → ℂ}
    {q : FormalMultilinearSeries ℂ ℂ ℂ} {δ : ℝ≥0∞}
    (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞))
    (hεpos : 0 < ε) (hεR : ε < R)
    (hg : HasFPowerSeriesOnBall g q (((R : ℝ) : ℂ)) δ)
    (hεεδ : ((ε + ε : ℝ≥0) : ℝ≥0∞) < δ)
    (heq : (pringsheimSeries a).sum =ᶠ[𝓝 (((R - ε : ℝ≥0) : ℝ) : ℂ)] g) :
    (ε : ℝ≥0∞) <
      ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  let r0 : ℝ≥0 := R - ε
  let zR : ℂ := ((R : ℝ) : ℂ)
  let z0 : ℂ := ((r0 : ℝ) : ℂ)
  let y : ℂ := -(((ε : ℝ) : ℂ))
  have hy_norm : ‖y‖₊ = ε := by
    simp [y]
  have hcenter : zR + y = z0 := by
    have hεRle : ε ≤ R := hεR.le
    have hz0 : z0 = zR - (((ε : ℝ) : ℂ)) := by
      simp [z0, zR, r0, NNReal.coe_sub hεRle]
    calc
      zR + y = zR - (((ε : ℝ) : ℂ)) := by simp [y, sub_eq_add_neg]
      _ = z0 := hz0.symm
  have hεδ : (‖y‖₊ : ℝ≥0∞) < δ := by
    rw [hy_norm]
    exact (ENNReal.coe_le_coe.2 (by simp : ε ≤ ε + ε)).trans_lt hεεδ
  have hgShift₀ : HasFPowerSeriesOnBall g (q.changeOrigin y) (zR + y) (δ - ‖y‖₊) :=
    hg.changeOrigin hεδ
  have hgShift : HasFPowerSeriesOnBall g (q.changeOrigin y) z0 (δ - (ε : ℝ≥0∞)) := by
    simpa [hcenter, hy_norm] using hgShift₀
  have hp0 : HasFPowerSeriesOnBall p.sum p (0 : ℂ) p.radius := by
    exact FormalMultilinearSeries.hasFPowerSeriesOnBall p
      (by simpa [p] using radius_pos_of_radius_eq a hRpos hR)
  have hr0_lt_R : r0 < R := by
    exact sub_lt_self_nnreal hRpos hεpos
  have hr0_lt_radius : (r0 : ℝ≥0∞) < p.radius := by
    simpa [p, hR] using ENNReal.coe_lt_coe.2 hr0_lt_R
  have hz0_norm : ‖z0‖₊ = r0 := by
    simp [z0]
  have hpShift₀ :
      HasFPowerSeriesOnBall p.sum (p.changeOrigin z0) ((0 : ℂ) + z0)
        (p.radius - ‖z0‖₊) :=
    hp0.changeOrigin (by simpa [hz0_norm] using hr0_lt_radius)
  have hpShift :
      HasFPowerSeriesOnBall p.sum (p.changeOrigin z0) z0
        (p.radius - (r0 : ℝ≥0∞)) := by
    simpa [hz0_norm] using hpShift₀
  have hseries :
      p.changeOrigin z0 = q.changeOrigin y :=
    hpShift.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
      hgShift.hasFPowerSeriesAt (by simpa [p, z0, r0] using heq)
  have hlarge :
      δ - (ε : ℝ≥0∞) ≤ (p.changeOrigin z0).radius := by
    simpa [hseries] using hgShift.r_le
  have hε_lt_sub : (ε : ℝ≥0∞) < δ - (ε : ℝ≥0∞) := by
    rw [lt_tsub_iff_right]
    simpa using hεεδ
  exact hε_lt_sub.trans_le (by simpa [p, z0, r0] using hlarge)

private lemma contradiction_of_shifted_radius_gt
    (a : ℕ → ℝ≥0) {R ε : ℝ≥0}
    (hRpos : 0 < R)
    (hR : (pringsheimSeries a).radius = (R : ℝ≥0∞))
    (hεpos : 0 < ε) (hεR : ε < R)
    (hshift :
      (ε : ℝ≥0∞) <
        ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius) :
    False := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  let r0 : ℝ≥0 := R - ε
  obtain ⟨t, hεt, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hshift
  have hr0_lt_R : r0 < R := sub_lt_self_nnreal hRpos hεpos
  have hr0_lt_radius : (r0 : ℝ≥0∞) < p.radius := by
    simpa [p, hR] using ENNReal.coe_lt_coe.2 hr0_lt_R
  have hcore :
      ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
    exact FormalMultilinearSeries.le_radius_add_of_lt_changeOrigin_radius_of_nonneg
      (a := a) (r0 := r0) (t := t) hr0_lt_radius
      (by simpa [p, r0] using ht)
  have hleR : ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ (R : ℝ≥0∞) := by
    simpa [p, hR] using hcore
  have hεt_nn : ε < t := ENNReal.coe_lt_coe.1 hεt
  have hR_lt_r0t : R < r0 + t := by
    rw [← NNReal.coe_lt_coe]
    have hεRle : ε ≤ R := hεR.le
    rw [NNReal.coe_add, NNReal.coe_sub hεRle]
    have hεt' : (ε : ℝ) < t := by exact_mod_cast hεt_nn
    linarith
  exact (not_lt_of_ge hleR) (ENNReal.coe_lt_coe.2 hR_lt_r0t)

private lemma choose_epsilon_two_lt
    {R δ₀ : ℝ≥0} (hRpos : 0 < R) (hδpos : 0 < δ₀) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε < R ∧ ε + ε < δ₀ := by
  let m : ℝ≥0 := min R δ₀
  have hmpos : 0 < m := by
    simp [m, hRpos, hδpos]
  refine ⟨m / 4, nnreal_quarter_pos hmpos, ?_, ?_⟩
  · exact (nnreal_quarter_lt hmpos).trans_le (min_le_left _ _)
  · exact (nnreal_two_mul_quarter_lt hmpos).trans_le (min_le_right _ _)

private lemma choose_epsilon_two_lt_two
    {R δ₀ η₀ : ℝ≥0} (hRpos : 0 < R) (hδpos : 0 < δ₀) (hηpos : 0 < η₀) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε < R ∧ ε + ε < δ₀ ∧ ε + ε < η₀ := by
  let m : ℝ≥0 := min R (min δ₀ η₀)
  have hmpos : 0 < m := by
    simp [m, hRpos, hδpos, hηpos]
  refine ⟨m / 4, nnreal_quarter_pos hmpos, ?_, ?_, ?_⟩
  · exact (nnreal_quarter_lt hmpos).trans_le (min_le_left _ _)
  · exact (nnreal_two_mul_quarter_lt hmpos).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · exact (nnreal_two_mul_quarter_lt hmpos).trans_le ((min_le_right _ _).trans (min_le_right _ _))

theorem pringsheim_not_analyticAt
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR :
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius =
        (R : ℝ≥0∞)) :
    ¬ AnalyticAt ℂ
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).sum
      (((R : ℝ) : ℂ)) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  change ¬ AnalyticAt ℂ p.sum (((R : ℝ) : ℂ))
  intro h
  obtain ⟨q, δ, hq⟩ := h
  obtain ⟨δ₀, hδ₀posE, hδ₀δ⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hq.r_pos
  have hδ₀pos : 0 < δ₀ := by
    simpa using hδ₀posE
  obtain ⟨ε, hεpos, hεR, hεεδ₀⟩ :=
    choose_epsilon_two_lt (R := R) (δ₀ := δ₀) hRpos hδ₀pos
  have hεεδ : ((ε + ε : ℝ≥0) : ℝ≥0∞) < δ :=
    (ENNReal.coe_lt_coe.2 hεεδ₀).trans hδ₀δ
  have hshift :
      (ε : ℝ≥0∞) <
        ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius := by
    apply shifted_radius_gt (a := a) (R := R) (ε := ε) (g := p.sum)
      (q := q) (δ := δ) hRpos
    · simpa [p] using hR
    · exact hεpos
    · exact hεR
    · simpa [p] using hq
    · exact hεεδ
    · exact Eventually.of_forall fun _ => rfl
  exact contradiction_of_shifted_radius_gt (a := a) (R := R) (ε := ε)
    hRpos (by simpa using hR) hεpos hεR hshift

private lemma eventually_eq_near_inner_of_eventually_eq_within
    {a : ℕ → ℝ≥0} {R ε : ℝ≥0} {g : ℂ → ℂ} {η : ℝ≥0∞}
    (hεpos : 0 < ε) (hεR : ε < R)
    (hεεη : ((ε + ε : ℝ≥0) : ℝ≥0∞) < η)
    (hwithin :
      Metric.eball (((R : ℝ) : ℂ)) η ∩
          Metric.eball (0 : ℂ) (R : ℝ≥0∞) ⊆
        {z | g z = (pringsheimSeries a).sum z}) :
    g =ᶠ[𝓝 (((R - ε : ℝ≥0) : ℝ) : ℂ)] (pringsheimSeries a).sum := by
  let r0 : ℝ≥0 := R - ε
  let zR : ℂ := ((R : ℝ) : ℂ)
  let z0 : ℂ := ((r0 : ℝ) : ℂ)
  have hεRle : ε ≤ R := hεR.le
  have hz0R : edist z0 zR = (ε : ℝ≥0∞) := by
    rw [edist_eq_enorm_sub]
    have hdiff : z0 - zR = -(((ε : ℝ) : ℂ)) := by
      simp [z0, zR, r0, NNReal.coe_sub hεRle]
    rw [hdiff]
    simp [enorm_eq_nnnorm]
  have hz00 : edist z0 (0 : ℂ) = (r0 : ℝ≥0∞) := by
    rw [edist_eq_enorm_sub]
    simp [z0, enorm_eq_nnnorm]
  have hsumR : ε + r0 = R := add_sub_cancel_nnreal hεRle
  have hball :
      Metric.eball z0 (ε : ℝ≥0∞) ⊆
        {z | g z = (pringsheimSeries a).sum z} := by
    intro z hz
    apply hwithin
    constructor
    · rw [Metric.mem_eball]
      have hzdist : edist z z0 < (ε : ℝ≥0∞) := by
        simpa [z0] using (Metric.mem_eball.1 hz)
      calc
        edist z zR ≤ edist z z0 + edist z0 zR := edist_triangle _ _ _
        _ < (ε : ℝ≥0∞) + (ε : ℝ≥0∞) := by
          rw [hz0R]
          exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hzdist
        _ = ((ε + ε : ℝ≥0) : ℝ≥0∞) := by simp
        _ < η := hεεη
    · rw [Metric.mem_eball]
      have hzdist : edist z z0 < (ε : ℝ≥0∞) := by
        simpa [z0] using (Metric.mem_eball.1 hz)
      calc
        edist z (0 : ℂ) ≤ edist z z0 + edist z0 (0 : ℂ) := edist_triangle _ _ _
        _ < (ε : ℝ≥0∞) + (r0 : ℝ≥0∞) := by
          rw [hz00]
          exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hzdist
        _ = ((ε + r0 : ℝ≥0) : ℝ≥0∞) := by simp
        _ = (R : ℝ≥0∞) := by rw [hsumR]
  exact eventually_of_mem
    (Metric.eball_mem_nhds z0 (by simpa using (ENNReal.coe_pos.2 hεpos)))
    hball

theorem pringsheim_not_analyticContinuation
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR :
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius =
        (R : ℝ≥0∞)) :
    ¬ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (((R : ℝ) : ℂ)) ∧
      g =ᶠ[𝓝[Metric.eball (0 : ℂ) (R : ℝ≥0∞)] (((R : ℝ) : ℂ))]
        (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).sum := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := pringsheimSeries a
  change ¬ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (((R : ℝ) : ℂ)) ∧
      g =ᶠ[𝓝[Metric.eball (0 : ℂ) (R : ℝ≥0∞)] (((R : ℝ) : ℂ))] p.sum
  rintro ⟨g, hg, hgeq⟩
  obtain ⟨q, δ, hq⟩ := hg
  obtain ⟨η, hηpos, hηsubset⟩ :=
    EMetric.mem_nhdsWithin_iff.1 hgeq
  obtain ⟨δ₀, hδ₀posE, hδ₀δ⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hq.r_pos
  obtain ⟨η₀, hη₀posE, hη₀η⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hηpos
  have hδ₀pos : 0 < δ₀ := by
    simpa using hδ₀posE
  have hη₀pos : 0 < η₀ := by
    simpa using hη₀posE
  obtain ⟨ε, hεpos, hεR, hεεδ₀, hεεη₀⟩ :=
    choose_epsilon_two_lt_two (R := R) (δ₀ := δ₀) (η₀ := η₀)
      hRpos hδ₀pos hη₀pos
  have hεεδ : ((ε + ε : ℝ≥0) : ℝ≥0∞) < δ :=
    (ENNReal.coe_lt_coe.2 hεεδ₀).trans hδ₀δ
  have hεεη : ((ε + ε : ℝ≥0) : ℝ≥0∞) < η :=
    (ENNReal.coe_lt_coe.2 hεεη₀).trans hη₀η
  have heq_inner :
      g =ᶠ[𝓝 (((R - ε : ℝ≥0) : ℝ) : ℂ)] p.sum := by
    exact eventually_eq_near_inner_of_eventually_eq_within
      (a := a) (R := R) (ε := ε) (g := g) (η := η)
      hεpos hεR hεεη (by simpa [p] using hηsubset)
  have hshift :
      (ε : ℝ≥0∞) <
        ((pringsheimSeries a).changeOrigin (((R - ε : ℝ≥0) : ℝ) : ℂ)).radius := by
    apply shifted_radius_gt (a := a) (R := R) (ε := ε) (g := g)
      (q := q) (δ := δ) hRpos
    · simpa [p] using hR
    · exact hεpos
    · exact hεR
    · exact hq
    · exact hεεδ
    · simpa [p] using heq_inner.symm
  exact contradiction_of_shifted_radius_gt (a := a) (R := R) (ε := ε)
    hRpos (by simpa using hR) hεpos hεR hshift
