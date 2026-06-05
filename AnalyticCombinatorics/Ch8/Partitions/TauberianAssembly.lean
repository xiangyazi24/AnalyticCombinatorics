import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.Tauberian
import AnalyticCombinatorics.Ch8.Partitions.TauberianFull

/-!
# Assembly of the logarithmic Tauberian theorem

This file assembles the already-proved Abel and saddle-window estimates into
the cumulative logarithmic Tauberian theorem.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

private lemma pos_zero_of_one_le {a : ℕ → ℝ} (ha0 : 1 ≤ a 0) : 0 < a 0 := by
  linarith

private lemma laplace_pos_of_one_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {t : ℝ}
    (hsum : Summable fun n : ℕ => a n * Real.exp (-(t * n))) :
    0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
  laplace_tsum_pos_of_pos_zero ha (pos_zero_of_one_le ha0) hsum

private lemma Cum_pos_of_one_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0) (N : ℕ) :
    0 < Cum a N :=
  Cum_pos_of_pos_zero ha (pos_zero_of_one_le ha0) N

private lemma sqrt_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

private lemma sqrtK_div_sqrtN_tendsto_nhdsWithin_zero
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun N : ℕ => Real.sqrt K / Real.sqrt (N : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
  have hnhds :
      Tendsto (fun N : ℕ => Real.sqrt K / Real.sqrt (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop sqrt_nat_tendsto_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt K / Real.sqrt (N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    exact div_pos (Real.sqrt_pos.mpr hK) (Real.sqrt_pos.mpr hNpos)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩

theorem tauberian_cum_limsup
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Real.log (Cum a N) ≤
        (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := by
  intro ε hε
  have hF_upper :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n)))
          ≤ K + ε * Real.sqrt K :=
    hF.eventually (eventually_le_nhds (by
      have hmul : 0 < ε * Real.sqrt K := by positivity
      linarith))
  have hcomp :
      ∀ᶠ N : ℕ in atTop,
        (Real.sqrt K / Real.sqrt (N : ℝ))
          * Real.log
              (∑' n : ℕ,
                a n * Real.exp (-((Real.sqrt K / Real.sqrt (N : ℝ)) * n)))
          ≤ K + ε * Real.sqrt K :=
    (sqrtK_div_sqrtN_tendsto_nhdsWithin_zero hK).eventually hF_upper
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcomp] with N hN hFN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqrtK_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  let t : ℝ := Real.sqrt K / Real.sqrt (N : ℝ)
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos hsqrtK_pos hsqrtN_pos
  have hlog_bound :
      Real.log (∑' n : ℕ, a n * Real.exp (-(t * n)))
        ≤ (K + ε * Real.sqrt K) / t := by
    rw [le_div_iff₀ ht]
    simpa [mul_comm, t] using hFN
  have hbase :=
    log_Cum_le_laplace (a := a) ha (pos_zero_of_one_le ha0) (t := t) ht (hsum t ht) N
  have halg :
      t * (N : ℝ) + (K + ε * Real.sqrt K) / t
        = (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := by
    dsimp [t]
    field_simp [hsqrtN_pos.ne', hsqrtK_pos.ne']
    rw [Real.sq_sqrt hK.le, Real.sq_sqrt hNpos.le]
    nlinarith [Real.sq_sqrt hK.le]
  calc
    Real.log (Cum a N)
        ≤ t * (N : ℝ)
            + Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := hbase
    _ ≤ t * (N : ℝ) + (K + ε * Real.sqrt K) / t := by linarith
    _ = (2 * Real.sqrt K + ε) * Real.sqrt (N : ℝ) := halg

theorem tauberian_cum_global_bound
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ η > 0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ,
        Cum a N ≤ C * Real.exp ((2 * Real.sqrt K + η) * Real.sqrt (N : ℝ)) := by
  intro η hη
  let B : ℝ := 2 * Real.sqrt K + η
  have hEv := tauberian_cum_limsup a ha ha0 hK hsum hF η hη
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hEv
  let C0 : ℝ :=
    ∑ N ∈ Finset.range N0,
      Cum a N / Real.exp (B * Real.sqrt (N : ℝ))
  let C : ℝ := max 1 C0
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 C0)
  refine ⟨C, hC_nonneg, ?_⟩
  intro N
  let E : ℝ := Real.exp (B * Real.sqrt (N : ℝ))
  have hEpos : 0 < E := by dsimp [E]; positivity
  by_cases hlt : N < N0
  · have hmem : N ∈ Finset.range N0 := Finset.mem_range.mpr hlt
    have hratio_nonneg :
        ∀ M ∈ Finset.range N0,
          0 ≤ Cum a M / Real.exp (B * Real.sqrt (M : ℝ)) := by
      intro M _hM
      exact div_nonneg (Cum_nonneg ha M) (Real.exp_pos _).le
    have hratio_le_C0 :
        Cum a N / Real.exp (B * Real.sqrt (N : ℝ)) ≤ C0 := by
      dsimp [C0]
      exact Finset.single_le_sum hratio_nonneg hmem
    have hratio_le_C : Cum a N / E ≤ C := by
      dsimp [E, C]
      exact hratio_le_C0.trans (le_max_right 1 C0)
    rwa [div_le_iff₀ hEpos] at hratio_le_C
  · have hge : N0 ≤ N := le_of_not_gt hlt
    have hlog : Real.log (Cum a N) ≤ B * Real.sqrt (N : ℝ) := by
      simpa [B] using hN0 N hge
    have hcum_exp :
        Cum a N ≤ Real.exp (B * Real.sqrt (N : ℝ)) :=
      (Real.log_le_iff_le_exp (Cum_pos_of_one_le ha ha0 N)).mp hlog
    have hCge_one : 1 ≤ C := by
      dsimp [C]
      exact le_max_left 1 C0
    calc
      Cum a N ≤ Real.exp (B * Real.sqrt (N : ℝ)) := hcum_exp
      _ ≤ C * Real.exp (B * Real.sqrt (N : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_right hCge_one (Real.exp_pos _).le

theorem tauberian_exists_large_cum_near_saddle
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ t in 𝓝[>] 0, ∃ N : ℕ,
      (1 - δ) * K / t ^ 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (1 + δ) * K / t ^ 2 ∧
      (2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
  rcases sqrt_laplace_bad_inside_gap (K := K) (ε := ε) hK hε with
    ⟨ρw, hρw, hwinGapEv⟩
  rcases sqrt_laplace_restricted_gap_strong (K := K) (δ := δ) hK hδ hδ1 with
    ⟨η, ρo, hη, hρo, hoffGapEv⟩
  rcases tauberian_cum_global_bound a ha ha0 hK hsum hF η hη with
    ⟨C, hC, hglobal⟩
  let r0 : ℝ := min ρw (ρo / 2)
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min hρw (half_pos hρo)
  let τ : ℝ := r0 / 2
  have hτ : 0 < τ := by
    dsimp [τ]
    exact half_pos hr0
  have hCabsEv : ∀ᶠ t : ℝ in 𝓝[>] 0, C ≤ Real.exp ((ρo / 2) / t) :=
    const_le_exp_inv_eventually (D := C) (c := ρo / 2) (half_pos hρo)
  have htwoEv : ∀ᶠ t : ℝ in 𝓝[>] 0, (2 : ℝ) ≤ Real.exp (τ / t) :=
    const_le_exp_inv_eventually (D := (2 : ℝ)) (c := τ) hτ
  have hFLowerEv :
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        K - τ / 2 ≤
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) :=
    hF.eventually (eventually_ge_nhds (by
      have hpos : 0 < τ / 2 := half_pos hτ
      linarith))
  filter_upwards
    [self_mem_nhdsWithin, hwinGapEv, hoffGapEv, hCabsEv, htwoEv, hFLowerEv]
    with t ht hwinGap hoffGap hCabs htwo hFLower
  have htpos : 0 < t := ht
  by_contra hno
  let W : ℕ → Prop := fun N =>
    (1 - δ) * K / t ^ 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ (1 + δ) * K / t ^ 2
  let Bbad : ℝ := 2 * Real.sqrt K - ε
  let Boff : ℝ := 2 * Real.sqrt K + η
  let full : ℕ → ℝ := fun N => Cum a N * Real.exp (-(t * (N : ℝ)))
  let win : ℕ → ℝ := fun N => if W N then full N else 0
  let off : ℕ → ℝ := fun N => if W N then 0 else full N
  let bad : ℕ → ℝ := fun N =>
    Real.exp (Bbad * Real.sqrt (N : ℝ) - t * (N : ℝ))
  let rterm : ℕ → ℝ := fun N =>
    if W N then 0 else Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ))
  let fac : ℝ := 1 - Real.exp (-t)
  have hfac_nonneg : 0 ≤ fac := by
    dsimp [fac]
    have hexp_lt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
    linarith
  have hfac_le_one : fac ≤ 1 := by
    dsimp [fac]
    linarith [Real.exp_pos (-t)]
  have hbad_summable : Summable bad := by
    dsimp [bad, Bbad]
    exact exp_sqrt_sub_linear_summable ht
  have hwin_nonneg : ∀ N, 0 ≤ win N := by
    intro N
    dsimp [win, full]
    split
    · exact mul_nonneg (Cum_nonneg ha N) (Real.exp_pos _).le
    · norm_num
  have hwin_le_bad : ∀ N, win N ≤ bad N := by
    intro N
    dsimp [win, bad]
    by_cases hW : W N
    · simp only [hW, ↓reduceIte, full]
      have hnot :
          ¬ Bbad * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
        intro hlarge
        exact hno ⟨N, hW.1, hW.2, by simpa [Bbad] using hlarge⟩
      have hlog_lt : Real.log (Cum a N) < Bbad * Real.sqrt (N : ℝ) :=
        not_le.mp hnot
      have hcum_le : Cum a N ≤ Real.exp (Bbad * Real.sqrt (N : ℝ)) :=
        (Real.log_le_iff_le_exp (Cum_pos_of_one_le ha ha0 N)).mp (le_of_lt hlog_lt)
      have hmul :=
        mul_le_mul_of_nonneg_right hcum_le (Real.exp_pos (-(t * (N : ℝ)))).le
      calc
        Cum a N * Real.exp (-(t * (N : ℝ)))
            ≤ Real.exp (Bbad * Real.sqrt (N : ℝ)) * Real.exp (-(t * (N : ℝ))) := hmul
        _ = Real.exp (Bbad * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
          rw [← Real.exp_add]
          ring_nf
    · simp only [hW, ↓reduceIte]
      positivity
  have hwin_summable : Summable win :=
    hbad_summable.of_nonneg_of_le hwin_nonneg hwin_le_bad
  have hrterm_nonneg : ∀ N, 0 ≤ rterm N := by
    intro N
    dsimp [rterm]
    split <;> positivity
  have hrterm_le_full : ∀ N,
      rterm N ≤ Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
    intro N
    dsimp [rterm]
    split
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hrterm_summable : Summable rterm :=
    (exp_sqrt_sub_linear_summable (B := Boff) htpos).of_nonneg_of_le
      hrterm_nonneg hrterm_le_full
  have hoff_nonneg : ∀ N, 0 ≤ off N := by
    intro N
    dsimp [off, full]
    split
    · norm_num
    · exact mul_nonneg (Cum_nonneg ha N) (Real.exp_pos _).le
  have hoff_le_Crterm : ∀ N, off N ≤ C * rterm N := by
    intro N
    dsimp [off, rterm]
    by_cases hW : W N
    · simp [hW]
    · simp only [hW, ↓reduceIte, full]
      have hglob : Cum a N ≤ C * Real.exp (Boff * Real.sqrt (N : ℝ)) := by
        simpa [Boff] using hglobal N
      have hmul :=
        mul_le_mul_of_nonneg_right hglob (Real.exp_pos (-(t * (N : ℝ)))).le
      calc
        Cum a N * Real.exp (-(t * (N : ℝ)))
            ≤ (C * Real.exp (Boff * Real.sqrt (N : ℝ)))
                * Real.exp (-(t * (N : ℝ))) := hmul
        _ = C * Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
          calc
            (C * Real.exp (Boff * Real.sqrt (N : ℝ))) * Real.exp (-(t * (N : ℝ)))
                = C * (Real.exp (Boff * Real.sqrt (N : ℝ))
                    * Real.exp (-(t * (N : ℝ)))) := by ring
            _ = C * Real.exp (Boff * Real.sqrt (N : ℝ) - t * (N : ℝ)) := by
              rw [← Real.exp_add]
              ring_nf
  have hCrterm_summable : Summable fun N : ℕ => C * rterm N :=
    hrterm_summable.mul_left C
  have hoff_summable : Summable off :=
    hCrterm_summable.of_nonneg_of_le hoff_nonneg hoff_le_Crterm
  have hwin_tsum_le : (∑' N : ℕ, win N) ≤ ∑' N : ℕ, bad N :=
    hwin_summable.tsum_le_tsum hwin_le_bad hbad_summable
  have hoff_tsum_le_C :
      (∑' N : ℕ, off N) ≤ C * (∑' N : ℕ, rterm N) := by
    calc
      (∑' N : ℕ, off N)
          ≤ ∑' N : ℕ, C * rterm N :=
            hoff_summable.tsum_le_tsum hoff_le_Crterm hCrterm_summable
      _ = C * (∑' N : ℕ, rterm N) := by
            rw [tsum_mul_left]
  have hbad_gap :
      fac * (∑' N : ℕ, bad N) ≤ Real.exp ((K - ρw) / t) := by
    simpa [fac, bad, Bbad] using hwinGap
  have hrterm_gap :
      (∑' N : ℕ, rterm N) ≤ Real.exp ((K - ρo) / t) := by
    simpa [rterm, W, Boff] using hoffGap
  have hsplit :
      (∑' N : ℕ, full N) = (∑' N : ℕ, win N) + (∑' N : ℕ, off N) := by
    calc
      (∑' N : ℕ, full N)
          = ∑' N : ℕ, (win N + off N) := by
            apply tsum_congr
            intro N
            dsimp [win, off]
            by_cases hW : W N <;> simp [hW]
      _ = (∑' N : ℕ, win N) + (∑' N : ℕ, off N) :=
            (hwin_summable.hasSum.add hoff_summable.hasSum).tsum_eq
  have hwin_part :
      fac * (∑' N : ℕ, win N) ≤ Real.exp ((K - r0) / t) := by
    have hmul : fac * (∑' N : ℕ, win N) ≤ fac * (∑' N : ℕ, bad N) :=
      mul_le_mul_of_nonneg_left hwin_tsum_le hfac_nonneg
    have hr0_le : r0 ≤ ρw := by
      dsimp [r0]
      exact min_le_left _ _
    have hexp_le :
        Real.exp ((K - ρw) / t) ≤ Real.exp ((K - r0) / t) :=
      Real.exp_monotone <|
        div_le_div_of_nonneg_right (by linarith) htpos.le
    exact (hmul.trans hbad_gap).trans hexp_le
  have hoff_part :
      fac * (∑' N : ℕ, off N) ≤ Real.exp ((K - r0) / t) := by
    have hoff_tsum_nonneg : 0 ≤ ∑' N : ℕ, off N :=
      tsum_nonneg hoff_nonneg
    have hfac_drop : fac * (∑' N : ℕ, off N) ≤ ∑' N : ℕ, off N := by
      simpa using mul_le_mul_of_nonneg_right hfac_le_one hoff_tsum_nonneg
    have htoC : fac * (∑' N : ℕ, off N) ≤ C * (∑' N : ℕ, rterm N) :=
      hfac_drop.trans hoff_tsum_le_C
    have htoGap :
        C * (∑' N : ℕ, rterm N) ≤ C * Real.exp ((K - ρo) / t) :=
      mul_le_mul_of_nonneg_left hrterm_gap hC
    have habsorb :
        C * Real.exp ((K - ρo) / t) ≤ Real.exp ((K - ρo / 2) / t) := by
      have hmul :=
        mul_le_mul_of_nonneg_right hCabs (Real.exp_pos ((K - ρo) / t)).le
      calc
        C * Real.exp ((K - ρo) / t)
            ≤ Real.exp ((ρo / 2) / t) * Real.exp ((K - ρo) / t) := hmul
        _ = Real.exp ((K - ρo / 2) / t) := by
          rw [← Real.exp_add]
          congr
          field_simp [htpos.ne']
          ring
    have hr0_le : r0 ≤ ρo / 2 := by
      dsimp [r0]
      exact min_le_right _ _
    have hexp_le :
        Real.exp ((K - ρo / 2) / t) ≤ Real.exp ((K - r0) / t) :=
      Real.exp_monotone <|
        div_le_div_of_nonneg_right (by linarith) htpos.le
    exact (htoC.trans htoGap).trans (habsorb.trans hexp_le)
  have hF_upper_point :
      (∑' n : ℕ, a n * Real.exp (-(t * n))) ≤ Real.exp ((K - τ) / t) := by
    have habel := laplace_eq_abel_cum a ha htpos (hsum t htpos)
    have hpre :
        (∑' n : ℕ, a n * Real.exp (-(t * n)))
          ≤ 2 * Real.exp ((K - r0) / t) := by
      calc
        (∑' n : ℕ, a n * Real.exp (-(t * n)))
            = fac * (∑' N : ℕ, full N) := by
              simpa [fac, full] using habel
        _ = fac * ((∑' N : ℕ, win N) + (∑' N : ℕ, off N)) := by
              rw [hsplit]
        _ = fac * (∑' N : ℕ, win N) + fac * (∑' N : ℕ, off N) := by
              ring
        _ ≤ Real.exp ((K - r0) / t) + Real.exp ((K - r0) / t) :=
              add_le_add hwin_part hoff_part
        _ = 2 * Real.exp ((K - r0) / t) := by ring
    have habsorb :
        2 * Real.exp ((K - r0) / t) ≤ Real.exp ((K - τ) / t) := by
      have hmul :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos ((K - r0) / t)).le
      calc
        2 * Real.exp ((K - r0) / t)
            ≤ Real.exp (τ / t) * Real.exp ((K - r0) / t) := hmul
        _ = Real.exp ((K - τ) / t) := by
          rw [← Real.exp_add]
          congr
          dsimp [τ]
          field_simp [htpos.ne']
          ring
    exact hpre.trans habsorb
  have hFpos : 0 < ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
    laplace_pos_of_one_le ha ha0 (hsum t htpos)
  have hlog_lower :
      (K - τ / 2) / t ≤
        Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))) := by
    rw [div_le_iff₀ ht]
    simpa [mul_comm] using hFLower
  have hF_lower_point :
      Real.exp ((K - τ / 2) / t) ≤
        ∑' n : ℕ, a n * Real.exp (-(t * n)) :=
    (Real.le_log_iff_exp_le hFpos).mp hlog_lower
  have hstrict :
      Real.exp ((K - τ) / t) < Real.exp ((K - τ / 2) / t) :=
    Real.exp_lt_exp.mpr <|
      div_lt_div_of_pos_right (by linarith [hτ]) htpos
  exact not_lt_of_ge hF_lower_point (hF_upper_point.trans_lt hstrict)

private lemma sqrt_const_div_nat_tendsto_nhdsWithin_zero
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝[>] (0 : ℝ)) := by
  have harg :
      Tendsto (fun M : ℕ => A / (M : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)
  have hnhds :
      Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp harg
  have hpos : ∀ᶠ M : ℕ in atTop, 0 < Real.sqrt (A / (M : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
    exact Real.sqrt_pos.mpr (div_pos hA hMpos)
  exact tendsto_nhdsWithin_iff.mpr ⟨hnhds, hpos⟩

theorem tauberian_cum_eventual_lower
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    ∀ γ > 0, ∀ᶠ M : ℕ in atTop,
      (2 * Real.sqrt K - γ) * Real.sqrt (M : ℝ) ≤ Real.log (Cum a M) := by
  intro γ hγ
  let s : ℝ := Real.sqrt K
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr hK
  let ε : ℝ := min s (γ / 4)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hs (by positivity)
  have hε_le_s : ε ≤ s := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_γ : ε ≤ γ / 4 := by
    dsimp [ε]
    exact min_le_right _ _
  let δ : ℝ := min (1 / 2 : ℝ) (γ / (16 * s))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδ_le_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ1 : δ < 1 := by linarith
  have hδ_le_γ : δ ≤ γ / (16 * s) := by
    dsimp [δ]
    exact min_le_right _ _
  let r : ℝ := (1 - δ) / (1 + δ)
  have hden_pos : 0 < 1 + δ := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith) hden_pos.le
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one hden_pos]
    linarith
  have hr_ge : 1 - 2 * δ ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hden_pos]
    nlinarith [sq_nonneg δ]
  have hsqrtr_ge_r : r ≤ Real.sqrt r := by
    rw [Real.le_sqrt hr_nonneg hr_nonneg]
    nlinarith [hr_nonneg, hr_le_one]
  have hsqrtr_ge : 1 - 2 * δ ≤ Real.sqrt r :=
    hr_ge.trans hsqrtr_ge_r
  have hδ_loss : 4 * s * δ ≤ γ / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hδ_le_γ (by positivity : 0 ≤ 4 * s)
    have hs_ne : s ≠ 0 := hs.ne'
    calc
      4 * s * δ ≤ 4 * s * (γ / (16 * s)) := by
        simpa [mul_assoc] using hmul
      _ = γ / 4 := by
        field_simp [hs_ne]
        ring
  have hcoeff_nonneg : 0 ≤ 2 * s - ε := by linarith
  have hcoef_lower :
      2 * s - γ ≤ (2 * s - ε) * Real.sqrt r := by
    have hmul :
        (2 * s - ε) * (1 - 2 * δ) ≤ (2 * s - ε) * Real.sqrt r :=
      mul_le_mul_of_nonneg_left hsqrtr_ge hcoeff_nonneg
    have hbase : 2 * s - γ ≤ (2 * s - ε) * (1 - 2 * δ) := by
      have hεδ_nonneg : 0 ≤ 2 * ε * δ := by positivity
      nlinarith [hε_le_γ, hδ_loss, hεδ_nonneg]
    exact hbase.trans hmul
  let A : ℝ := (1 + δ) * K
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos hden_pos hK
  have hlocEv :=
    tauberian_exists_large_cum_near_saddle a ha ha0 hK hsum hF hε hδ hδ1
  have htend : Tendsto (fun M : ℕ => Real.sqrt (A / (M : ℝ))) atTop (𝓝[>] (0 : ℝ)) :=
    sqrt_const_div_nat_tendsto_nhdsWithin_zero hA
  have hlocM :
      ∀ᶠ M : ℕ in atTop,
        ∃ N : ℕ,
          (1 - δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 ≤ (N : ℝ) ∧
          (N : ℝ) ≤ (1 + δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 ∧
          (2 * Real.sqrt K - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) :=
    htend.eventually hlocEv
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlocM] with M hM hloc
  rcases hloc with ⟨N, hNL, hNU, hNlarge⟩
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let tM : ℝ := Real.sqrt (A / (M : ℝ))
  have htM_sq : tM ^ 2 = A / (M : ℝ) := by
    dsimp [tM]
    rw [Real.sq_sqrt (div_nonneg hA.le hMpos.le)]
  have hupper_eq : (1 + δ) * K / tM ^ 2 = (M : ℝ) := by
    rw [htM_sq]
    change A / (A / (M : ℝ)) = (M : ℝ)
    field_simp [hA.ne', hMpos.ne']
  have hlower_eq : (1 - δ) * K / tM ^ 2 = r * (M : ℝ) := by
    rw [htM_sq]
    dsimp [A, r]
    field_simp [hden_pos.ne', hK.ne', hMpos.ne']
  have hNU' : (N : ℝ) ≤ (M : ℝ) := by
    simpa [tM] using hNU.trans_eq hupper_eq
  have hNM : N ≤ M := by exact_mod_cast hNU'
  have hlower_eq' :
      (1 - δ) * K / (Real.sqrt (A / (M : ℝ))) ^ 2 = r * (M : ℝ) := by
    simpa [tM] using hlower_eq
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsqrtM_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hsqrt_div_sq :
      (Real.sqrt A / Real.sqrt (M : ℝ)) ^ 2 = A / (M : ℝ) := by
    field_simp [hsqrtM_pos.ne']
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hMpos.le]
    ring
  have hlower_eq'' :
      (1 - δ) * K / (Real.sqrt A / Real.sqrt (M : ℝ)) ^ 2 = r * (M : ℝ) := by
    rw [hsqrt_div_sq]
    dsimp [A, r]
    field_simp [hden_pos.ne', hK.ne', hMpos.ne']
  have hNL' : r * (M : ℝ) ≤ (N : ℝ) := by
    simpa [hlower_eq'', hlower_eq'] using hNL
  have hsqrt_rM_le_N : Real.sqrt (r * (M : ℝ)) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hNL'
  have hsqrt_rM :
      Real.sqrt (r * (M : ℝ)) = Real.sqrt r * Real.sqrt (M : ℝ) := by
    rw [Real.sqrt_mul hr_nonneg]
  have hcum_mono : Cum a N ≤ Cum a M :=
    Cum_mono ha hNM
  have hlog_mono : Real.log (Cum a N) ≤ Real.log (Cum a M) :=
    Real.log_le_log (Cum_pos_of_one_le ha ha0 N) hcum_mono
  have hfrom_local :
      (2 * s - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a M) := by
    have hlocal' :
        (2 * s - ε) * Real.sqrt (N : ℝ) ≤ Real.log (Cum a N) := by
      simpa [s] using hNlarge
    exact hlocal'.trans hlog_mono
  calc
    (2 * Real.sqrt K - γ) * Real.sqrt (M : ℝ)
        = (2 * s - γ) * Real.sqrt (M : ℝ) := by simp [s]
    _ ≤ ((2 * s - ε) * Real.sqrt r) * Real.sqrt (M : ℝ) := by
          exact mul_le_mul_of_nonneg_right hcoef_lower (Real.sqrt_nonneg _)
    _ = (2 * s - ε) * (Real.sqrt r * Real.sqrt (M : ℝ)) := by ring
    _ = (2 * s - ε) * Real.sqrt (r * (M : ℝ)) := by rw [hsqrt_rM]
    _ ≤ (2 * s - ε) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt_rM_le_N hcoeff_nonneg
    _ ≤ Real.log (Cum a M) := hfrom_local

theorem log_tauberian_cumulative_sqrt
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : 1 ≤ a 0)
    {K : ℝ} (hK : 0 < K)
    (hsum : ∀ t > 0, Summable fun n : ℕ => a n * Real.exp (-(t * n)))
    (hF :
      Tendsto
        (fun t : ℝ =>
          t * Real.log (∑' n : ℕ, a n * Real.exp (-(t * n))))
        (𝓝[>] 0) (𝓝 K)) :
    Tendsto
      (fun N : ℕ => Real.log (Cum a N) / Real.sqrt (N : ℝ))
      atTop
      (𝓝 (2 * Real.sqrt K)) := by
  rw [Metric.tendsto_nhds]
  intro γ hγ
  have hγ2 : 0 < γ / 2 := half_pos hγ
  have hupperEv :=
    tauberian_cum_limsup a ha ha0 hK hsum hF (γ / 2) hγ2
  have hlowerEv :=
    tauberian_cum_eventual_lower a ha ha0 hK hsum hF (γ / 2) hγ2
  filter_upwards [eventually_ge_atTop (1 : ℕ), hupperEv, hlowerEv] with N hN hupper hlower
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hupper_div :
      Real.log (Cum a N) / Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt K + γ / 2 := by
    rw [div_le_iff₀ hsqrtN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hupper
  have hlower_div :
      2 * Real.sqrt K - γ / 2 ≤
        Real.log (Cum a N) / Real.sqrt (N : ℝ) := by
    rw [le_div_iff₀ hsqrtN_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower
  have habs :
      |Real.log (Cum a N) / Real.sqrt (N : ℝ) - 2 * Real.sqrt K| < γ := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [Real.dist_eq] using habs

end

end AnalyticCombinatorics.Ch8.Partitions.Tauberian
