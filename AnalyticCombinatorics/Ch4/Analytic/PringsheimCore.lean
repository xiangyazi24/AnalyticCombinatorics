import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.Bridge

open Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section

namespace FormalMultilinearSeries

private lemma card_finset_fin_card_eq (k l : ℕ) :
    Fintype.card {s : Finset (Fin (k + l)) // s.card = l} = Nat.choose (k + l) l := by
  rw [Fintype.card_of_subtype (Finset.powersetCard l Finset.univ) (by intro s; simp)]
  simp

private lemma scalar_changeOriginSeries_eval_one
    (c : ℕ → ℂ) (x : ℂ) (k l : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ c).changeOriginSeries k l (fun _ => x))
      (fun _ => (1 : ℂ)) =
        (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
  unfold FormalMultilinearSeries.changeOriginSeries
  simp_rw [ContinuousMultilinearMap.sum_apply]
  simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  simp_rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp_rw [FormalMultilinearSeries.coeff_ofScalars]
  simp_rw [smul_eq_mul]
  have hprod (s : Finset (Fin (k + l))) (hs : s.card = l) :
      (∏ i : Fin (k + l), s.piecewise (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l := by
    change (∏ i ∈ (Finset.univ : Finset (Fin (k + l))),
      s.piecewise (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l
    rw [Finset.prod_piecewise]
    simp [hs]
  have hprod' (s : {s : Finset (Fin (k + l)) // s.card = l}) :
      (∏ i : Fin (k + l), (s : Finset (Fin (k + l))).piecewise
        (fun _ => x) (fun _ => (1 : ℂ)) i) = x ^ l :=
    hprod s.1 s.2
  simp_rw [hprod']
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [card_finset_fin_card_eq]
  rw [Nat.choose_symm_add]
  ring_nf

lemma ofScalars_changeOrigin_coeff
    (c : ℕ → ℂ) (x : ℂ) (k : ℕ)
    (hx : (‖x‖₊ : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    ((FormalMultilinearSeries.ofScalars ℂ c).changeOrigin x).coeff k =
      ∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hr : 0 < p.radius := lt_of_le_of_lt (zero_le _) hx
  have hxmem : x ∈ Metric.eball (0 : ℂ) p.radius := mem_eball_zero_iff.2 hx
  have hs := (p.hasFPowerSeriesOnBall_changeOrigin k hr).hasSum hxmem
  rw [zero_add] at hs
  rw [FormalMultilinearSeries.coeff]
  calc
    (p.changeOrigin x k) (fun _ : Fin k => (1 : ℂ))
        = ∑' l : ℕ,
            (p.changeOriginSeries k l (fun _ => x)) (fun _ : Fin k => (1 : ℂ)) :=
          (ContinuousMultilinearMap.hasSum_eval hs
            (fun _ : Fin k => (1 : ℂ))).tsum_eq.symm
    _ = ∑' l : ℕ,
          (Nat.choose (k + l) k : ℂ) * c (k + l) * x ^ l := by
          apply tsum_congr
          intro l
          simpa [p] using scalar_changeOriginSeries_eval_one c x k l

lemma ofScalars_changeOrigin_nnnorm
    (a : ℕ → ℝ≥0) (r0 : ℝ≥0) (k : ℕ)
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius) :
    ‖((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ) k)‖₊ =
      ∑' l : ℕ, (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
  let b : ℕ → ℝ≥0 := fun l => (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l
  have hcomplex :
      (∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * (a (k + l) : ℂ) *
          (((r0 : ℝ) : ℂ) ^ l)) = (((∑' l : ℕ, b l) : ℝ≥0) : ℂ) := by
    calc
      (∑' l : ℕ, (Nat.choose (k + l) k : ℂ) * (a (k + l) : ℂ) *
          (((r0 : ℝ) : ℂ) ^ l))
          = ∑' l : ℕ, (((b l : ℝ≥0) : ℝ) : ℂ) := by
            apply tsum_congr
            intro l
            simp [b, NNReal.coe_natCast]
      _ = (((∑' l : ℕ, ((b l : ℝ≥0) : ℝ)) : ℝ) : ℂ) := by
            exact (Complex.ofReal_tsum (fun l : ℕ => ((b l : ℝ≥0) : ℝ))).symm
      _ = (((∑' l : ℕ, b l) : ℝ≥0) : ℂ) := by
            rw [NNReal.coe_tsum]
  apply NNReal.eq
  rw [coe_nnnorm]
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef]
  rw [ofScalars_changeOrigin_coeff (fun n => (a n : ℂ)) ((r0 : ℝ) : ℂ) k]
  · rw [hcomplex]
    simp [b]
  · simpa using hr0

private lemma nnnorm_ofScalars_nnreal (a : ℕ → ℝ≥0) (n : ℕ) :
    ‖(FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) n)‖₊ = a n := by
  apply NNReal.eq
  simp

lemma inner_summable_changeOrigin_coeff_base
    (a : ℕ → ℝ≥0) (r0 : ℝ≥0) (k : ℕ)
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius) :
    Summable fun l : ℕ =>
      (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  have hsigma := p.changeOriginSeries_summable_aux₂ hr0 k
  have houter := (NNReal.summable_sigma.1 hsigma).2
  refine houter.congr ?_
  intro l
  have hfinite :
      (∑' s : {s : Finset (Fin (k + l)) // s.card = l}, ‖p (k + l)‖₊ * r0 ^ l) =
        (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l := by
    rw [tsum_fintype]
    rw [Finset.sum_const]
    rw [nsmul_eq_mul]
    rw [Finset.card_univ]
    rw [card_finset_fin_card_eq]
    rw [Nat.choose_symm_add]
    simp [p, nnnorm_ofScalars_nnreal, mul_assoc]
  simpa only [Sigma.fst] using hfinite

lemma summable_original_of_sigma
    (a : ℕ → ℝ≥0) (r0 t : ℝ≥0)
    (hsigma : Summable fun p : (Σ _ : ℕ, ℕ) =>
      (Nat.choose (p.1 + p.2) p.1 : ℝ≥0) * a (p.1 + p.2) *
        r0 ^ p.2 * t ^ p.1) :
    Summable fun n => a n * (r0 + t) ^ n := by
  let F : ℕ → ℕ → ℝ≥0 := fun k l =>
    (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l * t ^ k
  have hsigma' : Summable fun p : (Σ _ : ℕ, ℕ) => F p.1 p.2 := by
    simpa [F, mul_assoc] using hsigma
  let e : (Σ n : ℕ, Finset.antidiagonal n) ≃ (Σ _ : ℕ, ℕ) :=
    Finset.sigmaAntidiagonalEquivProd.trans (Equiv.sigmaEquivProd ℕ ℕ).symm
  have hant : Summable fun p : (Σ n : ℕ, Finset.antidiagonal n) =>
      F (p.2 : ℕ × ℕ).1 (p.2 : ℕ × ℕ).2 := by
    simpa [e, F] using (e.summable_iff.2 hsigma')
  have houter := (NNReal.summable_sigma.1 hant).2
  refine houter.congr ?_
  intro n
  have hcollapse :
      (∑ kl ∈ Finset.antidiagonal n,
          a n * (Nat.choose n kl.1 : ℝ≥0) * r0 ^ kl.2 * t ^ kl.1) =
        a n * (r0 + t) ^ n := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => a n * (Nat.choose n k : ℝ≥0) * r0 ^ l * t ^ k) n]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    rw [add_comm r0 t, add_pow]
    simp [mul_comm, mul_assoc]
  have htsum :
      (∑' kl : Finset.antidiagonal n, F (kl : ℕ × ℕ).1 (kl : ℕ × ℕ).2) =
        a n * (r0 + t) ^ n := by
    rw [tsum_fintype]
    calc
      (∑ b : Finset.antidiagonal n, F (b : ℕ × ℕ).1 (b : ℕ × ℕ).2)
          = ∑ kl ∈ Finset.antidiagonal n, F kl.1 kl.2 :=
            Finset.sum_finset_coe (fun kl : ℕ × ℕ => F kl.1 kl.2) (Finset.antidiagonal n)
      _ = ∑ kl ∈ Finset.antidiagonal n,
            a n * (Nat.choose n kl.1 : ℝ≥0) * r0 ^ kl.2 * t ^ kl.1 := by
            apply Finset.sum_congr rfl
            intro kl hkl
            have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
            simp [F, hsum, mul_comm, mul_left_comm]
      _ = a n * (r0 + t) ^ n := hcollapse
  simpa using htsum

lemma sigma_summable_changeOrigin_coeff
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0}
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius)
    (ht : (t : ℝ≥0∞) <
      ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ)).radius) :
    Summable fun p : (Σ _ : ℕ, ℕ) =>
      (Nat.choose (p.1 + p.2) p.1 : ℝ≥0) * a (p.1 + p.2) *
        r0 ^ p.2 * t ^ p.1 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  let base : ℕ → ℕ → ℝ≥0 := fun k l =>
    (Nat.choose (k + l) k : ℝ≥0) * a (k + l) * r0 ^ l
  have hinner : ∀ k : ℕ, Summable fun l : ℕ => base k l * t ^ k := by
    intro k
    exact (inner_summable_changeOrigin_coeff_base a r0 k hr0).mul_right (t ^ k)
  have hchange : Summable fun k : ℕ => ‖p.changeOrigin ((r0 : ℝ) : ℂ) k‖₊ * t ^ k := by
    exact (p.changeOrigin ((r0 : ℝ) : ℂ)).summable_nnnorm_mul_pow ht
  have houter : Summable fun k : ℕ => ∑' l : ℕ, base k l * t ^ k := by
    refine hchange.congr ?_
    intro k
    rw [ofScalars_changeOrigin_nnnorm a r0 k]
    · rw [NNReal.tsum_mul_right]
    · simpa [p] using hr0
  have hsigma : Summable fun q : (Σ _ : ℕ, ℕ) => base q.1 q.2 * t ^ q.1 :=
    NNReal.summable_sigma.2 ⟨hinner, houter⟩
  simpa [base, mul_assoc] using hsigma

lemma summable_original_of_summable_changeOrigin
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0}
    (hr0 : (r0 : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius)
    (ht : (t : ℝ≥0∞) <
      ((FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).changeOrigin
        ((r0 : ℝ) : ℂ)).radius) :
    Summable fun n => a n * (r0 + t) ^ n :=
  by
    exact summable_original_of_sigma a r0 t
      (sigma_summable_changeOrigin_coeff (a := a) (r0 := r0) (t := t) hr0 ht)

lemma le_radius_add_of_lt_changeOrigin_radius_of_nonneg
    (a : ℕ → ℝ≥0) {r0 t : ℝ≥0} :
    let p : FormalMultilinearSeries ℂ ℂ ℂ :=
      FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
    (r0 : ℝ≥0∞) < p.radius →
    (t : ℝ≥0∞) < (p.changeOrigin ((r0 : ℝ) : ℂ)).radius →
      ((r0 + t : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
  dsimp
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  intro hr0 ht
  apply p.le_radius_of_summable_nnnorm
  have hs : Summable fun n : ℕ => a n * (r0 + t) ^ n :=
    summable_original_of_summable_changeOrigin (a := a) (r0 := r0) (t := t) hr0 ht
  refine hs.congr ?_
  intro n
  simp [p, nnnorm_ofScalars_nnreal]

end FormalMultilinearSeries
