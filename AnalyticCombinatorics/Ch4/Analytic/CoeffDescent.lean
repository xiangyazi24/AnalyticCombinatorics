import AnalyticCombinatorics.Ch4.Analytic.OTransfer
import AnalyticCombinatorics.Ch4.Analytic.DerivEstimate

/-!
# Coefficient descent and general O-transfer

This file bootstraps the already-proved `β > 1` O-transfer theorem to all real
`β`.  The key bookkeeping device is the scalar one-variable derivative series:
take Mathlib's Frechet derivative series and apply it to `1`.
-/

open Complex Filter Asymptotics
open scoped Topology Real ENNReal BigOperators

noncomputable section

/-- The scalar one-variable derivative series associated to a scalar FMLS. -/
def scalarDerivSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

lemma scalarDerivSeries_coeff_smul (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = (n + 1) • p.coeff (n + 1) := by
  rw [scalarDerivSeries, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply']
  exact FormalMultilinearSeries.derivSeries_coeff_one p n

lemma scalarDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (scalarDerivSeries p).coeff n = (n + 1 : ℂ) * p.coeff (n + 1) := by
  rw [scalarDerivSeries_coeff_smul]
  simp [nsmul_eq_mul]

/-- The scalar FMLS for the `k`-th iterated derivative. -/
def scalarIteratedDerivSeries (k : ℕ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  match k with
  | 0 => p
  | k + 1 => scalarDerivSeries (scalarIteratedDerivSeries k p)

lemma HasFPowerSeriesOnBall.scalar_deriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (deriv f) (scalarDerivSeries p) x r := by
  convert (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv using 1

lemma HasFPowerSeriesOnBall.scalar_iterated_deriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) (k : ℕ) :
    HasFPowerSeriesOnBall ((deriv^[k]) f) (scalarIteratedDerivSeries k p) x r := by
  induction k with
  | zero => simpa [scalarIteratedDerivSeries] using h
  | succ k ih =>
      simpa [scalarIteratedDerivSeries, Function.iterate_succ_apply'] using ih.scalar_deriv

lemma HasFPowerSeriesAt.scalar_iteratedDeriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (h : HasFPowerSeriesAt f p (0 : ℂ)) (k : ℕ) :
    HasFPowerSeriesAt (iteratedDeriv k f) (scalarIteratedDerivSeries k p) (0 : ℂ) := by
  rcases h with ⟨r, hr⟩
  rw [iteratedDeriv_eq_iterate]
  exact (hr.scalar_iterated_deriv k).hasFPowerSeriesAt

theorem hasFPowerSeriesAt_iteratedDeriv
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p (0 : ℂ)) (k : ℕ) :
    HasFPowerSeriesAt (iteratedDeriv k f) (scalarIteratedDerivSeries k p) (0 : ℂ) :=
  hp.scalar_iteratedDeriv k

lemma scalarIteratedDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    (scalarIteratedDerivSeries k p).coeff m =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℂ)) * p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp [scalarIteratedDerivSeries]
  | succ k ih =>
      simp only [scalarIteratedDerivSeries]
      rw [scalarDerivSeries_coeff, ih]
      rw [Finset.prod_range_succ']
      simp_rw [Nat.cast_add, Nat.cast_one]
      ring_nf

theorem coeff_iteratedDeriv_eq
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (_hp : HasFPowerSeriesAt f p (0 : ℂ)) (k m : ℕ) :
    (scalarIteratedDerivSeries k p).coeff m =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℂ)) * p.coeff (m + k) :=
  scalarIteratedDerivSeries_coeff p k m

lemma complex_nat_prod_norm (k m : ℕ) :
    ‖(∏ j ∈ Finset.range k, (m + 1 + j : ℂ))‖ =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_congr rfl ?_
  intro j _hj
  have hc : ((m : ℂ) + 1 + (j : ℂ)) = ((m + 1 + j : ℕ) : ℂ) := by
    norm_num [Nat.cast_add]
  have hr : ((m : ℝ) + 1 + (j : ℝ)) = ((m + 1 + j : ℕ) : ℝ) := by
    norm_num [Nat.cast_add]
  rw [hc, hr, Complex.norm_natCast]

lemma scalarIteratedDerivSeries_coeff_norm (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    ‖(scalarIteratedDerivSeries k p).coeff m‖ =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖ := by
  rw [scalarIteratedDerivSeries_coeff]
  rw [norm_mul, complex_nat_prod_norm]

theorem coeff_iteratedDeriv_norm_eq
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (_hp : HasFPowerSeriesAt f p (0 : ℂ)) (k m : ℕ) :
    ‖(scalarIteratedDerivSeries k p).coeff m‖ =
      (∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖ :=
  scalarIteratedDerivSeries_coeff_norm p k m

lemma desc_prod_ge_pow (k m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) ^ k ≤ ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
  calc
    (m : ℝ) ^ k = ∏ j ∈ Finset.range k, (m : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
      refine Finset.prod_le_prod (fun j hj => by positivity) ?_
      intro j hj
      exact_mod_cast (by omega : m ≤ m + 1 + j)

lemma desc_prod_pos (k m : ℕ) :
    0 < ∏ j ∈ Finset.range k, (m + 1 + j : ℝ) := by
  refine Finset.prod_pos ?_
  intro j hj
  positivity

lemma inv_desc_prod_isBigO (k : ℕ) :
    (fun m : ℕ => (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpowpos : 0 < (m : ℝ) ^ k := pow_pos hmpos k
  have hle := desc_prod_ge_pow k m hm
  have hinv : (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ ≤ ((m : ℝ) ^ k)⁻¹ := by
    exact inv_anti₀ hpowpos hle
  have htarget : (m : ℝ) ^ (-(k : ℝ)) = ((m : ℝ) ^ k)⁻¹ := by
    rw [Real.rpow_neg hmpos.le (k : ℝ), Real.rpow_natCast]
  have hnonneg : 0 ≤ (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ := by positivity
  rw [Real.norm_of_nonneg hnonneg, htarget]
  simpa using hinv

lemma tail_isBigO_of_iterated_coeff_isBigO
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) (β : ℝ)
    (hderiv : (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β + k - 1))) :
    (fun m : ℕ => ‖p.coeff (m + k)‖) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
  let P : ℕ → ℝ := fun m => ∏ j ∈ Finset.range k, (m + 1 + j : ℝ)
  have heq : (fun m : ℕ => ‖p.coeff (m + k)‖) =ᶠ[atTop]
      (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) := by
    refine eventually_atTop.mpr ⟨0, fun m _hm => ?_⟩
    have hPpos : 0 < P m := by
      dsimp [P]
      exact desc_prod_pos k m
    have hdesc := scalarIteratedDerivSeries_coeff_norm p k m
    dsimp [P]
    calc
      ‖p.coeff (m + k)‖ = ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ((∏ j ∈ Finset.range k, (m + 1 + j : ℝ)) * ‖p.coeff (m + k)‖)) := by
            field_simp [hPpos.ne']
      _ = (∏ j ∈ Finset.range k, (m + 1 + j : ℝ))⁻¹ *
          ‖(scalarIteratedDerivSeries k p).coeff m‖ := by rw [hdesc]
  have hinvO : (fun m : ℕ => (P m)⁻¹) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (-(k : ℝ))) := by
    simpa [P] using inv_desc_prod_isBigO k
  have hmul : (fun m : ℕ => (P m)⁻¹ * ‖(scalarIteratedDerivSeries k p).coeff m‖) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β - 1)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := -(k : ℝ)) (b := β + k - 1) (c := β - 1)
      hinvO hderiv (by ring_nf; linarith)
  exact heq.trans_isBigO hmul

lemma nat_sub_const_isTheta (k : ℕ) :
    (fun n : ℕ => ((n - k : ℕ) : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · refine IsBigO.of_bound 1 ?_
    refine eventually_atTop.mpr ⟨0, fun n _hn => ?_⟩
    have hle : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.sub_le n k
    simp [hle]
  · refine IsBigO.of_bound 2 ?_
    refine eventually_atTop.mpr ⟨2 * k, fun n hn => ?_⟩
    have hnat : n ≤ 2 * (n - k) := by omega
    have hle : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg _), mul_comm, mul_assoc] using hle

lemma nat_sub_const_rpow_isBigO (k : ℕ) (e : ℝ) :
    (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ e) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ e) := by
  exact (IsTheta.rpow
    (eventually_atTop.mpr ⟨0, fun n _hn => by positivity⟩)
    (eventually_atTop.mpr ⟨0, fun n _hn => by positivity⟩)
    (nat_sub_const_isTheta k)).1

lemma isBigO_of_shift {E : Type*} [Norm E] (a : ℕ → E) (k : ℕ) (e : ℝ)
    (h : (fun m : ℕ => a (m + k)) =O[atTop] (fun m : ℕ => (m : ℝ) ^ e)) :
    a =O[atTop] (fun n : ℕ => (n : ℝ) ^ e) := by
  have hcomp := h.comp_tendsto (Filter.tendsto_sub_atTop_nat k)
  have hcomp' : (fun n : ℕ => a ((n - k) + k)) =O[atTop]
      (fun n : ℕ => ((n - k : ℕ) : ℝ) ^ e) := by
    simpa [Function.comp_apply] using hcomp
  have heq : a =ᶠ[atTop] (fun n : ℕ => a ((n - k) + k)) := by
    refine eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
    simp [Nat.sub_add_cancel hn]
  exact heq.trans_isBigO (hcomp'.trans (nat_sub_const_rpow_isBigO k e))

theorem coeff_norm_isBigO_atTop_of_delta_bound
    {R φ β M : ℝ} {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hR : 1 < R) (hφ0 : 0 < φ) (hφ2 : φ < Real.pi / 2)
    (hp : HasFPowerSeriesAt f p (0 : ℂ))
    (hΔ : AnalyticOnNhd ℂ f (DeltaDomainArg R φ))
    (hbound : ∀ z ∈ DeltaDomainArg R φ,
      ‖f z‖ ≤ M * ‖(1 : ℂ) - z‖ ^ (-β)) :
    (fun n : ℕ => ‖p.coeff n‖) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β - 1)) := by
  have hφπ : φ < Real.pi := by linarith [hφ2, Real.pi_pos]
  have hM0 : 0 ≤ M := by
    have hz0 : (0 : ℂ) ∈ DeltaDomainArg R φ :=
      zero_mem_deltaDomainArg (by linarith) hφπ
    have h0 := hbound 0 hz0
    have hleM : ‖f 0‖ ≤ M := by simpa using h0
    exact (norm_nonneg _).trans hleM
  obtain ⟨k, hkraw⟩ := exists_nat_gt (1 - β)
  have hβk : 1 < β + (k : ℝ) := by linarith
  let R' : ℝ := (1 + R) / 2
  have hR'1 : 1 < R' := by dsimp [R']; linarith
  have hRR' : R' < R := by dsimp [R']; linarith
  let φ' : ℝ := (φ + Real.pi / 2) / 2
  have hφ'0 : 0 < φ' := by dsimp [φ']; linarith [hφ0, Real.pi_pos]
  have hφlt : φ < φ' := by dsimp [φ']; linarith [hφ2]
  have hφ'2 : φ' < Real.pi / 2 := by dsimp [φ']; linarith [hφ2]
  have hsubset : DeltaDomainArg R' φ' ⊆ DeltaDomainArg R φ := by
    intro z hz
    exact ⟨lt_trans hz.1 hRR', hz.2.1, lt_trans hφlt hz.2.2⟩
  have hΔ' : AnalyticOnNhd ℂ f (DeltaDomainArg R' φ') := fun z hz => hΔ z (hsubset hz)
  have hp_iter : HasFPowerSeriesAt (iteratedDeriv k f)
      (scalarIteratedDerivSeries k p) (0 : ℂ) := hp.scalar_iteratedDeriv k
  have hΔ_iter : AnalyticOnNhd ℂ (iteratedDeriv k f) (DeltaDomainArg R' φ') := by
    simpa [iteratedDeriv_eq_iterate] using hΔ'.iterated_deriv k
  obtain ⟨M', hM'0, hderiv_bound⟩ :=
    exists_iteratedDeriv_norm_le_deltaDomain (R := R) (R' := R') (φ := φ) (φ' := φ')
      (β := β) (M := M) (f := f) k hR'1 hRR' hφ0 hφlt hφ'2 hΔ hM0 hbound
  have hderiv_bound' : ∀ z ∈ DeltaDomainArg R' φ',
      ‖iteratedDeriv k f z‖ ≤ M' * ‖(1 : ℂ) - z‖ ^ (-(β + (k : ℝ))) := by
    intro z hz
    have h := hderiv_bound z hz
    have hexp : -β - (k : ℝ) = -(β + (k : ℝ)) := by ring
    simpa [hexp] using h
  have hderivO : (fun m : ℕ => ‖(scalarIteratedDerivSeries k p).coeff m‖) =O[atTop]
      (fun m : ℕ => (m : ℝ) ^ (β + k - 1)) := by
    exact coeff_norm_isBigO_atTop_of_delta_bound_beta_gt_one
      (R := R') (φ := φ') (β := β + (k : ℝ)) (M := M')
      (f := iteratedDeriv k f) (p := scalarIteratedDerivSeries k p)
      hR'1 hφ'0 hφ'2 hp_iter hΔ_iter hM'0 hderiv_bound' hβk
  have htail := tail_isBigO_of_iterated_coeff_isBigO p k β hderivO
  exact isBigO_of_shift (fun n : ℕ => ‖p.coeff n‖) k (β - 1) htail

end
