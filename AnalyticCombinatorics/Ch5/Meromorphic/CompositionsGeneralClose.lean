import Mathlib
import AnalyticCombinatorics.Ch4.Analytic.SubstComp
import AnalyticCombinatorics.Ch5.Meromorphic.CompositionsGeneral
import AnalyticCombinatorics.Ch5.Meromorphic.FibonacciCompositions
import AnalyticCombinatorics.Ch5.Meromorphic.Transfer

/-!
# Closing the general finite-part composition family

This file supplies the formal OGF bridge, the derivative nonvanishing input, and the
dominant-pole decomposition needed by `CompositionsGeneral`.
-/

open Complex Filter Asymptotics
open scoped BigOperators ComplexOrder ENNReal NNReal PowerSeries Topology

noncomputable section

namespace AnalyticCombinatorics
namespace Ch5
namespace Meromorphic
namespace CompositionsGeneral
namespace Close

/-- The finite part series `∑_{s∈S} X^s`. -/
def partSeriesℂ (S : Finset ℕ) : PowerSeries ℂ :=
  ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s

lemma partSeriesℂ_eq (S : Finset ℕ) :
    partSeriesℂ S = ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s := rfl

lemma compS_succ_eq_sum_filter (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    compS S h0 (n + 1) =
      ∑ s ∈ S.filter (fun s => s ≤ n + 1), compS S h0 (n + 1 - s) := by
  classical
  rw [compS_succ_eq_sum_subtype S h0 n]
  let e :
      {s : ℕ // s ∈ S ∧ s ≤ n + 1} ≃
        {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)} := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro s
      exact (⟨s.1, Finset.mem_filter.mpr ⟨s.2.1, s.2.2⟩⟩ :
        {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)})
    · intro s
      exact (⟨s.1, Finset.mem_filter.mp s.2⟩ :
        {s : ℕ // s ∈ S ∧ s ≤ n + 1})
    · intro s
      ext
      rfl
    · intro s
      ext
      rfl
  calc
    (∑ s : {s : ℕ // s ∈ S ∧ s ≤ n + 1}, compS S h0 (n + 1 - s.1)) =
        ∑ s : {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)},
          compS S h0 (n + 1 - s.1) := by
      exact Fintype.sum_equiv e
        (fun s : {s : ℕ // s ∈ S ∧ s ≤ n + 1} => compS S h0 (n + 1 - s.1))
        (fun s : {s : ℕ // s ∈ S.filter (fun s => s ≤ n + 1)} =>
          compS S h0 (n + 1 - s.1))
        (by intro s; rfl)
    _ = ∑ s ∈ S.filter (fun s => s ≤ n + 1), compS S h0 (n + 1 - s) := by
      simpa using
        (Finset.sum_attach (S.filter (fun s => s ≤ n + 1))
          (fun s : ℕ => compS S h0 (n + 1 - s)))

lemma coeff_compSeriesℂ_mul_partSeriesℂ
    (S : Finset ℕ) (h0 : 0 ∉ S) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n (compSeriesℂ S h0 * partSeriesℂ S) =
      ∑ s ∈ S.filter (fun s => s ≤ n), (compS S h0 (n - s) : ℂ) := by
  classical
  rw [partSeriesℂ, Finset.mul_sum]
  simp only [map_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsn : s ≤ n
  · simp [hsn, PowerSeries.coeff_mul_X_pow', coeff_compSeriesℂ]
  · simp [hsn, PowerSeries.coeff_mul_X_pow']

lemma constantCoeff_compSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff (compSeriesℂ S h0) = 1 := by
  rw [compSeriesℂ, PowerSeries.constantCoeff_mk]
  exact_mod_cast compS_zero S h0

lemma coeff_zero_partSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.coeff (R := ℂ) 0 (partSeriesℂ S) = 0 := by
  classical
  simp [partSeriesℂ, PowerSeries.coeff_X_pow, h0]

lemma constantCoeff_partSeriesℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff (partSeriesℂ S) = 0 := by
  simpa [PowerSeries.constantCoeff] using coeff_zero_partSeriesℂ S h0

/-- Formal OGF identity for genuine `S`-composition counts. -/
theorem compSeriesℂ_mul_denominator (S : Finset ℕ) (h0 : 0 ∉ S) :
    compSeriesℂ S h0 *
      (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s) = 1 := by
  classical
  rw [← partSeriesℂ_eq S]
  have hsplit :
      compSeriesℂ S h0 * (1 - partSeriesℂ S) =
        compSeriesℂ S h0 - compSeriesℂ S h0 * partSeriesℂ S := by
    ring
  rw [hsplit]
  ext n
  cases n with
  | zero =>
      simpa [constantCoeff_compSeriesℂ S h0] using constantCoeff_partSeriesℂ S h0
  | succ n =>
      simp only [map_sub, coeff_compSeriesℂ, coeff_compSeriesℂ_mul_partSeriesℂ,
        PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte]
      have hrecℕ := compS_succ_eq_sum_filter S h0 n
      have hrecℂ :
          (compS S h0 (n + 1) : ℂ) =
            ∑ s ∈ S.filter (fun s => s ≤ n + 1), (compS S h0 (n + 1 - s) : ℂ) := by
        exact_mod_cast hrecℕ
      exact sub_eq_zero.mpr hrecℂ

lemma denominator_constantCoeff_ne_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    PowerSeries.constantCoeff
      (1 - ∑ s ∈ S, (PowerSeries.X : PowerSeries ℂ) ^ s : PowerSeries ℂ) ≠ 0 := by
  rw [← partSeriesℂ_eq S]
  simp [constantCoeff_partSeriesℂ S h0]

/-- The genuine count series is the rational OGF. -/
theorem compSeriesℂ_eq_compOGFℂ (S : Finset ℕ) (h0 : 0 ∉ S) :
    compSeriesℂ S h0 = compOGFℂ S := by
  rw [compOGFℂ]
  exact (PowerSeries.eq_inv_iff_mul_eq_one (denominator_constantCoeff_ne_zero S h0)).2
    (compSeriesℂ_mul_denominator S h0)

lemma compOGFℂ_eq_geometric_subst (S : Finset ℕ) (h0 : 0 ∉ S) :
    compOGFℂ S = (PowerSeries.invUnitsSub (1 : ℂˣ)).subst (partSeriesℂ S) := by
  let H : PowerSeries ℂ := partSeriesℂ S
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    simpa [H] using constantCoeff_partSeriesℂ S h0
  have hHas : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
  have hsubst : (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H * (1 - H) = 1 := by
    have hsubHX :
        (PowerSeries.C ((1 : ℂˣ) : ℂ) - PowerSeries.X).subst H = 1 - H := by
      rw [PowerSeries.subst_sub hHas, PowerSeries.subst_C, PowerSeries.subst_X hHas]
      simp
    rw [← hsubHX, ← PowerSeries.subst_mul hHas, PowerSeries.invUnitsSub_mul_sub]
    change (PowerSeries.C (1 : ℂ)).subst H = 1
    rw [PowerSeries.subst_C]
    simp
  rw [compOGFℂ]
  rw [← partSeriesℂ_eq S]
  change (1 - H)⁻¹ = (PowerSeries.invUnitsSub (1 : ℂˣ)).subst H
  have h0 : PowerSeries.constantCoeff (1 - H : PowerSeries ℂ) ≠ 0 := by
    simp [H, constantCoeff_partSeriesℂ S h0]
  exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).2 hsubst).symm

lemma toFMLS_invUnitsSub_one :
    PowerSeries.toFMLS (PowerSeries.invUnitsSub (1 : ℂˣ)) =
      formalMultilinearSeries_geometric ℂ ℂ := by
  ext n
  simp [PowerSeries.toFMLS, formalMultilinearSeries_geometric_eq_ofScalars,
    FormalMultilinearSeries.ofScalars]

lemma toFMLS_add (f g : PowerSeries ℂ) :
    PowerSeries.toFMLS (f + g) = PowerSeries.toFMLS f + PowerSeries.toFMLS g := by
  change FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff (R := ℂ) n (f + g)) =
    FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n f) +
      FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff (R := ℂ) n g)
  rw [← FormalMultilinearSeries.ofScalars_add]
  congr

lemma toFMLS_finset_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ) :
    PowerSeries.toFMLS (∑ i ∈ s, F i) =
      ∑ i ∈ s, PowerSeries.toFMLS (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change FormalMultilinearSeries.ofScalars ℂ (fun n => (0 : ℂ)) = 0
      exact FormalMultilinearSeries.ofScalars_series_eq_zero_of_scalar_zero ℂ ℂ
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, toFMLS_add, ih]

lemma hasFPowerSeriesAt_pow_toFMLS_X_pow (s : ℕ) :
    HasFPowerSeriesAt (fun z : ℂ => z ^ s)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n •
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)).coeff n
  have hsingle : HasSum term (term s) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X_pow, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma partPoly_hasFPowerSeriesAt_zero (S : Finset ℕ) :
    HasFPowerSeriesAt (partPoly ℂ S)
      (PowerSeries.toFMLS (partSeriesℂ S)) (0 : ℂ) := by
  classical
  have hsum :
      HasFPowerSeriesAt (fun z : ℂ => ∑ s ∈ S, z ^ s)
        (∑ s ∈ S, PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) (0 : ℂ) := by
    induction S using Finset.induction_on with
    | empty =>
        simpa using
          (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
            (c := (0 : ℂ)) (e := (0 : ℂ)))
    | insert a S ha ih =>
        simpa [Finset.sum_insert ha] using
          (hasFPowerSeriesAt_pow_toFMLS_X_pow a).add ih
  have hFMLS :
      (∑ s ∈ S, PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ s)) =
        PowerSeries.toFMLS (partSeriesℂ S) := by
    rw [partSeriesℂ]
    exact (toFMLS_finset_sum S
      (fun s : ℕ => (PowerSeries.X : PowerSeries ℂ) ^ s)).symm
  simpa [partPoly, hFMLS]
    using hsum

theorem compSeriesℂ_hasFPowerSeriesAt_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    HasFPowerSeriesAt (fun z : ℂ => (1 - partPoly ℂ S z)⁻¹)
      (PowerSeries.toFMLS (compSeriesℂ S h0)) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (0 : ℂ) :=
    (hasFPowerSeriesOnBall_inv_one_sub ℂ ℂ).hasFPowerSeriesAt
  have houter' : HasFPowerSeriesAt (fun z : ℂ => (1 - z)⁻¹)
      (formalMultilinearSeries_geometric ℂ ℂ) (partPoly ℂ S 0) := by
    simpa [partPoly_zero_of_notMem_zero (R := ℂ) S h0] using houter
  have hcomp := houter'.comp (partPoly_hasFPowerSeriesAt_zero S)
  rw [compSeriesℂ_eq_compOGFℂ S h0, compOGFℂ_eq_geometric_subst S h0]
  rw [PowerSeries.toFMLS_subst_eq_comp (constantCoeff_partSeriesℂ S h0)]
  rw [toFMLS_invUnitsSub_one]
  exact hcomp

lemma partPoly_hasDerivAt (S : Finset ℕ) (ρ : ℂ) :
    HasDerivAt (partPoly ℂ S) (partPolyDerivAt S ρ) ρ := by
  classical
  change HasDerivAt (fun z : ℂ => ∑ s ∈ S, z ^ s)
    (∑ s ∈ S, (s : ℂ) * ρ ^ (s - 1)) ρ
  have h := HasDerivAt.sum (u := S)
    (fun s _hs => hasDerivAt_pow s ρ)
  convert h using 1
  funext z
  simp

lemma partPoly_analyticAt (S : Finset ℕ) (z : ℂ) :
    AnalyticAt ℂ (partPoly ℂ S) z := by
  classical
  unfold partPoly
  fun_prop

lemma partPoly_rhoSℂ (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPoly ℂ S (rhoSℂ S hcard h0) = 1 := by
  rw [rhoSℂ, partPoly_complex_ofReal, partPoly_rhoS hcard h0]
  norm_num

theorem partPolyDerivAt_rhoSℂ_ne_zero
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S) :
    partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0 := by
  classical
  let ρ : ℝ := rhoS S hcard h0
  have hρpos : 0 < ρ := rhoS_pos hcard h0
  have hSnonempty : S.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2) hcard)
  have hterm_pos :
      ∀ s ∈ S, 0 < (s : ℝ) * ρ ^ (s - 1) := by
    intro s hs
    have hsposNat : 0 < s := Nat.pos_of_ne_zero fun hs0 => h0 (by simpa [hs0] using hs)
    have hspos : 0 < (s : ℝ) := by exact_mod_cast hsposNat
    exact mul_pos hspos (pow_pos hρpos (s - 1))
  have hsum_pos : 0 < ∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1) :=
    Finset.sum_pos hterm_pos hSnonempty
  have hsum_ne : (∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1)) ≠ 0 :=
    ne_of_gt hsum_pos
  have hcast :
      partPolyDerivAt S (rhoSℂ S hcard h0) =
        ((∑ s ∈ S, (s : ℝ) * ρ ^ (s - 1)) : ℂ) := by
    simp [partPolyDerivAt, rhoSℂ, ρ]
  rw [hcast]
  exact_mod_cast hsum_ne

/-- The denominator polynomial `1 - P_S(X)`. -/
def denominatorPolynomial (S : Finset ℕ) : Polynomial ℂ :=
  1 - ∑ s ∈ S, Polynomial.X ^ s

lemma eval_denominatorPolynomial (S : Finset ℕ) (z : ℂ) :
    Polynomial.eval z (denominatorPolynomial S) = 1 - partPoly ℂ S z := by
  simp [denominatorPolynomial, partPoly, Polynomial.eval_finset_sum]

lemma denominatorPolynomial_ne_zero (S : Finset ℕ) (h0 : 0 ∉ S) :
    denominatorPolynomial S ≠ 0 := by
  intro h
  have heval := congrArg (fun p : Polynomial ℂ => Polynomial.eval 0 p) h
  have hleft : Polynomial.eval 0 (denominatorPolynomial S) = 1 := by
    rw [eval_denominatorPolynomial]
    simp [partPoly_zero_of_notMem_zero (R := ℂ) S h0]
  simp at heval
  rw [hleft] at heval
  exact one_ne_zero heval

lemma denominatorPolynomial_isRoot_iff (S : Finset ℕ) (z : ℂ) :
    Polynomial.IsRoot (denominatorPolynomial S) z ↔
      1 - partPoly ℂ S z = 0 := by
  simp [Polynomial.IsRoot, eval_denominatorPolynomial]

lemma roots_erase_rho_norm_gt
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    ∀ z ∈ (denominatorPolynomial S).roots.toFinset.erase (rhoSℂ S hcard h0),
      rhoS S hcard h0 < ‖z‖ := by
  classical
  intro z hz
  have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset :=
    (Finset.mem_erase.mp hz).2
  have hz_ne_rho : z ≠ rhoSℂ S hcard h0 :=
    (Finset.mem_erase.mp hz).1
  have hroot :
      1 - partPoly ℂ S z = 0 := by
    have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
    have hIsRoot : Polynomial.IsRoot (denominatorPolynomial S) z :=
      (Polynomial.mem_roots hp).mp (Multiset.mem_toFinset.mp hzroots)
    exact (denominatorPolynomial_isRoot_iff S z).mp hIsRoot
  by_contra hnot
  have hzle : ‖z‖ ≤ rhoS S hcard h0 := le_of_not_gt hnot
  have hzrho :
      z = rhoSℂ S hcard h0 := by
    simpa [rhoSℂ] using root_eq_rhoS_of_gcd hcard h0 hgcd hroot hzle
  exact hz_ne_rho hzrho

theorem exists_dominant_annulus
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    ∃ R T : ℝ,
      ‖rhoSℂ S hcard h0‖ < R ∧ R < T ∧
        ∀ z ∈ Metric.closedBall (0 : ℂ) T,
          z ≠ rhoSℂ S hcard h0 → 1 - partPoly ℂ S z ≠ 0 := by
  classical
  let ρℂ : ℂ := rhoSℂ S hcard h0
  let ρ : ℝ := rhoS S hcard h0
  let badRoots : Finset ℂ := (denominatorPolynomial S).roots.toFinset.erase ρℂ
  have hρnorm : ‖ρℂ‖ = ρ := by
    change ‖rhoSℂ S hcard h0‖ = ρ
    rw [rhoSℂ]
    exact Complex.norm_of_nonneg (rhoS_pos hcard h0).le
  have hbad_gt : ∀ z ∈ badRoots, ρ < ‖z‖ := by
    intro z hz
    simpa [badRoots, ρ] using roots_erase_rho_norm_gt S hcard h0 hgcd z hz
  by_cases hbad_empty : badRoots = ∅
  · refine ⟨ρ + 2⁻¹, ρ + 1, ?_, ?_, ?_⟩
    · rw [hρnorm]
      linarith
    · linarith
    · intro z _hz hz_ne hroot
      have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
      have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset := by
        exact Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hp).mpr ((denominatorPolynomial_isRoot_iff S z).mpr hroot))
      have hzbad : z ∈ badRoots := by
        exact Finset.mem_erase.mpr ⟨hz_ne, hzroots⟩
      simp [hbad_empty] at hzbad
  · have hbad_nonempty : badRoots.Nonempty := Finset.nonempty_iff_ne_empty.mpr hbad_empty
    let badNorms : Finset ℝ := badRoots.image fun z => ‖z‖
    have hbadNorms_nonempty : badNorms.Nonempty := by
      rcases hbad_nonempty with ⟨z, hz⟩
      exact ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let m : ℝ := badNorms.min' hbadNorms_nonempty
    have hρm : ρ < m := by
      dsimp [m]
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      exact hbad_gt z hz
    rcases exists_between hρm with ⟨T, hρT, hTm⟩
    rcases exists_between hρT with ⟨R, hρR, hRT⟩
    refine ⟨R, T, ?_, hRT, ?_⟩
    · rw [hρnorm]
      exact hρR
    · intro z hzclosed hz_ne hroot
      have hp : denominatorPolynomial S ≠ 0 := denominatorPolynomial_ne_zero S h0
      have hzroots : z ∈ (denominatorPolynomial S).roots.toFinset := by
        exact Multiset.mem_toFinset.mpr
          ((Polynomial.mem_roots hp).mpr ((denominatorPolynomial_isRoot_iff S z).mpr hroot))
      have hzbad : z ∈ badRoots := Finset.mem_erase.mpr ⟨hz_ne, hzroots⟩
      have hzNormMem : ‖z‖ ∈ badNorms := Finset.mem_image.mpr ⟨z, hzbad, rfl⟩
      have hm_le_z : m ≤ ‖z‖ := by
        exact Finset.min'_le badNorms ‖z‖ hzNormMem
      have hz_le_T : ‖z‖ ≤ T := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosed
      linarith

theorem compS_isEquivalent
    (S : Finset ℕ) (hcard : 2 ≤ S.card) (h0 : 0 ∉ S)
    (hgcd : S.gcd id = 1) :
    (fun n : ℕ => (compS S h0 n : ℂ)) ~[atTop]
      (fun n : ℕ =>
        compAsymptoticConstant S hcard h0 * (rhoSℂ S hcard h0)⁻¹ ^ n) := by
  classical
  rcases exists_dominant_annulus S hcard h0 hgcd with
    ⟨R, T, hρR, hRT, hden⟩
  have hρpos : 0 < ‖rhoSℂ S hcard h0‖ := by
    rw [rhoSℂ]
    rw [Complex.norm_of_nonneg (rhoS_pos hcard h0).le]
    exact rhoS_pos hcard h0
  have hCρ : partPoly ℂ S (rhoSℂ S hcard h0) = 1 :=
    partPoly_rhoSℂ S hcard h0
  have hCan : ∀ z ∈ Metric.closedBall (0 : ℂ) T, AnalyticAt ℂ (partPoly ℂ S) z :=
    fun z _hz => partPoly_analyticAt S z
  have hderiv : HasDerivAt (partPoly ℂ S)
      (partPolyDerivAt S (rhoSℂ S hcard h0)) (rhoSℂ S hcard h0) :=
    partPoly_hasDerivAt S (rhoSℂ S hcard h0)
  have hderiv_ne : partPolyDerivAt S (rhoSℂ S hcard h0) ≠ 0 :=
    partPolyDerivAt_rhoSℂ_ne_zero S hcard h0
  have hF :
      HasFPowerSeriesAt (fun z : ℂ => (1 - partPoly ℂ S z)⁻¹)
        (PowerSeries.toFMLS (compSeriesℂ S h0)) (0 : ℂ) :=
    compSeriesℂ_hasFPowerSeriesAt_zero S h0
  rcases SupercriticalSeqGenuine.supercriticalSeq_decomposition_from_supercritical_data
      (F := compSeriesℂ S h0) (Cfun := partPoly ℂ S)
      (ρ := rhoSℂ S hcard h0)
      (Cderiv := partPolyDerivAt S (rhoSℂ S hcard h0))
      (R := R) (S := T)
      hρpos hρR hRT hCρ hCan hderiv hderiv_ne hden hF with
    ⟨g, _hg_has, hgR, hdecomp⟩
  exact compS_isEquivalent_of_dominant_decomposition
    S hcard h0 g hρR hderiv_ne hgR
    (by simpa [residueConstant] using hdecomp)

end Close
end CompositionsGeneral
end Meromorphic
end Ch5
end AnalyticCombinatorics
