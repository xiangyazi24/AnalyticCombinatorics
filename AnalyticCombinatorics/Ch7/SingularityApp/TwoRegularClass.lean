import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.TwoRegular
import AnalyticCombinatorics.Ch2.EGF.LabelledSetExp
import AnalyticCombinatorics.Ch5.Meromorphic.Alignments
import AnalyticCombinatorics.Ch4.Analytic.SubstComp

/-!
# Genuine labelled class of two-regular graphs

A two-regular labelled graph is a labelled `SET` of undirected cycles of
length at least three.  The cycle carried by one block is modelled as a full
cycle permutation on the block labels, modulo reversing the orientation.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace TwoRegularClass

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- Directed full cycles on `Fin n`, represented as permutations with cycle type `{n}`. -/
def FullCyclePerm (n : ℕ) : Type :=
  {σ : Equiv.Perm (Fin n) // σ.cycleType = {n}}

instance (n : ℕ) : Fintype (FullCyclePerm n) := by
  classical
  unfold FullCyclePerm
  infer_instance

instance (n : ℕ) : DecidableEq (FullCyclePerm n) := by
  classical
  infer_instance

/-- Reversing the orientation of a directed full cycle. -/
def fullCycleReverse {n : ℕ} (c : FullCyclePerm n) : FullCyclePerm n :=
  ⟨c.1⁻¹, by rw [Equiv.Perm.cycleType_inv, c.2]⟩

lemma fullCycleReverse_reverse {n : ℕ} (c : FullCyclePerm n) :
    fullCycleReverse (fullCycleReverse c) = c := by
  apply Subtype.ext
  simp [fullCycleReverse]

lemma fullCyclePerm_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (FullCyclePerm n) = (n - 1).factorial := by
  classical
  have hcycles := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin n) (n := n) hn (by simp)
  have hsub :
      Fintype.card (FullCyclePerm n) =
        ({g | g.cycleType = ({n} : Multiset ℕ)} :
          Finset (Equiv.Perm (Fin n))).card := by
    unfold FullCyclePerm
    exact Fintype.subtype_card
      ({g | g.cycleType = ({n} : Multiset ℕ)} : Finset (Equiv.Perm (Fin n)))
      (by intro g; simp)
  rw [hsub, hcycles]
  simp

lemma fullCyclePerm_orderOf {n : ℕ} (c : FullCyclePerm n) :
    orderOf c.1 = n := by
  rw [← Equiv.Perm.lcm_cycleType c.1, c.2]
  simp

lemma fullCycleReverse_ne_of_three_le {n : ℕ} (hn : 3 ≤ n) (c : FullCyclePerm n) :
    fullCycleReverse c ≠ c := by
  intro h
  have hinv : c.1⁻¹ = c.1 := congrArg Subtype.val h
  have hsq : c.1 ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← hinv]
    rw [mul_inv_cancel]
  have hdiv : n ∣ 2 := by
    rw [← fullCyclePerm_orderOf c]
    exact orderOf_dvd_of_pow_eq_one hsq
  exact not_le_of_gt (by omega : 2 < n) (Nat.le_of_dvd (by norm_num) hdiv)

instance fullCyclePermVAddBool (n : ℕ) : VAdd Bool (FullCyclePerm n) where
  vadd b c := if b then fullCycleReverse c else c

instance fullCyclePermAddActionBool (n : ℕ) : AddAction Bool (FullCyclePerm n) where
  zero_vadd c := by
    rfl
  add_vadd b₁ b₂ c := by
    cases b₁ <;> cases b₂
    · rfl
    · rfl
    · rfl
    · change c = fullCycleReverse (fullCycleReverse c)
      rw [fullCycleReverse_reverse]

/-- Undirected cycle structures on `Fin n`: full directed cycles modulo reversal. -/
abbrev UndirectedCycle (n : ℕ) : Type :=
  Quotient (AddAction.orbitRel Bool (FullCyclePerm n))

instance (n : ℕ) : Fintype (UndirectedCycle n) := by
  classical
  unfold UndirectedCycle
  infer_instance

lemma fixedBy_false_card (n : ℕ) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) false) =
      Fintype.card (FullCyclePerm n) := by
  classical
  change Fintype.card {c : FullCyclePerm n // false +ᵥ c = c} =
    Fintype.card (FullCyclePerm n)
  exact Fintype.card_congr
    { toFun := fun c => c.1
      invFun := fun c => ⟨c, rfl⟩
      left_inv := fun c => by cases c; rfl
      right_inv := fun c => rfl }

lemma fixedBy_true_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (AddAction.fixedBy (FullCyclePerm n) true) = 0 := by
  classical
  change Fintype.card {c : FullCyclePerm n // true +ᵥ c = c} = 0
  haveI : IsEmpty {c : FullCyclePerm n // true +ᵥ c = c} :=
    ⟨fun x => fullCycleReverse_ne_of_three_le hn x.1 (by simpa using x.2)⟩
  exact Fintype.card_eq_zero

lemma undirectedCycle_card_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (UndirectedCycle n) = (n - 1).factorial / 2 := by
  classical
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  exact Nat.eq_div_of_mul_eq_right (by norm_num : 2 ≠ 0)
    (by simpa [UndirectedCycle, mul_comm] using hburn.symm)

/-- One-block class of undirected cycles of length at least three. -/
def undirectedCycleClass : CombClass where
  Obj n := if 3 ≤ n then UndirectedCycle n else Fin 0
  finObj n := by
    classical
    by_cases h : 3 ≤ n
    · rw [if_pos h]
      infer_instance
    · rw [if_neg h]
      infer_instance

@[simp] lemma undirectedCycleClass_counts (n : ℕ) :
    undirectedCycleClass.counts n =
      if 3 ≤ n then (n - 1).factorial / 2 else 0 := by
  classical
  by_cases h : 3 ≤ n
  · simp [undirectedCycleClass, CombClass.counts, h, undirectedCycle_card_of_three_le h]
  · simp [undirectedCycleClass, CombClass.counts, h]

@[simp] lemma undirectedCycleClass_counts_zero :
    undirectedCycleClass.counts 0 = 0 := by
  simp

/-- The genuine labelled class of two-regular graphs: a labelled set of undirected cycles. -/
def twoRegularClass : CombClass :=
  undirectedCycleClass.set

/-- The genuine combinatorial count of two-regular labelled graphs. -/
def twoRegularClassCount (n : ℕ) : ℕ :=
  twoRegularClass.counts n

lemma undirectedCycleClass_coeff_egf_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf =
      (1 : ℚ) / (2 * n) := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_pos hn]
  have hn0 : n ≠ 0 := by omega
  have hfac : n.factorial = n * (n - 1).factorial := by
    cases n with
    | zero => contradiction
    | succ m =>
        simp [Nat.factorial_succ, Nat.mul_comm]
  have hcard := undirectedCycle_card_of_three_le hn
  have hburn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    Bool (FullCyclePerm n)
  rw [Fintype.sum_bool, fixedBy_false_card, fixedBy_true_card_of_three_le hn,
    fullCyclePerm_card (by omega : 2 ≤ n), Fintype.card_bool, zero_add] at hburn
  change (n - 1).factorial = Fintype.card (UndirectedCycle n) * 2 at hburn
  have hmul_nat : Fintype.card (UndirectedCycle n) * 2 = (n - 1).factorial := by
    exact hburn.symm
  have hhalf_mul_nat : ((n - 1).factorial / 2) * 2 = (n - 1).factorial := by
    rw [← hcard]
    exact hmul_nat
  have hmul_rat : (((n - 1).factorial / 2 : ℕ) : ℚ) * 2 =
      ((n - 1).factorial : ℚ) := by
    exact_mod_cast hhalf_mul_nat
  have hhalf_rat :
      (((n - 1).factorial / 2 : ℕ) : ℚ) =
        ((n - 1).factorial : ℚ) / 2 := by
    nlinarith
  rw [hfac]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hfnq : (((n - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have h2q : (2 : ℚ) ≠ 0 := by norm_num
  rw [hhalf_rat]
  field_simp [hnq, hfnq, h2q]
  norm_num [Nat.cast_mul]
  ring

lemma undirectedCycleClass_coeff_egf_of_lt_three {n : ℕ} (hn : n < 3) :
    PowerSeries.coeff (R := ℚ) n undirectedCycleClass.egf = 0 := by
  rw [CombClass.coeff_egf, undirectedCycleClass_counts, if_neg (by omega)]
  simp

/-- The core EGF is half the directed cycle EGF, with sizes one and two removed. -/
theorem undirectedCycleClass_egf :
    undirectedCycleClass.egf =
      (2⁻¹ : ℚ) • cycleEGFℚ -
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) -
          (4⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  ext n
  by_cases hn : 3 ≤ n
  · rw [undirectedCycleClass_coeff_egf_of_three_le hn]
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, coeff_cycleEGFℚ]
    have hn1 : n ≠ 1 := by omega
    have hn2 : n ≠ 2 := by omega
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, hn1, hn2]
    field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]
  · have hnlt : n < 3 := by omega
    rw [undirectedCycleClass_coeff_egf_of_lt_three hnlt]
    interval_cases n
    · simp [cycleEGFℚ_constantCoeff]
    · simp [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · norm_num [coeff_cycleEGFℚ, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

/-- Same EGF statement, expressed through the Ch2 labelled-cycle construction. -/
theorem undirectedCycleClass_egf_via_lcyc :
    undirectedCycleClass.egf =
      (2⁻¹ : ℚ) • CombClass.atom.lcyc.egf -
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) -
          (4⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  rw [undirectedCycleClass_egf, atom_lcyc_egf_eq_cycleEGFℚ]

/-- The EGF of the genuine two-regular class is the labelled `SET` exponential. -/
theorem twoRegularClass_egf :
    twoRegularClass.egf = (PowerSeries.exp ℚ).subst undirectedCycleClass.egf := by
  rw [twoRegularClass, CombClass.egf_set undirectedCycleClass undirectedCycleClass_counts_zero]

/-- Closed formal EGF using the labelled-cycle logarithm. -/
theorem twoRegularClass_egf_closed :
    twoRegularClass.egf =
      (PowerSeries.exp ℚ).subst
        ((2⁻¹ : ℚ) • cycleEGFℚ -
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) -
            (4⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
  rw [twoRegularClass_egf, undirectedCycleClass_egf]

/-! ### Complex analytic bridge to the singularity-analysis file -/

/-- The complex core EGF for one undirected cycle block. -/
def twoRegularCoreEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ undirectedCycleClass.egf

/-- The complex EGF of the genuine two-regular class. -/
def twoRegularClassEGFℂ : PowerSeries ℂ :=
  PowerSeries.mapℂ twoRegularClass.egf

/-- The closed complex core series. -/
def twoRegularCoreSeriesℂ : PowerSeries ℂ :=
  (2⁻¹ : ℂ) • cycleEGFℂ -
    (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) -
      (4⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

lemma twoRegularCoreEGFℂ_eq :
    twoRegularCoreEGFℂ = twoRegularCoreSeriesℂ := by
  unfold twoRegularCoreEGFℂ twoRegularCoreSeriesℂ
  rw [undirectedCycleClass_egf]
  ext n
  simp [PowerSeries.coeff_mapℂ, coeff_cycleEGFℚ, coeff_cycleEGFℂ]
  by_cases h1 : n = 1
  · subst n
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  · by_cases h2 : n = 2
    · subst n
      simp [PowerSeries.coeff_X]
    · simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, h1, h2]

lemma twoRegularCoreEGFℂ_constantCoeff :
    PowerSeries.constantCoeff twoRegularCoreEGFℂ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [twoRegularCoreEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]

lemma twoRegularClassEGFℂ_eq_complex_subst :
    twoRegularClassEGFℂ =
      (PowerSeries.exp ℂ).subst twoRegularCoreEGFℂ := by
  rw [twoRegularClassEGFℂ, twoRegularCoreEGFℂ, twoRegularClass_egf]
  have hsubst : PowerSeries.HasSubst undirectedCycleClass.egf := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
      undirectedCycleClass_counts_zero]
    simp
  change PowerSeries.map (algebraMap ℚ ℂ)
      ((PowerSeries.exp ℚ).subst undirectedCycleClass.egf) = _
  simpa [PowerSeries.mapℂ] using
    (PowerSeries.map_subst (a := undirectedCycleClass.egf)
      (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ))

lemma toFMLS_twoRegularCoreSeriesℂ :
    PowerSeries.toFMLS twoRegularCoreSeriesℂ =
      (2⁻¹ : ℂ) • PowerSeries.toFMLS cycleEGFℂ -
        (2⁻¹ : ℂ) • PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) -
          (4⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) := by
  ext n
  simp [twoRegularCoreSeriesℂ, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_sq_toFMLS_X_sq :
    HasFPowerSeriesAt (fun z : ℂ => z ^ 2)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n •
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)).coeff n
  have hsingle : HasSum term (term 2) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X_pow, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

/-- Analytic representative of the one-block EGF near zero. -/
def twoRegularCoreFun : ℂ → ℂ :=
  (2⁻¹ : ℂ) • cycleAnalyticFun -
    (2⁻¹ : ℂ) • (fun z : ℂ => z) -
      (4⁻¹ : ℂ) • (fun z : ℂ => z ^ 2)

lemma twoRegularCoreFun_zero : twoRegularCoreFun 0 = 0 := by
  simp [twoRegularCoreFun, cycleAnalyticFun_zero]

lemma twoRegularCoreFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt twoRegularCoreFun
      (PowerSeries.toFMLS twoRegularCoreEGFℂ) (0 : ℂ) := by
  have hcycle := cycleAnalyticFun_hasFPowerSeriesAt_zero.const_smul (c := (2⁻¹ : ℂ))
  have hid := hasFPowerSeriesAt_id_toFMLS_X.const_smul (c := (2⁻¹ : ℂ))
  have hsq := hasFPowerSeriesAt_sq_toFMLS_X_sq.const_smul (c := (4⁻¹ : ℂ))
  have h := (hcycle.sub hid).sub hsq
  rw [twoRegularCoreEGFℂ_eq, toFMLS_twoRegularCoreSeriesℂ]
  simpa [twoRegularCoreFun] using h

lemma exp_toFMLS_exp_eq_expSeries :
    PowerSeries.toFMLS (PowerSeries.exp ℂ) = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS]

lemma exp_hasFPowerSeriesAt_zero_toFMLS :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ)) (0 : ℂ) := by
  have hsum : HasFPowerSeriesAt (NormedSpace.expSeries ℂ ℂ).sum
      (NormedSpace.expSeries ℂ ℂ) (0 : ℂ) := by
    exact ((NormedSpace.expSeries ℂ ℂ).hasFPowerSeriesOnBall
      (by
        rw [NormedSpace.expSeries_radius_eq_top]
        exact WithTop.top_pos)).hasFPowerSeriesAt
  have hfun : (NormedSpace.expSeries ℂ ℂ).sum = Complex.exp := by
    funext z
    calc
      (NormedSpace.expSeries ℂ ℂ).sum z = NormedSpace.exp z := by
        exact congrFun (NormedSpace.exp_eq_expSeries_sum ℂ).symm z
      _ = Complex.exp z := by
        exact (congrFun Complex.exp_eq_exp_ℂ z).symm
  rw [exp_toFMLS_exp_eq_expSeries]
  rwa [hfun] at hsum

lemma twoRegularClassEGFℂ_hasFPowerSeriesAt_exp_core :
    HasFPowerSeriesAt (fun z : ℂ => Complex.exp (twoRegularCoreFun z))
      (PowerSeries.toFMLS twoRegularClassEGFℂ) (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp
      (PowerSeries.toFMLS (PowerSeries.exp ℂ)) (twoRegularCoreFun 0) := by
    simpa [twoRegularCoreFun_zero] using exp_hasFPowerSeriesAt_zero_toFMLS
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := twoRegularCoreFun) houter twoRegularCoreFun_hasFPowerSeriesAt_zero
  rw [twoRegularClassEGFℂ_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp twoRegularCoreEGFℂ_constantCoeff]
  simpa [Function.comp_def] using hcomp

lemma exp_twoRegularCoreFun_eq_twoRegularEGFFun_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.exp (twoRegularCoreFun z) = twoRegularEGFFun z := by
  have hz0 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
  have hcore :
      twoRegularCoreFun z =
        (-(z / 2) - z ^ 2 / 4) + Complex.log (1 - z) * (-(1 / 2 : ℂ)) := by
    simp [twoRegularCoreFun, cycleAnalyticFun]
    ring
  unfold twoRegularEGFFun twoRegularPrefactor
  rw [hcore, Complex.exp_add]
  congr 1
  rw [Complex.cpow_def, if_neg hz0]

theorem twoRegularClassEGFℂ_toFMLS_eq_twoRegularEGFSeriesℂ :
    PowerSeries.toFMLS twoRegularClassEGFℂ = twoRegularEGFSeriesℂ := by
  have heq :
      (fun z : ℂ => Complex.exp (twoRegularCoreFun z)) =ᶠ[𝓝 (0 : ℂ)] twoRegularEGFFun := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact exp_twoRegularCoreFun_eq_twoRegularEGFFun_of_norm_lt_one hz_norm
  exact HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    twoRegularClassEGFℂ_hasFPowerSeriesAt_exp_core
    twoRegularEGFFun_hasFPowerSeriesAt_zero heq

theorem twoRegularClass_counts_eq_twoRegularGraphCount (n : ℕ) :
    (twoRegularClass.counts n : ℝ) = twoRegularGraphCount n := by
  have hseries := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
    twoRegularClassEGFℂ_toFMLS_eq_twoRegularEGFSeriesℂ
  have hcoeffℂ :
      (((twoRegularClass.counts n : ℚ) / (n.factorial : ℚ) : ℚ) : ℂ) =
        twoRegularEGFSeriesℂ.coeff n := by
    simpa [twoRegularClassEGFℂ, PowerSeries.coeff_mapℂ, CombClass.coeff_egf]
      using hseries
  have hcoeffℝ :
      (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ) = twoRegularEGFCoeff n := by
    have hre := congrArg Complex.re hcoeffℂ
    simpa [twoRegularEGFCoeff] using hre
  rw [twoRegularGraphCount]
  rw [← hcoeffℝ]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

theorem twoRegularClass_counts_div_factorial_isEquivalent :
    (fun n : ℕ => (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => twoRegularAsymptoticConstant * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hbridge :
      (fun n : ℕ => (twoRegularClass.counts n : ℝ) / (n.factorial : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => twoRegularGraphCount n / (n.factorial : ℝ)) :=
    Eventually.of_forall fun n => by
      dsimp
      rw [twoRegularClass_counts_eq_twoRegularGraphCount n]
  exact hbridge.trans_isEquivalent twoRegularGraphCount_div_factorial_isEquivalent

end TwoRegularClass
