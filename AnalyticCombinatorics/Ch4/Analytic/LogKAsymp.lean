import AnalyticCombinatorics.Ch4.Analytic.LogKCoeff
import AnalyticCombinatorics.Ch4.Analytic.LogSqSingularity
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# General log^k singularity scale: asymptotic layer

This file builds on `LogKCoeff.lean`.

It proves the real elementary-symmetric bracket asymptotic

  `k! · e_k((α+j)⁻¹, j<n) ~ (log n)^k`

and the resulting coefficient scale

  `k! · choose(α+n-1,n) · e_k ~ n^(α-1)/Γ(α) · (log n)^k`.
-/

open Filter Asymptotics
open scoped BigOperators Topology PowerSeries

noncomputable section

namespace AnalyticCombinatorics

/-- Shifted power sums:
`p_r(n) = ∑_{j<n} ((α+j)⁻¹)^r`. -/
def shiftedPowerSum (α : ℝ) (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ((α + (j : ℝ))⁻¹) ^ r

/-- Elementary symmetric function in `{(α+j)⁻¹ | j < n}`. -/
def shiftedElemSymm (α : ℝ) (k n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range n).powersetCard k,
    ∏ j ∈ s, (α + (j : ℝ))⁻¹

/-- The normalized logarithmic bracket `k! · e_k`. -/
def logKBracket (α : ℝ) (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * shiftedElemSymm α k n

/-- Full real coefficient scale for `(1-z)^(-α)·(-log(1-z))^k`. -/
def logKSingularityScale (α : ℝ) (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * Ring.choose (α + n - 1) n * shiftedElemSymm α k n

@[simp] theorem shiftedElemSymm_zero (α : ℝ) (n : ℕ) :
    shiftedElemSymm α 0 n = 1 := by
  simp [shiftedElemSymm]

/-- Cast real elementary symmetric functions to the complex version from `LogKCoeff`. -/
theorem shiftedElemSymm_cast (α : ℝ) (k n : ℕ) :
    ((shiftedElemSymm α k n : ℝ) : ℂ)
      = shiftedElemSymmℂ (α : ℂ) k n := by
  classical
  rw [shiftedElemSymm, shiftedElemSymmℂ, Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]

@[simp] theorem shiftedElemSymm_succ_zero (α : ℝ) (k : ℕ) :
    shiftedElemSymm α (k + 1) 0 = 0 := by
  rw [shiftedElemSymm, Finset.range_zero,
    Finset.powersetCard_eq_empty.mpr (by simp), Finset.sum_empty]

theorem shiftedElemSymm_succ_n (α : ℝ) (k n : ℕ) :
    shiftedElemSymm α (k + 1) (n + 1)
      =
    shiftedElemSymm α (k + 1) n
      + (α + (n : ℝ))⁻¹ * shiftedElemSymm α k n := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, Complex.ofReal_mul,
    shiftedElemSymm_cast, shiftedElemSymm_cast, shiftedElemSymm_cast]
  rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast]
  exact shiftedElemSymmℂ_succ_n (α : ℂ) k n

theorem shiftedPowerSum_succ_n (α : ℝ) (r n : ℕ) :
    shiftedPowerSum α r (n + 1)
      =
    shiftedPowerSum α r n + ((α + (n : ℝ))⁻¹) ^ r := by
  rw [shiftedPowerSum, shiftedPowerSum, Finset.sum_range_succ]

private theorem shiftedPowerSum_one_eq_shiftedHarmonic (α : ℝ) :
    (fun n : ℕ => shiftedPowerSum α 1 n)
      = fun n : ℕ => shiftedHarmonic α n := by
  funext n
  simp [shiftedPowerSum, shiftedHarmonic]

/-- A finite sum of little-o terms is little-o. -/
private theorem isLittleO_finset_sum
    {ι : Type*} {s : Finset ι}
    {f : ι → ℕ → ℝ} {g : ℕ → ℝ}
    (h : ∀ i ∈ s, (f i) =o[atTop] g) :
    (fun n : ℕ => ∑ i ∈ s, f i n) =o[atTop] g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (isLittleO_zero (α := ℕ) (β := ℝ) (γ := ℝ) atTop g)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (by simp)).add
        (ih (fun i hi => h i (by simp [hi])))

theorem log_pow_isLittleO_log_pow {a b : ℕ} (hab : a < b) :
    (fun n : ℕ => (Real.log n) ^ a)
      =o[atTop]
    (fun n : ℕ => (Real.log n) ^ b) := by
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbsub : 0 < b - a := by omega
  have hzero :
      ∀ᶠ n : ℕ in atTop,
        (Real.log n) ^ b = 0 → (Real.log n) ^ a = 0 := by
    filter_upwards [hlog_atTop.eventually_gt_atTop 0] with n hn hb0
    exact False.elim ((pow_ne_zero b hn.ne') hb0)
  rw [Asymptotics.isLittleO_iff_tendsto' hzero]
  have hratio :
      (fun n : ℕ => (Real.log n) ^ a / (Real.log n) ^ b)
        =ᶠ[atTop]
      (fun n : ℕ => ((Real.log n) ^ (b - a))⁻¹) := by
    filter_upwards [hlog_atTop.eventually_gt_atTop 0] with n hn
    have hne : Real.log n ≠ 0 := hn.ne'
    have hba : a ≤ b := le_of_lt hab
    conv_lhs => rw [show b = (b - a) + a from (Nat.sub_add_cancel hba).symm, pow_add]
    rw [mul_comm, ← div_div, div_self (pow_ne_zero a hne), one_div]
  rw [tendsto_congr' hratio]
  have hpow_atTop :
      Tendsto (fun n : ℕ => (Real.log n) ^ (b - a)) atTop atTop :=
    (tendsto_pow_atTop hbsub.ne').comp hlog_atTop
  exact tendsto_inv_atTop_zero.comp hpow_atTop

theorem shiftedPowerSum_isBigO_log
    {α : ℝ} (hα : 0 < α) {r : ℕ} (hr : 1 ≤ r) :
    (fun n : ℕ => shiftedPowerSum α r n)
      =O[atTop] (fun n : ℕ => Real.log n) := by
  have hbound :
      (fun n : ℕ => shiftedPowerSum α r n)
        =O[atTop] (fun n : ℕ => shiftedHarmonic α n) := by
    refine IsBigO.of_bound ((α⁻¹) ^ (r - 1)) (Eventually.of_forall fun n => ?_)
    have hcoef_nonneg : 0 ≤ (α⁻¹) ^ (r - 1) := by positivity
    have hsum_nonneg : 0 ≤ shiftedPowerSum α r n := by
      rw [shiftedPowerSum]
      exact Finset.sum_nonneg fun j _ => by positivity
    have hH_nonneg : 0 ≤ shiftedHarmonic α n := by
      rw [shiftedHarmonic]
      exact Finset.sum_nonneg fun j _ => by positivity
    rw [Real.norm_of_nonneg hsum_nonneg, Real.norm_of_nonneg hH_nonneg]
    rw [shiftedPowerSum, shiftedHarmonic, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hj_nonneg : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
    have hpos : 0 < α + (j : ℝ) := by linarith
    have hbase_nonneg : 0 ≤ (α + (j : ℝ))⁻¹ :=
      inv_nonneg.mpr hpos.le
    have hleα : (α + (j : ℝ))⁻¹ ≤ α⁻¹ := by
      exact inv_anti₀ hα (by linarith)
    rcases Nat.exists_eq_add_of_le hr with ⟨r', rfl⟩
    have hidx : 1 + r' - 1 = r' := by omega
    rw [hidx, add_comm 1 r', pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbase_nonneg hleα r') hbase_nonneg
  exact hbound.trans (shiftedHarmonic_isEquivalent_log hα).isBigO

/-! ## Newton identity -/

private theorem alternating_newton_cancel
    (x : ℝ) (E : ℕ → ℝ) (K : ℕ) :
    (∑ r ∈ Finset.range (K + 1), ((-1 : ℝ) ^ r * x ^ (r + 1) * E (K - r)))
      +
      (∑ r ∈ Finset.range K, ((-1 : ℝ) ^ r * x ^ (r + 2) * E (K - 1 - r)))
      =
    x * E K := by
  have hcancel :
      (∑ r ∈ Finset.range K,
          ((-1 : ℝ) ^ (r + 1) * x ^ (r + 1 + 1) * E (K - (r + 1))))
        + (∑ r ∈ Finset.range K,
          ((-1 : ℝ) ^ r * x ^ (r + 2) * E (K - 1 - r)))
        = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro r hr
    have hidx : K - (r + 1) = K - 1 - r := by omega
    rw [hidx, pow_succ]
    ring
  have h0 : (-1 : ℝ) ^ 0 * x ^ (0 + 1) * E (K - 0) = x * E K := by simp
  rw [Finset.sum_range_succ', add_right_comm, hcancel, zero_add, h0]



/-- `e_1 = p_1` (first elementary symmetric = first power sum). -/
theorem shiftedElemSymm_one (α : ℝ) (m : ℕ) :
    shiftedElemSymm α 1 m = shiftedPowerSum α 1 m := by
  rw [shiftedElemSymm, shiftedPowerSum, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- Newton identity for the shifted elementary symmetric functions. -/
theorem shiftedElemSymm_newton (α : ℝ) (k n : ℕ) :
    (((k + 1 : ℕ) : ℝ)) * shiftedElemSymm α (k + 1) n
      =
    ∑ r ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ r
        * shiftedPowerSum α (r + 1) n
        * shiftedElemSymm α (k - r) n) := by
  classical
  revert k
  induction n with
  | zero =>
      intro k
      rw [shiftedElemSymm_succ_zero]
      simp [shiftedPowerSum]
  | succ n ih =>
      intro k
      cases k with
      | zero =>
          simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, Nat.sub_zero,
            shiftedElemSymm_zero, mul_one, Nat.cast_one]
          exact shiftedElemSymm_one α (n + 1)
      | succ k =>
          let x : ℝ := (α + (n : ℝ))⁻¹
          let T : ℕ → ℝ :=
            fun r =>
              (-1 : ℝ) ^ r
                * shiftedPowerSum α (r + 1) (n + 1)
                * shiftedElemSymm α (k + 1 - r) (n + 1)
          let A : ℕ → ℝ :=
            fun r =>
              (-1 : ℝ) ^ r
                * shiftedPowerSum α (r + 1) n
                * shiftedElemSymm α (k + 1 - r) n
          let B : ℕ → ℝ :=
            fun r =>
              (-1 : ℝ) ^ r
                * shiftedPowerSum α (r + 1) n
                * shiftedElemSymm α (k - r) n
          let C : ℕ → ℝ :=
            fun r =>
              (-1 : ℝ) ^ r
                * x ^ (r + 1)
                * shiftedElemSymm α (k + 1 - r) n
          let D : ℕ → ℝ :=
            fun r =>
              (-1 : ℝ) ^ r
                * x ^ (r + 2)
                * shiftedElemSymm α (k - r) n
          have hE :
              shiftedElemSymm α (k + 2) (n + 1)
                =
              shiftedElemSymm α (k + 2) n + x * shiftedElemSymm α (k + 1) n := by
            simpa [x] using shiftedElemSymm_succ_n α (k + 1) n
          have hsplitT :
              (∑ r ∈ Finset.range (k + 2), T r)
                =
              (∑ r ∈ Finset.range (k + 1), T r) + T (k + 1) := by
            change (∑ r ∈ Finset.range ((k + 1) + 1), T r)
                =
              (∑ r ∈ Finset.range (k + 1), T r) + T (k + 1)
            rw [Finset.sum_range_succ]
          have hsplitA :
              (∑ r ∈ Finset.range (k + 2), A r)
                =
              (∑ r ∈ Finset.range (k + 1), A r) + A (k + 1) := by
            change (∑ r ∈ Finset.range ((k + 1) + 1), A r)
                =
              (∑ r ∈ Finset.range (k + 1), A r) + A (k + 1)
            rw [Finset.sum_range_succ]
          have hsplitC :
              (∑ r ∈ Finset.range (k + 2), C r)
                =
              (∑ r ∈ Finset.range (k + 1), C r) + C (k + 1) := by
            change (∑ r ∈ Finset.range ((k + 1) + 1), C r)
                =
              (∑ r ∈ Finset.range (k + 1), C r) + C (k + 1)
            rw [Finset.sum_range_succ]
          have hprefix :
              (∑ r ∈ Finset.range (k + 1), T r)
                =
              ∑ r ∈ Finset.range (k + 1),
                (A r + x * B r + C r + D r) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [Finset.mem_range] at hr
            dsimp [T, A, B, C, D]
            have hidx : k + 1 - r = (k - r) + 1 := by omega
            rw [hidx, shiftedElemSymm_succ_n, shiftedPowerSum_succ_n]
            dsimp [x]
            have hxpow : ((α + (n : ℝ))⁻¹) ^ (r + 2)
                = ((α + (n : ℝ))⁻¹) ^ (r + 1) * ((α + (n : ℝ))⁻¹) := by
              rw [show r + 2 = r + 1 + 1 by omega, pow_succ]
            rw [hxpow]
            ring
          have hlast :
              T (k + 1) = A (k + 1) + C (k + 1) := by
            dsimp [T, A, C]
            rw [shiftedPowerSum_succ_n]
            simp [shiftedElemSymm_zero, x]
            ring
          have hcancel :
              (∑ r ∈ Finset.range (k + 2), C r)
                + (∑ r ∈ Finset.range (k + 1), D r)
                =
              x * shiftedElemSymm α (k + 1) n := by
            have h :=
              alternating_newton_cancel x
                (fun m : ℕ => shiftedElemSymm α m n) (k + 1)
            simpa [C, D] using h
          have hnew_expand :
              (∑ r ∈ Finset.range (k + 2), T r)
                =
              (∑ r ∈ Finset.range (k + 2), A r)
                +
              x * (∑ r ∈ Finset.range (k + 1), B r)
                +
              x * shiftedElemSymm α (k + 1) n := by
            rw [hsplitT, hprefix, hlast, hsplitA]
            calc
              (∑ r ∈ Finset.range (k + 1), (A r + x * B r + C r + D r))
                  + (A (k + 1) + C (k + 1))
                =
              ((∑ r ∈ Finset.range (k + 1), A r) + A (k + 1))
                +
              x * (∑ r ∈ Finset.range (k + 1), B r)
                +
              (((∑ r ∈ Finset.range (k + 1), C r) + C (k + 1))
                + (∑ r ∈ Finset.range (k + 1), D r)) := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                    Finset.sum_add_distrib, Finset.mul_sum]
                  ring
              _ =
              ((∑ r ∈ Finset.range (k + 1), A r) + A (k + 1))
                +
              x * (∑ r ∈ Finset.range (k + 1), B r)
                +
              x * shiftedElemSymm α (k + 1) n := by
                  rw [← hsplitC, hcancel]
          rw [hE]
          have ih1 := ih (k + 1)
          have ih0 := ih k
          change
            (((k + 2 : ℕ) : ℝ))
                * (shiftedElemSymm α (k + 2) n
                  + x * shiftedElemSymm α (k + 1) n)
              =
            ∑ r ∈ Finset.range (k + 2), T r
          rw [hnew_expand, ← ih1, ← ih0]
          push_cast
          ring


theorem logKBracket_newton (α : ℝ) (k n : ℕ) :
    logKBracket α (k + 1) n
      =
    shiftedPowerSum α 1 n * logKBracket α k n
      +
    ∑ r ∈ Finset.range k,
      ((-1 : ℝ) ^ (r + 1)
        * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))
        * shiftedPowerSum α (r + 2) n
        * logKBracket α (k - 1 - r) n := by
  classical
  have hN := shiftedElemSymm_newton α k n
  let F : ℕ → ℝ :=
    fun r =>
      (-1 : ℝ) ^ r
        * shiftedPowerSum α (r + 1) n
        * shiftedElemSymm α (k - r) n
  have hN' :
      (((k + 1 : ℕ) : ℝ)) * shiftedElemSymm α (k + 1) n
        =
      ∑ r ∈ Finset.range (k + 1), F r := by
    simpa [F] using hN
  calc
    logKBracket α (k + 1) n
        =
      (k.factorial : ℝ)
        * ((((k + 1 : ℕ) : ℝ)) * shiftedElemSymm α (k + 1) n) := by
        rw [logKBracket, Nat.factorial_succ]
        push_cast
        ring
    _ =
      (k.factorial : ℝ) * (∑ r ∈ Finset.range (k + 1), F r) := by
        rw [hN']
    _ =
      (k.factorial : ℝ)
        * (F 0 + ∑ r ∈ Finset.range k, F (r + 1)) := by
        rw [Finset.sum_range_succ']
        ring
    _ =
      shiftedPowerSum α 1 n * logKBracket α k n
        +
      ∑ r ∈ Finset.range k,
        ((-1 : ℝ) ^ (r + 1)
          * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))
          * shiftedPowerSum α (r + 2) n
          * logKBracket α (k - 1 - r) n := by
        rw [mul_add, Finset.mul_sum]
        refine congrArg₂ HAdd.hAdd ?_ ?_
        · simp [F, logKBracket]
          ring
        · refine Finset.sum_congr rfl ?_
          intro r hr
          rw [Finset.mem_range] at hr
          have hsub : k - (r + 1) = k - 1 - r := by omega
          have hfac_ne :
              (((k - 1 - r).factorial : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero (k - 1 - r)
          simp [F, logKBracket, hsub]
          field_simp [hfac_ne]

/-- `k!·e_k((α+j)⁻¹, j<n) ~ (log n)^k`. -/
theorem logKBracket_isEquivalent_log_pow
    {α : ℝ} (hα : 0 < α) (k : ℕ) :
    (fun n : ℕ => logKBracket α k n)
      ~[atTop]
    (fun n : ℕ => (Real.log n) ^ k) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          have hleft :
              (fun n : ℕ => logKBracket α 0 n)
                = fun _ : ℕ => (1 : ℝ) := by
            funext n
            simp [logKBracket]
          rw [hleft]
          simpa using
            (Asymptotics.IsEquivalent.refl
              (l := atTop) (u := fun _ : ℕ => (1 : ℝ)))
      | succ k =>
          have ihk :
              (fun n : ℕ => logKBracket α k n)
                ~[atTop]
              (fun n : ℕ => (Real.log n) ^ k) :=
            ih k (Nat.lt_succ_self k)
          have hp1 :
              (fun n : ℕ => shiftedPowerSum α 1 n)
                ~[atTop]
              (fun n : ℕ => Real.log n) := by
            rw [shiftedPowerSum_one_eq_shiftedHarmonic]
            exact shiftedHarmonic_isEquivalent_log hα
          have hmain :
              (fun n : ℕ =>
                  shiftedPowerSum α 1 n * logKBracket α k n)
                ~[atTop]
              (fun n : ℕ => (Real.log n) ^ (k + 1)) := by
            have hmul := hp1.mul ihk
            have heq : ((fun n : ℕ => Real.log n) * (fun n : ℕ => (Real.log n) ^ k))
                = (fun n : ℕ => (Real.log n) ^ (k + 1)) := by
              funext n; simp only [Pi.mul_apply]; rw [pow_succ]; ring
            rwa [heq] at hmul
          have hnewton :
              (fun n : ℕ => logKBracket α (k + 1) n)
                =
              (fun n : ℕ =>
                shiftedPowerSum α 1 n * logKBracket α k n
                  +
                ∑ r ∈ Finset.range k,
                  ((-1 : ℝ) ^ (r + 1)
                    * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))
                    * shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n) := by
            funext n
            exact logKBracket_newton α k n
          have hlower :
              (fun n : ℕ =>
                ∑ r ∈ Finset.range k,
                  ((-1 : ℝ) ^ (r + 1)
                    * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))
                    * shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n)
                =o[atTop]
              (fun n : ℕ => (Real.log n) ^ (k + 1)) := by
            refine isLittleO_finset_sum ?_
            intro r hr
            rw [Finset.mem_range] at hr
            have hps :
                (fun n : ℕ => shiftedPowerSum α (r + 2) n)
                  =O[atTop] (fun n : ℕ => Real.log n) :=
              shiftedPowerSum_isBigO_log hα (by omega : 1 ≤ r + 2)
            have hm_lt : k - 1 - r < k + 1 := by omega
            have hbr :
                (fun n : ℕ => logKBracket α (k - 1 - r) n)
                  ~[atTop]
                (fun n : ℕ => (Real.log n) ^ (k - 1 - r)) :=
              ih (k - 1 - r) hm_lt
            have hprod :
                (fun n : ℕ =>
                  shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n)
                  =O[atTop]
                (fun n : ℕ =>
                  Real.log n * (Real.log n) ^ (k - 1 - r)) :=
              hps.mul hbr.isBigO
            have hpoweq :
                (fun n : ℕ =>
                  Real.log n * (Real.log n) ^ (k - 1 - r))
                  =ᶠ[atTop]
                (fun n : ℕ => (Real.log n) ^ (k - r)) := by
              have hkr : k - r = (k - 1 - r) + 1 := by omega
              filter_upwards with n
              rw [hkr, pow_succ]
              ring
            have hprod' :
                (fun n : ℕ =>
                  shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n)
                  =O[atTop]
                (fun n : ℕ => (Real.log n) ^ (k - r)) :=
              hprod.congr' EventuallyEq.rfl hpoweq
            have hlo :
                (fun n : ℕ => (Real.log n) ^ (k - r))
                  =o[atTop]
                (fun n : ℕ => (Real.log n) ^ (k + 1)) :=
              log_pow_isLittleO_log_pow (by omega : k - r < k + 1)
            have hterm :
                (fun n : ℕ =>
                  shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n)
                  =o[atTop]
                (fun n : ℕ => (Real.log n) ^ (k + 1)) :=
              hprod'.trans_isLittleO hlo
            refine (hterm.const_mul_left
              ((-1 : ℝ) ^ (r + 1)
                * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))).congr'
              ?_ EventuallyEq.rfl
            filter_upwards with n
            ring
          have hsum :
              (fun n : ℕ =>
                shiftedPowerSum α 1 n * logKBracket α k n
                  +
                ∑ r ∈ Finset.range k,
                  ((-1 : ℝ) ^ (r + 1)
                    * ((k.factorial : ℝ) / (((k - 1 - r).factorial : ℕ) : ℝ)))
                    * shiftedPowerSum α (r + 2) n
                    * logKBracket α (k - 1 - r) n)
                ~[atTop]
              (fun n : ℕ => (Real.log n) ^ (k + 1)) :=
            hmain.add_isLittleO hlower
          rw [hnewton]
          exact hsum

/-- Cast the real log^k scale to the complex closed coefficient. -/
theorem logKSingularityScale_cast (α : ℝ) (k n : ℕ) :
    (logKSingularityScale α k n : ℂ)
      = logKCoeffℂ (α : ℂ) k n := by
  have hchoose : Ring.choose (((α : ℂ) + n - 1)) n =
      ((Ring.choose (α + n - 1) n : ℝ) : ℂ) := by
    rw [Ring.choose, Ring.choose]
    change Ring.multichoose ((α : ℂ) + n - 1 - n + 1) n =
      (algebraMap ℝ ℂ)
        (Ring.multichoose ((α + n - 1 : ℝ) - n + 1) n)
    rw [Ring.map_multichoose
      (algebraMap ℝ ℂ) ((α + n - 1 : ℝ) - n + 1) n]
    congr 1
    norm_num [Complex.ofReal_add, Complex.ofReal_sub]
  rw [logKSingularityScale, logKCoeffℂ, binCoeffℂ,
    Complex.ofReal_mul, Complex.ofReal_mul, shiftedElemSymm_cast, ← hchoose]
  push_cast
  ring

theorem logKSingularityScale_isEquivalent
    {α : ℝ} (hα : 1 < α) (k : ℕ) :
    (fun n : ℕ => logKSingularityScale α k n)
      ~[atTop]
    (fun n : ℕ =>
      ((n : ℝ) ^ (α - 1) / Real.Gamma α) * (Real.log n) ^ k) := by
  have hα0 : 0 < α := by linarith
  have hchoose :=
    choose_standard_scale_real (α := α)
      (fun m => by
        have hm : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        exact ne_of_gt (by linarith))
  have hbracket := logKBracket_isEquivalent_log_pow hα0 k
  refine (hchoose.mul hbracket).congr_left ?_
  filter_upwards with n
  simp [Pi.mul_apply, logKSingularityScale, logKBracket]
  ring

end AnalyticCombinatorics
