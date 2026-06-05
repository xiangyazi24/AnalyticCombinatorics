import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.SummatoryWindow
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# Model-kernel window limit for the Erdős partition route

This file isolates the model-kernel window limit

  (1/n) * Σ_{1 ≤ m ≤ n-1, a√n ≤ m ≤ b√n}
    σ(m) * exp (-(C/2) * m / √n)
  →
  ∫ y in a..b, (π²/6) * y * exp (-(C/2)y)

The proof is deliberately split into:

1. basic summatory-window mass convergence for half-open windows;
2. a first-window `α = 0` variant using `sigma_summatory_asymptotic`;
3. the final real-variable step approximation theorem.

The final step approximation theorem is marked as the only remaining prover task.
It is the sub-block squeeze/Riemann-Stieltjes argument described in the prompt.
-/

-- generous heartbeats: long ε-bookkeeping chains in the windowed summatory limits
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

noncomputable section

open Filter Finset
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model


local notation "σR" => Sigma.sigmaR
local notation "Sσ" => Sigma.summatory

/-- Main quadratic constant for the summatory divisor function. -/
private noncomputable def Q : ℝ := Real.pi ^ 2 / 12

/-- The model density. -/
private noncomputable def modelDensity (C : ℝ) (y : ℝ) : ℝ :=
  (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y)

/-- The model weighted window sum. -/
private noncomputable def modelKernelWindowSum (C a b : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ m ∈ Finset.Icc 1 (n - 1),
      (if a * Real.sqrt (n : ℝ) ≤ (m : ℝ) ∧
          (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
       then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
       else 0)

/-- Half-open unweighted mass `(α√n, β√n]`, scaled by `1/n`. -/
private noncomputable def halfOpenMass (α β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    (Sσ (β * Real.sqrt (n : ℝ)) - Sσ (α * Real.sqrt (n : ℝ)))

private lemma Q_pos : 0 < Q := by
  dsimp [Q]
  positivity

private lemma two_mul_Q :
    2 * Q = Real.pi ^ 2 / 6 := by
  dsimp [Q]
  ring

private lemma modelDensity_eq (C y : ℝ) :
    modelDensity C y =
      2 * Q * y * Real.exp (-(C / 2) * y) := by
  dsimp [modelDensity, Q]
  ring

private lemma sqrt_nat_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

private lemma sqrt_nat_pos_eventually :
    ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact Real.sqrt_pos_of_pos (by exact_mod_cast hn)

private lemma natCast_pos_eventually :
    ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact_mod_cast hn

private lemma one_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

private lemma log_over_sqrt_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log (2 * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ))
      atTop
      (𝓝 0) := by
  have hsqrt := sqrt_nat_atTop
  have hreal :
      Tendsto (fun x : ℝ => Real.log (2 * x) / x) atTop (𝓝 0) := by
    have h1 :
        Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 :
        Tendsto (fun x : ℝ => Real.log 2 / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h2pos : (0 : ℝ) < 2 := by norm_num
    rw [Real.log_mul h2pos.ne' hx.ne']
    ring
  exact hreal.comp hsqrt

private lemma log_const_mul_sqrt_over_sqrt_tendsto_zero
    {β : ℝ} (hβ : 0 < β) :
    Tendsto
      (fun n : ℕ =>
        Real.log (2 * (β * Real.sqrt (n : ℝ))) /
          Real.sqrt (n : ℝ))
      atTop
      (𝓝 0) := by
  have hsqrt := sqrt_nat_atTop
  have hreal :
      Tendsto
        (fun x : ℝ => Real.log (2 * (β * x)) / x)
        atTop
        (𝓝 0) := by
    have hmulpos : 0 < 2 * β := by positivity
    have h1 :
        Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 :
        Tendsto (fun x : ℝ => Real.log (2 * β) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (2 : ℝ) * (β * x) = (2 * β) * x by ring,
      Real.log_mul hmulpos.ne' hx.ne']
    ring
  exact hreal.comp hsqrt

private lemma alpha_sqrt_ge_one_eventually
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ α * Real.sqrt (n : ℝ) := by
  have ht :
      Tendsto (fun n : ℕ => α * Real.sqrt (n : ℝ)) atTop atTop := by
    exact (sqrt_nat_atTop.const_mul_atTop hα)
  exact ht.eventually_ge_atTop 1

/--
First-window summatory mass, i.e. the case `α = 0`:

`S(β√n)/n → Q β²`.
-/
lemma summatory_zero_to_beta_scaled_tendsto
    {β : ℝ} (hβ : 0 < β) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * Sσ (β * Real.sqrt (n : ℝ)))
      atTop
      (𝓝 (Q * β ^ 2)) := by
  rcases Sigma.sigma_summatory_asymptotic with ⟨K, hKpos, hK⟩
  have hmain :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            (Q * (β * Real.sqrt (n : ℝ)) ^ 2))
        atTop
        (𝓝 (Q * β ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnz : (n : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : n ≠ 0)
    have hsqr :
        (β * Real.sqrt (n : ℝ)) ^ 2 = β ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    rw [hsqr]
    field_simp [hnz]
  have herr :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            (Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2))
        atTop
        (𝓝 0) := by
    refine squeeze_zero_norm'
      (a := fun n : ℕ => K * β *
        (Real.log (2 * (β * Real.sqrt (n : ℝ))) / Real.sqrt (n : ℝ))) ?_ ?_
    · filter_upwards
        [eventually_ge_atTop (1 : ℕ),
         ((sqrt_nat_atTop.const_mul_atTop hβ)).eventually_ge_atTop 1]
        with n hn hx
      rw [Real.norm_eq_abs]
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hspos : 0 < Real.sqrt (n : ℝ) :=
        Real.sqrt_pos_of_pos (by exact_mod_cast hn)
      have hbound := hK (β * Real.sqrt (n : ℝ)) hx
      have hrewrite :
          (1 / (n : ℝ)) *
              (K * (β * Real.sqrt (n : ℝ)) *
                Real.log (2 * (β * Real.sqrt (n : ℝ))))
            =
          K * β *
            (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
              Real.sqrt (n : ℝ)) := by
        have hsqr :
            Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))
        field_simp [hnpos.ne', hspos.ne', hsqr]
        rw [sq, hsqr]
      calc
        |(1 / (n : ℝ)) *
            (Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2)|
            =
          (1 / (n : ℝ)) *
            |Sσ (β * Real.sqrt (n : ℝ)) -
              Q * (β * Real.sqrt (n : ℝ)) ^ 2| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ))]
        _ ≤
          (1 / (n : ℝ)) *
            (K * (β * Real.sqrt (n : ℝ)) *
              Real.log (2 * (β * Real.sqrt (n : ℝ)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              dsimp [Q]
              simpa using hbound
        _ =
          K * β *
            (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
              Real.sqrt (n : ℝ)) := hrewrite
    · have ht :=
        log_const_mul_sqrt_over_sqrt_tendsto_zero (β := β) hβ
      simpa [mul_assoc] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => K * β) atTop (𝓝 (K * β))).mul ht)
  have hsum := herr.add hmain
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  ring

/--
Half-open window mass convergence:

`(S(β√n)-S(α√n))/n → Q(β²-α²)`.
-/
lemma halfOpenMass_tendsto
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) :
    Tendsto (halfOpenMass α β) atTop
      (𝓝 (Q * (β ^ 2 - α ^ 2))) := by
  by_cases hαzero : α = 0
  · subst hαzero
    have hβ : 0 < β := lt_of_le_of_lt hα hαβ
    have hfirst := summatory_zero_to_beta_scaled_tendsto (β := β) hβ
    have hfun : halfOpenMass 0 β = fun n : ℕ =>
        (1 / (n : ℝ)) * Sσ (β * Real.sqrt (n : ℝ)) := by
      funext n
      have hS0 : Sσ ((0 : ℝ) * Real.sqrt (n : ℝ)) = 0 := by
        have : ((0 : ℝ) * Real.sqrt (n : ℝ)) = 0 := by ring
        rw [this]
        unfold Sigma.summatory
        rw [show ⌊(0 : ℝ)⌋₊ = 0 from Nat.floor_zero]
        rw [Finset.Icc_eq_empty (by norm_num : ¬(1 : ℕ) ≤ 0)]
        exact Finset.sum_empty
      unfold halfOpenMass
      rw [hS0, sub_zero]
    rw [hfun]
    simpa [Q] using hfirst
  · have hαpos : 0 < α := lt_of_le_of_ne' hα hαzero
    rcases Sigma.summatory_window_diff with ⟨K, hKpos, hK⟩
    have herr :
        Tendsto
          (fun n : ℕ =>
            (1 / (n : ℝ)) *
              ((Sσ (β * Real.sqrt (n : ℝ)) -
                  Sσ (α * Real.sqrt (n : ℝ))) -
                Q * (n : ℝ) * (β ^ 2 - α ^ 2)))
          atTop
          (𝓝 0) := by
      refine squeeze_zero_norm'
        (a := fun n : ℕ => K * (α + β) *
          (Real.log (2 * (β * Real.sqrt (n : ℝ))) / Real.sqrt (n : ℝ))) ?_ ?_
      · filter_upwards
          [eventually_ge_atTop (1 : ℕ),
           alpha_sqrt_ge_one_eventually (α := α) hαpos]
          with n hn hα1
        rw [Real.norm_eq_abs]
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
        have hbound := hK α β n hα hαβ hα1
        calc
          |(1 / (n : ℝ)) *
            ((Sσ (β * Real.sqrt (n : ℝ)) -
                Sσ (α * Real.sqrt (n : ℝ))) -
              Q * (n : ℝ) * (β ^ 2 - α ^ 2))|
              =
            (1 / (n : ℝ)) *
              |(Sσ (β * Real.sqrt (n : ℝ)) -
                  Sσ (α * Real.sqrt (n : ℝ))) -
                Q * (n : ℝ) * (β ^ 2 - α ^ 2)| := by
                rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ))]
          _ ≤
            (1 / (n : ℝ)) *
              (K * (α + β) * Real.sqrt (n : ℝ) *
                Real.log (2 * (β * Real.sqrt (n : ℝ)))) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                dsimp [Q]
                simpa using hbound
          _ =
            K * (α + β) *
              (Real.log (2 * (β * Real.sqrt (n : ℝ))) /
                Real.sqrt (n : ℝ)) := by
                have hspos : 0 < Real.sqrt (n : ℝ) :=
                  Real.sqrt_pos_of_pos (by exact_mod_cast hn)
                have hsqr :
                    Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
                  Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))
                field_simp [hnpos.ne', hspos.ne', hsqr]
                rw [sq, hsqr]
                ring
      · have hβpos : 0 < β := lt_trans hαpos hαβ
        have ht :=
          log_const_mul_sqrt_over_sqrt_tendsto_zero (β := β) hβpos
        simpa [mul_assoc] using
          ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => K * (α + β))
              atTop
              (𝓝 (K * (α + β)))).mul ht)
    have hmain :
        Tendsto
          (fun n : ℕ =>
            (1 / (n : ℝ)) *
              (Q * (n : ℝ) * (β ^ 2 - α ^ 2)))
          atTop
          (𝓝 (Q * (β ^ 2 - α ^ 2))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hnz : (n : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : n ≠ 0)
      field_simp [hnz]
    have hsum := herr.add hmain
    rw [zero_add] at hsum
    refine hsum.congr' ?_
    filter_upwards with n
    dsimp [halfOpenMass]
    ring

/--
For fixed `α < β`, the exponential factor is squeezed between endpoint values
on the block `(α√n, β√n]`.
-/
lemma model_exp_endpoint_squeeze
    {C α β : ℝ} (hC : 0 < C) (_hαβ : α ≤ β) :
    ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ,
        α * Real.sqrt (n : ℝ) < (m : ℝ) →
        (m : ℝ) ≤ β * Real.sqrt (n : ℝ) →
          Real.exp (-(C / 2) * β)
            ≤ Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)) ∧
          Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
            ≤ Real.exp (-(C / 2) * α) := by
  filter_upwards [sqrt_nat_pos_eventually] with n hspos m hmα hmβ
  have hdiv_lower : α ≤ (m : ℝ) / Real.sqrt (n : ℝ) := by
    exact (le_div_iff₀ hspos).mpr hmα.le
  have hdiv_upper : (m : ℝ) / Real.sqrt (n : ℝ) ≤ β := by
    exact (div_le_iff₀ hspos).mpr hmβ
  constructor
  · apply Real.exp_le_exp.mpr
    have hlam : 0 ≤ C / 2 := by linarith
    have hform : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)
        = -(C / 2 * ((m : ℝ) / Real.sqrt (n : ℝ))) := by ring
    rw [hform]
    have hmul := mul_le_mul_of_nonneg_left hdiv_upper hlam
    linarith
  · apply Real.exp_le_exp.mpr
    have hlam : 0 ≤ C / 2 := by linarith
    have hform : -(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ)
        = -(C / 2 * ((m : ℝ) / Real.sqrt (n : ℝ))) := by ring
    rw [hform]
    have hmul := mul_le_mul_of_nonneg_left hdiv_lower hlam
    linarith


end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
