import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.QuasiPowers

/-!
# Cycles in a random permutation

This file instantiates the local quasi-powers interface for the Feller coupling
model of the number of cycles in a uniform random permutation:
`C_n = sum_{k=1}^n B_k`, with independent Bernoulli variables
`P(B_k = 1) = 1 / k`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The harmonic scale `H_n = sum_{k=1}^n 1/k`, as a real number. -/
def cycleH (n : ℕ) : ℝ :=
  (harmonic n : ℝ)

/-- Bernoulli law with success probability `1 / (k + 1)`. -/
def cycleBernoulliLaw (k : ℕ) : Measure ℝ :=
  ENNReal.ofReal (1 - ((k : ℝ) + 1)⁻¹) • Measure.dirac (0 : ℝ) +
    ENNReal.ofReal (((k : ℝ) + 1)⁻¹) • Measure.dirac (1 : ℝ)

lemma cycleBernoulliLaw_isProbabilityMass (k : ℕ) :
    (cycleBernoulliLaw k) Set.univ = 1 := by
  rw [cycleBernoulliLaw]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  simp
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 1 - ((k : ℝ) + 1)⁻¹ := by
    rw [sub_nonneg]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  rw [← ENNReal.ofReal_add hnonneg (inv_nonneg.mpr hpos.le)]
  rw [show 1 - ((k : ℝ) + 1)⁻¹ + ((k : ℝ) + 1)⁻¹ = (1 : ℝ) by ring]
  simp

instance cycleBernoulliLaw_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (cycleBernoulliLaw k) where
  measure_univ := cycleBernoulliLaw_isProbabilityMass k

/-- Product probability space for the first `n` Feller Bernoulli variables. -/
abbrev CycleΩ (n : ℕ) := Fin n → ℝ

/-- Product law of the independent Bernoulli variables `B_k`, `1 ≤ k ≤ n`. -/
def cycleP (n : ℕ) : Measure (CycleΩ n) :=
  Measure.pi (fun i : Fin n => cycleBernoulliLaw i.1)

instance cycleP_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (cycleP n) := by
  unfold cycleP
  infer_instance

/-- Feller coupling model for the number of cycles in a uniform random permutation. -/
def cycleCount (n : ℕ) (ω : CycleΩ n) : ℝ :=
  ∑ i, ω i

/-- One factor in the cycle-count characteristic function, in logarithmic variable `z`. -/
def cycleBase (k : ℕ) (z : ℂ) : ℂ :=
  ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) +
    (((k : ℝ) + 1)⁻¹ : ℝ) * Complex.exp z

/-- The `H_n`-scale quadratic main term.  Its first two Taylor coefficients are both `1`. -/
def cycleMain (z : ℂ) : ℂ :=
  z + z ^ 2 / 2

/-- Exact logarithmic remainder in the quasi-powers expansion. -/
def cycleR (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    ((∑ i : Fin n, Complex.log (cycleBase i.1 z)) - (cycleH n : ℂ) * cycleMain z) /
      (cycleH n : ℂ)

lemma cycleH_zero : cycleH 0 = 0 := by
  simp [cycleH]

lemma cycleH_pos {n : ℕ} (hn : n ≠ 0) : 0 < cycleH n := by
  unfold cycleH
  exact_mod_cast harmonic_pos hn

lemma cycleH_ne_zero {n : ℕ} (hn : n ≠ 0) : (cycleH n : ℂ) ≠ 0 := by
  exact_mod_cast (cycleH_pos hn).ne'

lemma cycleBernoulliLaw_charFun (k : ℕ) (s : ℝ) :
    charFun (cycleBernoulliLaw k) s = cycleBase k (Complex.I * (s : ℂ)) := by
  rw [cycleBernoulliLaw, charFun_apply_real]
  have h0 : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (0 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (0 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  have h1 : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  rw [integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
    (h1.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnonneg : 0 ≤ 1 - ((k : ℝ) + 1)⁻¹ := by
    rw [sub_nonneg]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le)]
  have hcomm : (s : ℂ) * Complex.I = Complex.I * (s : ℂ) := by ring
  apply Complex.ext
  · dsimp [cycleBase]
    simp [hcomm]
    have hre0 :
        (((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).re) =
          (1 - ((k : ℝ) + 1)⁻¹) * 1 := by
      rw [Complex.smul_re]
      simp [smul_eq_mul]
    have hre1 :
        ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).re =
          ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
      rw [Complex.smul_re]
      simp [smul_eq_mul]
    exact calc
      ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).re +
          ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).re
          = (1 - ((k : ℝ) + 1)⁻¹) * 1 +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
              exact congrArg₂ (fun a b : ℝ => a + b) hre0 hre1
      _ = 1 - ((k : ℝ) + 1)⁻¹ +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).re := by
              ring_nf
  · dsimp [cycleBase]
    simp [hcomm]
    have him0 :
        (((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).im) =
          (1 - ((k : ℝ) + 1)⁻¹) * 0 := by
      rw [Complex.smul_im]
      simp [smul_eq_mul]
    have him1 :
        ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).im =
          ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
      rw [Complex.smul_im]
      simp [smul_eq_mul]
    exact calc
      ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) • (1 : ℂ)).im +
          ((((k : ℝ) + 1)⁻¹ : ℝ) • Complex.exp (Complex.I * (s : ℂ))).im
          = (1 - ((k : ℝ) + 1)⁻¹) * 0 +
              ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
              exact congrArg₂ (fun a b : ℝ => a + b) him0 him1
      _ = ((k : ℝ) + 1)⁻¹ * (Complex.exp (Complex.I * (s : ℂ))).im := by
              ring_nf

lemma cycleCount_charFun (n : ℕ) (s : ℝ) :
    charFun ((cycleP n).map (cycleCount n)) s =
      ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ)) := by
  change charFun ((Measure.pi fun i : Fin n => cycleBernoulliLaw i.1).map
      (fun p => ∑ i, p i)) s =
    ∏ i : Fin n, cycleBase i.1 (Complex.I * (s : ℂ))
  have h := congrFun (charFun_map_sum_pi_eq_prod
    (μ := fun i : Fin n => cycleBernoulliLaw i.1)) s
  rw [h]
  simp [cycleBernoulliLaw_charFun]

lemma cycleBase_ne_zero_of_abs_le_half {k : ℕ} {s : ℝ} (hs : |s| ≤ (1 / 2 : ℝ)) :
    cycleBase k (Complex.I * (s : ℂ)) ≠ 0 := by
  let p : ℝ := ((k : ℝ) + 1)⁻¹
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)
  have hdist : ‖(p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)‖ < 1 := by
    calc
      ‖(p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)‖
          = p * ‖Complex.exp (Complex.I * (s : ℂ)) - 1‖ := by
            rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hp_nonneg]
      _ ≤ p * ‖s‖ := by
            gcongr
            simpa [mul_comm] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s)
      _ ≤ p * (1 / 2 : ℝ) := by
            gcongr
            simpa [Real.norm_eq_abs] using hs
      _ ≤ 1 * (1 / 2 : ℝ) := by
            gcongr
      _ < 1 := by norm_num
  have hbase :
      cycleBase k (Complex.I * (s : ℂ)) =
        1 + (p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1) := by
    change (((1 - p : ℝ) : ℂ) + (p : ℂ) *
        Complex.exp (Complex.I * (s : ℂ))) =
      1 + (p : ℂ) * (Complex.exp (Complex.I * (s : ℂ)) - 1)
    rw [show ((1 - p : ℝ) : ℂ) = 1 - (p : ℂ) by norm_cast]
    ring
  rw [hbase]
  exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hdist)

lemma cycle_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((cycleP n).map (cycleCount n)) s =
      Complex.exp ((cycleH n : ℂ) * (((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        cycleR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro n s hs
  rw [cycleCount_charFun]
  by_cases hn : n = 0
  · subst n
    simp [cycleR, cycleH_zero]
  · let z : ℂ := Complex.I * (s : ℂ)
    have hbase : ∀ i : Fin n, cycleBase i.1 z ≠ 0 := fun i =>
      cycleBase_ne_zero_of_abs_le_half (k := i.1) (s := s) hs
    change (∏ i : Fin n, cycleBase i.1 z) =
      Complex.exp ((cycleH n : ℂ) * ((1 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + cycleR n z) + 0)
    rw [cycleR, if_neg hn]
    have hH : (cycleH n : ℂ) ≠ 0 := cycleH_ne_zero hn
    rw [show (cycleH n : ℂ) * ((1 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 +
          ((∑ i : Fin n, Complex.log (cycleBase i.1 z)) - (cycleH n : ℂ) * cycleMain z) /
            (cycleH n : ℂ)) + 0 =
        ∑ i : Fin n, Complex.log (cycleBase i.1 z) by
      field_simp [hH]
      simp [cycleMain]
      ring_nf]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Complex.exp_log (hbase i)).symm

lemma cycleH_tendsto_atTop : Tendsto cycleH atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbounded :
      Tendsto (fun n : ℕ => cycleH n - Real.log (n : ℝ))
        atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa [cycleH] using Real.tendsto_harmonic_sub_log
  have hsum := hlog.atTop_add hbounded
  refine Tendsto.congr' ?_ hsum
  filter_upwards with n
  ring

/-- The Bernoulli success weight in the Feller cycle decomposition. -/
private def cycleW (k : ℕ) : ℝ :=
  ((k : ℝ) + 1)⁻¹

private lemma cycleW_nonneg (k : ℕ) : 0 ≤ cycleW k := by
  dsimp [cycleW]
  positivity

private lemma cycleW_le_one (k : ℕ) : cycleW k ≤ 1 := by
  dsimp [cycleW]
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  exact inv_le_one_of_one_le₀ (by linarith : (1 : ℝ) ≤ (k : ℝ) + 1)

private lemma cycleH_nonneg (n : ℕ) : 0 ≤ cycleH n := by
  by_cases hn : n = 0
  · simp [hn, cycleH_zero]
  · exact (cycleH_pos hn).le

private lemma cycleBase_eq_one_add_cycleW (k : ℕ) (z : ℂ) :
    cycleBase k z = 1 + (cycleW k : ℂ) * (Complex.exp z - 1) := by
  dsimp [cycleBase, cycleW]
  rw [show ((1 - ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) =
      1 - ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) by norm_cast]
  ring

private lemma cycleW_sum_eq_cycleH_real (n : ℕ) :
    (∑ i : Fin n, cycleW i.1) = cycleH n := by
  rw [cycleH, harmonic]
  rw [Rat.cast_sum]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro x hx
  simp [cycleW, Finset.mem_range.mp hx]

private lemma cycleW_sum_eq_cycleH_complex (n : ℕ) :
    (∑ i : Fin n, (cycleW i.1 : ℂ)) = (cycleH n : ℂ) := by
  rw [← cycleW_sum_eq_cycleH_real n]
  norm_cast

private lemma cycleW_sq_summable :
    Summable (fun k : ℕ => cycleW k ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num : (1 : ℝ) < 2)
  refine h.congr ?_
  intro k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  rw [cycleW, abs_of_pos hk]
  field_simp [pow_two]
  rw [Real.rpow_two]

private lemma cycleW_sq_sum_le_tsum (n : ℕ) :
    (∑ i : Fin n, cycleW i.1 ^ 2) ≤ ∑' k : ℕ, cycleW k ^ 2 := by
  calc
    (∑ i : Fin n, cycleW i.1 ^ 2)
        = ∑ k ∈ Finset.range n, cycleW k ^ 2 := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro x hx
          simp [cycleW, Finset.mem_range.mp hx]
    _ ≤ ∑' k : ℕ, cycleW k ^ 2 := by
          exact cycleW_sq_summable.sum_le_tsum (Finset.range n)
            (fun i _hi => by positivity)

private lemma cycleW_sq_tsum_nonneg : 0 ≤ ∑' k : ℕ, cycleW k ^ 2 :=
  tsum_nonneg fun k => by positivity

private lemma norm_exp_sub_quadratic_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 := by
  have h := Complex.exp_bound (x := z) (n := 3) hz (by norm_num)
  have hsum (z : ℂ) :
      (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
        1 + z + z ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hconst : ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℝ))⁻¹) ≤ 1 := by
    norm_num [Nat.factorial]
  refine h.trans ?_
  calc
    ‖z‖ ^ 3 * ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℝ))⁻¹)
        ≤ ‖z‖ ^ 3 * 1 := by
          gcongr
    _ = ‖z‖ ^ 3 := by ring

private lemma norm_log_one_add_sub_self_sq {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 := by
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have h := Complex.norm_log_one_add_sub_self_le (z := x) hxlt
  have hinv : (1 - ‖x‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀]
    · linarith
    · linarith
    · norm_num
  calc
    ‖Complex.log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 := h
    _ ≤ ‖x‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖x‖ ^ 2 := by ring

private lemma cycle_scaled_remainder_norm_le {n : ℕ} {z : ℂ}
    (hn : n ≠ 0) (hw : ‖Complex.exp z - 1‖ ≤ 1 / 2) :
    ‖(cycleH n : ℂ) * cycleR n z‖ ≤
      cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
        (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp z - 1‖ ^ 2 := by
  let w : ℂ := Complex.exp z - 1
  let x : Fin n → ℂ := fun i => (cycleW i.1 : ℂ) * w
  have hscaled :
      (cycleH n : ℂ) * cycleR n z =
        (∑ i : Fin n, Complex.log (1 + x i)) - (cycleH n : ℂ) * cycleMain z := by
    rw [cycleR, if_neg hn]
    field_simp [cycleH_ne_zero hn]
    apply congrArg₂ (fun a b : ℂ => a - b) ?_ rfl
    apply Finset.sum_congr rfl
    intro i _hi
    rw [cycleBase_eq_one_add_cycleW]
  have hxsum : (∑ i : Fin n, x i) = (cycleH n : ℂ) * w := by
    calc
      (∑ i : Fin n, x i) = (∑ i : Fin n, (cycleW i.1 : ℂ) * w) := rfl
      _ = (∑ i : Fin n, (cycleW i.1 : ℂ)) * w := by rw [Finset.sum_mul]
      _ = (cycleH n : ℂ) * w := by rw [cycleW_sum_eq_cycleH_complex]
  have hlogsum :
      (∑ i : Fin n, Complex.log (1 + x i)) =
        (∑ i : Fin n, x i) + ∑ i : Fin n, (Complex.log (1 + x i) - x i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hdecomp :
      (cycleH n : ℂ) * cycleR n z =
        (cycleH n : ℂ) * (w - z - z ^ 2 / 2) +
          ∑ i : Fin n, (Complex.log (1 + x i) - x i) := by
    rw [hscaled, hlogsum, hxsum]
    simp [cycleMain, w]
    ring
  have hxnorm (i : Fin n) : ‖x i‖ = cycleW i.1 * ‖w‖ := by
    simp [x, Real.norm_eq_abs, abs_of_nonneg (cycleW_nonneg i.1)]
  have hxhalf (i : Fin n) : ‖x i‖ ≤ 1 / 2 := by
    rw [hxnorm]
    calc
      cycleW i.1 * ‖w‖ ≤ 1 * (1 / 2 : ℝ) := by
        gcongr
        exact cycleW_le_one i.1
      _ = 1 / 2 := by ring
  have hlog_bound :
      ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖ ≤
        (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
    calc
      ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖
          ≤ ∑ i : Fin n, ‖Complex.log (1 + x i) - x i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖x i‖ ^ 2 := by
            exact Finset.sum_le_sum fun i _hi => norm_log_one_add_sub_self_sq (hxhalf i)
      _ = (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
            simp_rw [hxnorm]
            calc
              (∑ x : Fin n, (cycleW ↑x * ‖w‖) ^ 2)
                  = ∑ i : Fin n, cycleW i.1 ^ 2 * ‖w‖ ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
              _ = (∑ i : Fin n, cycleW i.1 ^ 2) * ‖w‖ ^ 2 := by
                    rw [Finset.sum_mul]
  have hmain :
      ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2)‖ =
        cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cycleH_nonneg n)]
  rw [hdecomp]
  calc
    ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2) +
        ∑ i : Fin n, (Complex.log (1 + x i) - x i)‖
        ≤ ‖(cycleH n : ℂ) * (w - z - z ^ 2 / 2)‖ +
            ‖∑ i : Fin n, (Complex.log (1 + x i) - x i)‖ := norm_add_le _ _
    _ ≤ cycleH n * ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ +
          (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp z - 1‖ ^ 2 := by
          exact add_le_add (le_of_eq hmain) hlog_bound

private lemma norm_qpZ_cycleH (n : ℕ) (t : ℝ) :
    ‖qpZ cycleH 1 n t‖ = |t| * (Real.sqrt (cycleH n))⁻¹ := by
  have hs : 0 ≤ Real.sqrt (cycleH n) := Real.sqrt_nonneg _
  simp [qpZ, Real.norm_eq_abs, abs_of_nonneg hs, mul_comm, mul_left_comm]

private lemma cycleH_mul_norm_qpZ_cube_tendsto_zero (t : ℝ) :
    Tendsto (fun n : ℕ => cycleH n * ‖qpZ cycleH 1 n t‖ ^ 3) atTop (𝓝 0) := by
  have hsqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt (cycleH n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp cycleH_tendsto_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (cycleH n))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hsqrt_atTop
  have hlim : Tendsto
      (fun n : ℕ => |t| ^ 3 * (Real.sqrt (cycleH n))⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := |t| ^ 3)).mul hinv
  refine Tendsto.congr' ?_ hlim
  filter_upwards [cycleH_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  let s := Real.sqrt (cycleH n)
  have hs_ne : s ≠ 0 := Real.sqrt_ne_zero'.mpr hn
  have hsq : s ^ 2 = cycleH n := Real.sq_sqrt hn.le
  have hs_aux : cycleH n * s⁻¹ ^ 3 = s⁻¹ := by
    rw [← hsq]
    field_simp [hs_ne]
  rw [norm_qpZ_cycleH]
  change |t| ^ 3 * s⁻¹ = cycleH n * (|t| * s⁻¹) ^ 3
  calc
    |t| ^ 3 * s⁻¹ = |t| ^ 3 * (cycleH n * s⁻¹ ^ 3) := by rw [hs_aux]
    _ = cycleH n * (|t| * s⁻¹) ^ 3 := by ring

private theorem cycleR_scaled_tendsto_zero :
    ∀ t, Tendsto
      (fun n : ℕ => (cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)) atTop (𝓝 0) := by
  intro t
  let C : ℝ := ∑' k : ℕ, cycleW k ^ 2
  let z : ℕ → ℂ := fun n => qpZ cycleH 1 n t
  have hz0 : Tendsto z atTop (𝓝 0) :=
    quasiPower_scaledArgument_tendsto_zero (β := cycleH) (u₂ := 1) (t := t)
      cycleH_tendsto_atTop (by norm_num)
  have hnormsq : Tendsto (fun n : ℕ => ‖z n‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hz0.norm.pow 2)
  have hCnormsq : Tendsto (fun n : ℕ => (4 * C) * ‖z n‖ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 4 * C)).mul hnormsq
  have hbound_tendsto :
      Tendsto (fun n : ℕ => cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2)
        atTop (𝓝 0) := by
    simpa [z] using (cycleH_mul_norm_qpZ_cube_tendsto_zero t).add hCnormsq
  refine squeeze_zero_norm' ?_ hbound_tendsto
  have hzsmall : ∀ᶠ n in atTop, ‖z n‖ < 1 / 4 := by
    exact (tendsto_zero_iff_norm_tendsto_zero.mp hz0).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [
      cycleH_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      hzsmall] with n hHpos hzlt
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp [cycleH_zero] at hHpos
  have hzle1 : ‖z n‖ ≤ 1 := by
    exact hzlt.le.trans (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hw : ‖Complex.exp (z n) - 1‖ ≤ 1 / 2 := by
    calc
      ‖Complex.exp (z n) - 1‖ ≤ 2 * ‖z n‖ := Complex.norm_exp_sub_one_le hzle1
      _ ≤ 2 * (1 / 4 : ℝ) := by gcongr
      _ = 1 / 2 := by norm_num
  have hraw := cycle_scaled_remainder_norm_le (n := n) (z := z n) hn hw
  have hHnonneg : 0 ≤ cycleH n := cycleH_nonneg n
  have hSnonneg : 0 ≤ ∑ i : Fin n, cycleW i.1 ^ 2 := by positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact cycleW_sq_tsum_nonneg
  have hSleC : (∑ i : Fin n, cycleW i.1 ^ 2) ≤ C := by
    dsimp [C]
    exact cycleW_sq_sum_le_tsum n
  have hexp_quad :
      ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ ≤ ‖z n‖ ^ 3 := by
    convert norm_exp_sub_quadratic_le (z := z n) hzle1 using 1
    ring_nf
  have hw2 : ‖Complex.exp (z n) - 1‖ ^ 2 ≤ (2 * ‖z n‖) ^ 2 := by
    gcongr
    exact Complex.norm_exp_sub_one_le hzle1
  calc
    ‖(cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)‖
        = ‖(cycleH n : ℂ) * cycleR n (z n)‖ := rfl
    _ ≤ cycleH n * ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ +
          (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp (z n) - 1‖ ^ 2 := hraw
    _ ≤ cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2 := by
          calc
            cycleH n * ‖Complex.exp (z n) - 1 - z n - z n ^ 2 / 2‖ +
                (∑ i : Fin n, cycleW i.1 ^ 2) * ‖Complex.exp (z n) - 1‖ ^ 2
                ≤ cycleH n * ‖z n‖ ^ 3 +
                    C * (2 * ‖z n‖) ^ 2 := by
                    gcongr
            _ = cycleH n * ‖z n‖ ^ 3 + (4 * C) * ‖z n‖ ^ 2 := by ring

lemma cycleCount_aemeasurable (n : ℕ) :
    AEMeasurable (cycleCount n) (cycleP n) := by
  unfold cycleCount cycleP
  exact Finset.aemeasurable_fun_sum _ fun i _ => (measurable_pi_apply i).aemeasurable

/--
Conditional quasi-powers CLT for the Feller coupling cycle-count model.

The only hypothesis is the scaled logarithmic remainder estimate at the
quasi-powers normalization points.
-/
theorem permutationCycles_tendstoInDistribution_gaussian_of_cycleR_tendsto
    (hR : ∀ t, Tendsto
      (fun n : ℕ => (cycleH n : ℂ) * cycleR n (qpZ cycleH 1 n t)) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => (cycleCount n ω - cycleH n) / Real.sqrt (cycleH n)) atTop
      (fun x : ℝ => x) cycleP (gaussianReal 0 1) := by
  simpa using
    (quasiPowers_tendstoInDistribution_of_continuousAt
      (P := cycleP) (X := cycleCount) (β := cycleH)
      (u₁ := 1) (u₂ := 1) (R := cycleR) (V := fun _ : ℂ => 0)
      cycleCount_aemeasurable
      cycleH_tendsto_atTop
      (by norm_num : (0 : ℝ) < 1)
      continuousAt_const
      rfl
      cycle_hChar
      hR)

theorem permutationCycles_tendstoInDistribution_gaussian :
    TendstoInDistribution
      (fun n ω => (cycleCount n ω - cycleH n) / Real.sqrt (cycleH n)) atTop
      (fun x : ℝ => x) cycleP (gaussianReal 0 1) := by
  exact permutationCycles_tendstoInDistribution_gaussian_of_cycleR_tendsto
    cycleR_scaled_tendsto_zero

end LimitLaws
end Ch9
end AnalyticCombinatorics
