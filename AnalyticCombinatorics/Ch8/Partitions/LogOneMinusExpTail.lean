import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.LogHeadAssembly

/-!
# Tail calculus + summability for `log1mexp` (HR constant, brick 2 tail)

Self-contained foundation for the exponential-tail trapezoid (ChatGPT R8):
derivative/second-derivative exp-decay bounds, geometric sum, tail integrability,
sample summability, and the `O(t)` geometric error. The infinite-cell trapezoid
summation + final tail theorem build on these.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology BigOperators MeasureTheory Real
open scoped Topology BigOperators Interval

noncomputable section

/-- Derivative of `log1mexp` in tail form: `log1mexp'(x) = -1/(e^x - 1)`. -/
lemma log1mexp_hasDerivAt_tail {x : ℝ} (hx : 0 < x) :
    HasDerivAt log1mexp (-(1 / (Real.exp x - 1))) x := by
  have h := log1mexp_hasDerivAt hx
  convert h using 1
  rw [Real.exp_neg]
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have hden : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  field_simp

/-- `(-1/(e^x-1))' = e^x/(e^x-1)²`. -/
lemma log1mexpDeriv_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -(1 / (Real.exp y - 1)))
      (Real.exp x / (Real.exp x - 1) ^ 2) x := by
  have hden_deriv : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).sub_const 1
  have hden_ne : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx).ne'
  have hneg := (hden_deriv.inv hden_ne).neg
  simp only [one_div]
  convert hneg using 1
  ring

/-- Second-derivative tail bound: `|e^x/(e^x-1)²| ≤ 4 e^{-x}` for `x ≥ log 2`. -/
lemma log1mexp_second_deriv_tail_bound {x : ℝ} (hx : Real.log 2 ≤ x) :
    |Real.exp x / (Real.exp x - 1) ^ 2| ≤ 4 * Real.exp (-x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hx
  have he2 : 2 ≤ Real.exp x := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have hden_half : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith
  have hden_pos : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hden_sq : (Real.exp x / 2) ^ 2 ≤ (Real.exp x - 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hden_half 2
  have hmain : Real.exp x / (Real.exp x - 1) ^ 2 ≤ Real.exp x / ((Real.exp x / 2) ^ 2) :=
    div_le_div₀ (by positivity) le_rfl (by positivity) hden_sq
  have hsimp : Real.exp x / ((Real.exp x / 2) ^ 2) = 4 * Real.exp (-x) := by
    rw [Real.exp_neg]; field_simp [Real.exp_ne_zero x]; ring
  rw [abs_of_pos (by positivity : 0 < Real.exp x / (Real.exp x - 1) ^ 2)]
  exact hmain.trans_eq hsimp

/-- `∑_j e^{-(a+h·j)} = e^{-a}/(1-e^{-h})`. -/
lemma exp_tail_geometric_bound {a h : ℝ} (hh : 0 < h) :
    (∑' j : ℕ, Real.exp (-(a + h * (j : ℝ)))) = Real.exp (-a) / (1 - Real.exp (-h)) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hcongr : (fun j : ℕ => Real.exp (-(a + h * (j : ℝ))))
      = fun j : ℕ => Real.exp (-a) * (Real.exp (-h)) ^ j := by
    funext j
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- For `0 < h ≤ 1`, `1 - e^{-h} ≥ h/2`. -/
lemma one_sub_exp_neg_ge_half {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    h / 2 ≤ 1 - Real.exp (-h) := by
  have hexp_le : Real.exp (-h) ≤ 1 / (1 + h) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp h])
  have h1h : (1 : ℝ) + h ≠ 0 := by positivity
  have hbase : 1 - 1 / (1 + h) = h / (1 + h) := by field_simp; ring
  have hhalf : h / 2 ≤ h / (1 + h) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : (0 : ℝ) < 1 + h)]; nlinarith
  linarith

/-- `log1mexp` is integrable on a tail `Ioi a` (`a ≥ log 2`). -/
lemma log1mexp_integrableOn_Ioi_tail {a : ℝ} (ha : Real.log 2 ≤ a) :
    IntegrableOn log1mexp (Set.Ioi a) := by
  have hmeas : AEStronglyMeasurable log1mexp (volume.restrict (Set.Ioi a)) := by
    apply Measurable.aestronglyMeasurable
    unfold log1mexp
    exact (Real.measurable_log.comp
      (measurable_const.sub (Real.measurable_exp.comp measurable_neg))).neg
  have hdom : IntegrableOn (fun x : ℝ => 2 * Real.exp (-x)) (Set.Ioi a) := by
    have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi a) := by
      simpa [one_mul] using exp_neg_integrableOn_Ioi a one_pos
    exact hbase.const_mul 2
  apply Integrable.mono' hdom hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact log1mexp_tail_bound (le_trans ha hx.le)

/-- Tail samples are summable. -/
lemma summable_log1mexp_tail_samples {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Summable (fun j : ℕ => log1mexp (a + h * ((j + 1 : ℕ) : ℝ))) := by
  have hr0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hr1 : Real.exp (-h) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo : Summable (fun j : ℕ => 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_norm_bounded hgeo ?_
  intro j
  have hx : Real.log 2 ≤ a + h * ((j + 1 : ℕ) : ℝ) := by
    have hnon : 0 ≤ h * ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  rw [Real.norm_eq_abs]
  calc |log1mexp (a + h * ((j + 1 : ℕ) : ℝ))|
        ≤ 2 * Real.exp (-(a + h * ((j + 1 : ℕ) : ℝ))) := log1mexp_tail_bound hx
    _ = 2 * Real.exp (-(a + h)) * (Real.exp (-h)) ^ j := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring

/-- Tail samples tend to zero. -/
lemma log1mexp_tail_samples_tendsto_zero {a h : ℝ} (ha : Real.log 2 ≤ a) (hh : 0 < h) :
    Tendsto (fun n : ℕ => log1mexp (a + h * (n : ℝ))) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => a + h * (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop a (tendsto_natCast_atTop_atTop.const_mul_atTop hh)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖log1mexp (a + h * (n : ℝ))‖ ≤ 2 * Real.exp (-(a + h * (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop 0] with n _hn
    have hxge : Real.log 2 ≤ a + h * (n : ℝ) := by
      have hnon : 0 ≤ h * (n : ℝ) := by positivity
      linarith
    rw [Real.norm_eq_abs]
    exact log1mexp_tail_bound hxge
  have hzero : Tendsto (fun n : ℕ => 2 * Real.exp (-(a + h * (n : ℝ)))) atTop (𝓝 0) := by
    have hreal : Tendsto (fun x : ℝ => 2 * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2
    exact hreal.comp hx
  exact squeeze_zero_norm' hbound hzero

/-- The geometric tail error bound is `O(t) → 0`. -/
lemma tail_geometric_error_tendsto_zero :
    Tendsto (fun t : ℝ => (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖(4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))‖ ≤ 8 * t := by
    filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with t ht ht1
    have htpos : 0 < t := ht
    have htle : t ≤ 1 := le_of_lt ht1
    have hden : t / 2 ≤ 1 - Real.exp (-t) := one_sub_exp_neg_ge_half htpos htle
    have hdenpos : 0 < 1 - Real.exp (-t) := by linarith
    have hexp_le_one : Real.exp (-(trapR t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hRnn : 0 ≤ trapR t := by rw [trapR]; positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (4 : ℝ) * t ^ 2 * (Real.exp (-(trapR t)) / (1 - Real.exp (-t)))
          ≤ 4 * t ^ 2 * (1 / (t / 2)) := by gcongr
      _ = 8 * t := by field_simp; ring
  have ht : Tendsto (fun t : ℝ => 8 * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using h0.const_mul (8 : ℝ)
  exact squeeze_zero_norm' hbound ht

end

end AnalyticCombinatorics.Ch8.Partitions
