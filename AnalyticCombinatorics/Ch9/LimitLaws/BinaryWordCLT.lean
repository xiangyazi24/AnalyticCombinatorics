import Mathlib
import AnalyticCombinatorics.Ch9.LimitLaws.QuasiPowers

/-!
# Binary word counts and the local quasi-powers interface

The one-bit uniform binary-word count has characteristic function zero at `π`.
Consequently it cannot satisfy a global exponential-form `hChar` assumption, whose
right hand side is a complex exponential and therefore never zero.

The binary-word central limit theorem below uses the faithful local interface from
`QuasiPowers.lean`.  We encode bits as signs `-1, 1`; the number of ones in a word is
`(sum of signs + n) / 2`, so the usual count normalization is pointwise equal to the
standardized sign sum.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The uniform measure on one-bit binary words, written as a two-point measure. -/
def oneBitUniform : Measure Bool :=
  ENNReal.ofReal (1 / 2 : ℝ) • (Measure.dirac false + Measure.dirac true)

instance oneBitUniform_isProbabilityMeasure : IsProbabilityMeasure oneBitUniform := by
  rw [oneBitUniform]
  constructor
  simp [ENNReal.inv_two_add_inv_two]

/-- The number of ones in a one-bit binary word. -/
def oneBitCount (b : Bool) : ℝ :=
  if b then 1 else 0

/-- The law of the number of ones in a uniformly random one-bit binary word. -/
def oneBitCountLaw : Measure ℝ :=
  oneBitUniform.map oneBitCount

instance oneBitCountLaw_isProbabilityMeasure : IsProbabilityMeasure oneBitCountLaw :=
  Measure.isProbabilityMeasure_map
    ((by fun_prop : Measurable oneBitCount).aemeasurable)

lemma oneBitCountLaw_eq :
    oneBitCountLaw =
      ENNReal.ofReal (1 / 2 : ℝ) • (Measure.dirac (0 : ℝ) + Measure.dirac (1 : ℝ)) := by
  have hmeas : Measurable oneBitCount := by fun_prop
  rw [oneBitCountLaw, oneBitUniform, Measure.map_smul, Measure.map_add _ _ hmeas,
    Measure.map_dirac' hmeas, Measure.map_dirac' hmeas]
  simp [oneBitCount]

/-- The one-bit binary-word count has a zero of its characteristic function at `π`. -/
theorem oneBitCountLaw_charFun_pi :
    charFun oneBitCountLaw Real.pi = 0 := by
  rw [oneBitCountLaw_eq, charFun_apply_real]
  have h0 : Integrable (fun x : ℝ => Complex.exp (Real.pi * x * Complex.I))
      (Measure.dirac (0 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (0 : ℝ))
        (f := fun x : ℝ => Complex.exp (Real.pi * x * Complex.I)) (by simp))
  have h1 : Integrable (fun x : ℝ => Complex.exp (Real.pi * x * Complex.I))
      (Measure.dirac (1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (1 : ℝ))
        (f := fun x : ℝ => Complex.exp (Real.pi * x * Complex.I)) (by simp))
  rw [integral_smul_measure, integral_add_measure h0 h1, integral_dirac, integral_dirac]
  simp [Complex.exp_pi_mul_I]

/-- No global exponential representation can be the characteristic function of the one-bit count. -/
theorem oneBitCountLaw_no_global_exponential_charFun {F : ℝ → ℂ}
    (hF : ∀ s : ℝ, charFun oneBitCountLaw s = Complex.exp (F s)) :
    False := by
  have hzero : Complex.exp (F Real.pi) = 0 := by
    simpa [oneBitCountLaw_charFun_pi] using (hF Real.pi).symm
  exact Complex.exp_ne_zero (F Real.pi) hzero

/--
The current quasi-powers `hChar` shape is a global exponential representation.
Thus it cannot be instantiated for the one-bit uniform binary-word count.
-/
theorem oneBitCountLaw_no_quasiPowers_hChar
    {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}
    (hChar : ∀ n s,
      charFun oneBitCountLaw s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ)))) :
    False :=
  oneBitCountLaw_no_global_exponential_charFun
    (F := fun s =>
      (β 0 : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
        (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R 0 (Complex.I * (s : ℂ))) +
        V (Complex.I * (s : ℂ)))
    (fun s => hChar 0 s)

/-- The one-bit sign law, using `-1` for zero and `1` for one. -/
def oneBitSignLaw : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ))

instance oneBitSignLaw_isProbabilityMeasure : IsProbabilityMeasure oneBitSignLaw := by
  rw [oneBitSignLaw]
  constructor
  simp [ENNReal.inv_two_add_inv_two]

/-- Characteristic function of one sign bit. -/
lemma oneBitSignLaw_charFun (s : ℝ) :
    charFun oneBitSignLaw s =
      (Complex.exp (-((s : ℂ) * Complex.I)) + Complex.exp ((s : ℂ) * Complex.I)) / 2 := by
  rw [oneBitSignLaw, charFun_apply_real]
  have hm : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (-1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (-1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  have hp : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I))
      (Measure.dirac (1 : ℝ)) := by
    simpa using
      (integrable_dirac (a := (1 : ℝ))
        (f := fun x : ℝ => Complex.exp (s * x * Complex.I)) (by simp))
  rw [integral_smul_measure, integral_add_measure hm hp, integral_dirac, integral_dirac]
  have hto : (ENNReal.ofReal (1 / 2 : ℝ)).toReal = (2 : ℝ)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hto]
  simp
  change ((2 : ℝ)⁻¹) • Complex.exp (-((s : ℂ) * Complex.I)) +
      ((2 : ℝ)⁻¹) • Complex.exp ((s : ℂ) * Complex.I) =
    (Complex.exp (-((s : ℂ) * Complex.I)) + Complex.exp ((s : ℂ) * Complex.I)) / 2
  apply Complex.ext <;> simp <;> ring_nf

lemma oneBitSignLaw_integral_id :
    oneBitSignLaw[(fun x : ℝ => x)] = 0 := by
  rw [oneBitSignLaw]
  have hm : Integrable (fun x : ℝ => x) (Measure.dirac (-1 : ℝ)) := by
    simpa using (integrable_dirac (a := (-1 : ℝ)) (f := fun x : ℝ => x) (by simp))
  have hp : Integrable (fun x : ℝ => x) (Measure.dirac (1 : ℝ)) := by
    simpa using (integrable_dirac (a := (1 : ℝ)) (f := fun x : ℝ => x) (by simp))
  rw [integral_smul_measure, integral_add_measure hm hp, integral_dirac, integral_dirac]
  have hto : (ENNReal.ofReal (1 / 2 : ℝ)).toReal = (2 : ℝ)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hto]
  norm_num [smul_eq_mul]

lemma oneBitSignLaw_integral_sq :
    oneBitSignLaw[(fun x : ℝ => x ^ 2)] = 1 := by
  rw [oneBitSignLaw]
  have hm : Integrable (fun x : ℝ => x ^ 2) (Measure.dirac (-1 : ℝ)) := by
    simpa using (integrable_dirac (a := (-1 : ℝ)) (f := fun x : ℝ => x ^ 2) (by simp))
  have hp : Integrable (fun x : ℝ => x ^ 2) (Measure.dirac (1 : ℝ)) := by
    simpa using (integrable_dirac (a := (1 : ℝ)) (f := fun x : ℝ => x ^ 2) (by simp))
  rw [integral_smul_measure, integral_add_measure hm hp, integral_dirac, integral_dirac]
  have hto : (ENNReal.ofReal (1 / 2 : ℝ)).toReal = (2 : ℝ)⁻¹ := by
    rw [ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hto]
  norm_num [smul_eq_mul]

/-- Binary words of length `n`, sign-coded as coordinates in `{-1, 1}`. -/
abbrev Ω (n : ℕ) := Fin n → ℝ

/-- Product measure for a uniform sign-coded binary word. -/
def P (n : ℕ) : Measure (Ω n) :=
  Measure.pi (fun _ : Fin n => oneBitSignLaw)

instance P_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (P n) := by
  unfold P
  infer_instance

/-- Sum of signs in a sign-coded binary word. -/
def S (n : ℕ) (ω : Ω n) : ℝ :=
  ∑ i, ω i

/-- Number of ones in a sign-coded binary word. -/
def X (n : ℕ) (ω : Ω n) : ℝ :=
  (S n ω + n) / 2

/-- The sign-bit characteristic base. -/
def signBase (z : ℂ) : ℂ :=
  (Complex.exp (-z) + Complex.exp z) / 2

/-- The quadratic quasi-powers main term for a sign bit. -/
def signMain (z : ℂ) : ℂ :=
  z ^ 2 / 2

/-- Exact local logarithmic remainder for sign-coded binary words. -/
def signR (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    Complex.log (signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)) / (n : ℂ)

lemma signSum_charFun (n : ℕ) (s : ℝ) :
    charFun ((P n).map (S n)) s = (signBase (Complex.I * (s : ℂ))) ^ n := by
  change charFun ((Measure.pi fun _ : Fin n => oneBitSignLaw).map (fun p => ∑ i, p i)) s =
    (signBase (Complex.I * (s : ℂ))) ^ n
  have h := congrFun (charFun_map_sum_pi_eq_prod (μ := fun _ : Fin n => oneBitSignLaw)) s
  rw [h]
  simp [oneBitSignLaw_charFun, signBase, Finset.prod_const, Fintype.card_fin, div_pow, mul_comm]

lemma signBase_ne_zero_of_abs_le_half {s : ℝ} (hs : |s| ≤ (1 / 2 : ℝ)) :
    signBase (Complex.I * (s : ℂ)) ≠ 0 := by
  intro hzero
  have hnum : Complex.exp (-(Complex.I * (s : ℂ))) +
      Complex.exp (Complex.I * (s : ℂ)) = 0 := by
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact h
    · norm_num at h
  have hmul := congrArg (fun w : ℂ => w * Complex.exp (Complex.I * (s : ℂ))) hnum
  simp only [add_mul, zero_mul] at hmul
  have hne : Complex.exp (Complex.I * (s : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hexp2 : Complex.exp (2 * (Complex.I * (s : ℂ))) = -1 := by
    rw [Complex.exp_neg, inv_mul_cancel₀ hne] at hmul
    rw [← Complex.exp_add] at hmul
    have harg : Complex.I * (s : ℂ) + Complex.I * (s : ℂ) =
        2 * (Complex.I * (s : ℂ)) := by
      ring
    rw [harg] at hmul
    linear_combination hmul
  have hdiff : Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1 = -2 := by
    rw [show Complex.I * ((2 * s : ℝ) : ℂ) = 2 * (Complex.I * (s : ℂ)) by
      norm_num
      ring]
    rw [hexp2]
    norm_num
  have hnorm_eq : ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ = 2 := by
    rw [hdiff]
    norm_num
  have hle : ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ ≤ ‖2 * s‖ := by
    simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * s))
  have htwo_le_one : (2 : ℝ) ≤ 1 := by
    calc
      (2 : ℝ) = ‖Complex.exp (Complex.I * ((2 * s : ℝ) : ℂ)) - 1‖ := hnorm_eq.symm
      _ ≤ ‖2 * s‖ := hle
      _ = |2 * s| := Real.norm_eq_abs (2 * s)
      _ = 2 * |s| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (1 / 2 : ℝ) := by gcongr
      _ = 1 := by norm_num
  norm_num at htwo_le_one

lemma sign_hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
    charFun ((P n).map (S n)) s =
      Complex.exp (((n : ℝ) : ℂ) * (((0 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) +
        ((1 : ℝ) : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 +
        signR n (Complex.I * (s : ℂ))) + (0 : ℂ)) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  intro n s hs
  rw [signSum_charFun]
  by_cases hn : n = 0
  · subst n
    simp [signR]
  · let z : ℂ := Complex.I * (s : ℂ)
    let ratio : ℂ := signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)
    have hbase : signBase z ≠ 0 := signBase_ne_zero_of_abs_le_half (s := s) hs
    have hratio : ratio ≠ 0 := by
      dsimp [ratio]
      exact mul_ne_zero (pow_ne_zero n hbase) (Complex.exp_ne_zero _)
    change signBase z ^ n =
      Complex.exp (((n : ℂ) * ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + signR n z) + 0))
    rw [signR, if_neg hn]
    change signBase z ^ n =
      Complex.exp (((n : ℂ) *
        ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + Complex.log ratio / (n : ℂ)) + 0))
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [show ((n : ℂ) *
        ((0 : ℂ) * z + (1 : ℂ) * z ^ 2 / 2 + Complex.log ratio / (n : ℂ)) + 0) =
        (n : ℂ) * (z ^ 2 / 2) + Complex.log ratio by
      field_simp [hnC]
      ring]
    change signBase z ^ n = Complex.exp ((n : ℂ) * signMain z + Complex.log ratio)
    rw [Complex.exp_add, Complex.exp_log hratio]
    dsimp [ratio]
    rw [show Complex.exp ((n : ℂ) * signMain z) *
        (signBase z ^ n * Complex.exp (-(n : ℂ) * signMain z)) =
        signBase z ^ n *
          (Complex.exp ((n : ℂ) * signMain z) *
            Complex.exp (-(n : ℂ) * signMain z)) by
      ring]
    rw [← Complex.exp_add]
    rw [show (n : ℂ) * signMain z + (-(n : ℂ) * signMain z) = 0 by ring]
    simp

lemma oneBitSignLaw_charFun_signBase (s : ℝ) :
    charFun oneBitSignLaw s = signBase (Complex.I * (s : ℂ)) := by
  rw [oneBitSignLaw_charFun]
  simp [signBase, mul_comm]

lemma signRatio_tendsto_one (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) ^ n *
          Complex.exp (-(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)))
      atTop (𝓝 1) := by
  have hclt :
      Tendsto (fun n : ℕ => (charFun oneBitSignLaw ((√n)⁻¹ * t)) ^ n)
        atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
    simpa [Pi.pow_apply] using ProbabilityTheory.tendsto_charFun_inv_sqrt_mul_pow
      (P := oneBitSignLaw) (X := fun x : ℝ => x) (by fun_prop)
      oneBitSignLaw_integral_id oneBitSignLaw_integral_sq t
  have htarget :
      Tendsto
        (fun n : ℕ => (charFun oneBitSignLaw ((√n)⁻¹ * t)) ^ n *
          Complex.exp ((t : ℂ) ^ 2 / 2)) atTop (𝓝 1) := by
    have hmul := hclt.mul_const (Complex.exp ((t : ℂ) ^ 2 / 2))
    have hlim :
        Complex.exp (-(t : ℂ) ^ 2 / 2) * Complex.exp ((t : ℂ) ^ 2 / 2) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      simp
    simpa [hlim] using hmul
  refine Tendsto.congr' ?_ htarget
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase :
      signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        charFun oneBitSignLaw ((√n)⁻¹ * t) := by
    rw [oneBitSignLaw_charFun_signBase]
    simp [qpZ]
  have hmain :
      (n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        - (t : ℂ) ^ 2 / 2 := by
    have hquad := quasiPower_quadratic_term (β := (n : ℝ)) (u₂ := 1) (t := t) hnpos
      (by norm_num : (0 : ℝ) < 1)
    simpa [qpZ, signMain] using hquad
  rw [hbase]
  have hnegmain :
      -(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) =
        (t : ℂ) ^ 2 / 2 := by
    calc
      -(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)
          = -((n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t)) := by ring
      _ = (t : ℂ) ^ 2 / 2 := by
        rw [hmain]
        ring
  rw [hnegmain]

lemma signR_tendsto :
    ∀ t, Tendsto
      (fun n : ℕ =>
        ((n : ℝ) : ℂ) * signR n (qpZ (fun n : ℕ => (n : ℝ)) 1 n t))
      atTop (𝓝 0) := by
  intro t
  have hratio := signRatio_tendsto_one t
  have hlog :
      Tendsto
        (fun n : ℕ => Complex.log
          (signBase (qpZ (fun n : ℕ => (n : ℝ)) 1 n t) ^ n *
            Complex.exp (-(n : ℂ) * signMain (qpZ (fun n : ℕ => (n : ℝ)) 1 n t))))
        atTop (𝓝 0) := by
    simpa using hratio.clog (by simp [Complex.slitPlane] : (1 : ℂ) ∈ Complex.slitPlane)
  refine Tendsto.congr' ?_ hlog
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [signR, hn]
  field_simp [hnC]

theorem binaryWord_signSum_tendstoInDistribution_gaussian :
    TendstoInDistribution
      (fun n ω => (S n ω - (n : ℝ) * 0) / Real.sqrt ((n : ℝ) * 1)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) :=
  quasiPowers_tendstoInDistribution_of_continuousAt
    (P := P) (X := S) (β := fun n : ℕ => (n : ℝ)) (u₁ := 0) (u₂ := 1)
    (R := signR) (V := fun _ : ℂ => 0)
    (by
      intro n
      unfold S
      exact Finset.aemeasurable_fun_sum _ fun i _ => (measurable_pi_apply i).aemeasurable)
    tendsto_natCast_atTop_atTop
    (by norm_num)
    continuousAt_const
    rfl
    sign_hChar
    signR_tendsto

lemma normalized_count_eq_sign (n : ℕ) (ω : Ω n) :
    (X n ω - (n : ℝ) * (1 / 2)) / Real.sqrt ((n : ℝ) * (1 / 4)) =
      (S n ω - (n : ℝ) * 0) / Real.sqrt ((n : ℝ) * 1) := by
  by_cases hn : n = 0
  · subst n
    simp [X, S]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
    have hsqrt :
        Real.sqrt ((n : ℝ) * (1 / 4)) = Real.sqrt (n : ℝ) / 2 := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ)) (1 / 4 : ℝ)]
      norm_num
      ring
    rw [X, hsqrt]
    field_simp [hsqrt_ne]
    ring

/-- The number of ones in a uniform binary word satisfies the standard Gaussian CLT. -/
theorem binaryWord_symbolCount_tendstoInDistribution_gaussian :
    TendstoInDistribution
      (fun n ω => (X n ω - (n : ℝ) * (1 / 2)) / Real.sqrt ((n : ℝ) * (1 / 4))) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) := by
  refine TendstoInDistribution.congr ?_ (ae_of_all _ fun _ => rfl)
    binaryWord_signSum_tendstoInDistribution_gaussian
  intro n
  exact ae_of_all _ fun ω => (normalized_count_eq_sign n ω).symm

end LimitLaws
end Ch9
end AnalyticCombinatorics
