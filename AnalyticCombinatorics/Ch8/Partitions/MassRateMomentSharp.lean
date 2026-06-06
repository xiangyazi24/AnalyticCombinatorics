import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound

/-!
# Mass-rate campaign: the sharp moment bound `M_r(t) ≤ K_r/t^{r+2}`

The true leading order of `M_r(t) = Σ_m m^r σ(m) e^{−tm}` is `(r+1)!·ζ(2)/t^{r+2}`, sharper by
`1/t` than the crude `σ(m) ≤ m²` bound (`/t^{r+3}`).  Needed for the §5 `kernelMass_sub_approx2`
error terms (`M₃`, `M₄`).

Route: weighted divisor Fubini `M_r = Σ_a Σ_b a^{r+1} b^r ρ^{ab}` (ρ = e^{−t}), via
`_root_.sigmaAntidiagonalEquivProd` (`Σ_{ab=e} a^{r+1} b^r = e^r σ(e)`); the summand is dominated by
`ρ^{−1}·(a^{r+1}ρ^a)(b^r ρ^b)` (since `ab ≥ a+b−1`).  Opus-authored.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset ArithmeticFunction
open scoped BigOperators Topology ArithmeticFunction.sigma

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- The weighted antidiagonal summand is summable over `ℕ+ × ℕ+` (`0 ≤ ρ < 1`). -/
lemma summable_weighted_antidiag (r : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun c : ℕ+ × ℕ+ =>
      ((c.1 : ℕ) : ℝ) ^ (r + 1) * ((c.2 : ℕ) : ℝ) ^ r * ρ ^ ((c.1 : ℕ) * (c.2 : ℕ))) := by
  have hρn : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hρ0]
  -- dominator g(a)·h(b) with g a = ρ⁻¹·a^{r+1}ρ^a, h b = b^r ρ^b
  have hg : Summable (fun a : ℕ+ => ρ⁻¹ * (((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ))) :=
    (((summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r + 1) hρn).comp_injective
      PNat.coe_injective)).mul_left _
  have hh : Summable (fun b : ℕ+ => ((b : ℕ) : ℝ) ^ r * ρ ^ (b : ℕ)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) r hρn).comp_injective PNat.coe_injective
  have hprod : Summable (fun c : ℕ+ × ℕ+ =>
      (ρ⁻¹ * (((c.1 : ℕ) : ℝ) ^ (r + 1) * ρ ^ (c.1 : ℕ)))
        * (((c.2 : ℕ) : ℝ) ^ r * ρ ^ (c.2 : ℕ))) :=
    hg.mul_of_nonneg hh (fun a => by positivity) (fun b => by positivity)
  refine Summable.of_nonneg_of_le (fun c => by positivity) (fun c => ?_) hprod
  -- ρ^{ab} ≤ ρ^{a+b-1}, so a^{r+1}b^r ρ^{ab} ≤ ρ^{-1} a^{r+1}ρ^a b^r ρ^b
  have hab : (c.1 : ℕ) + (c.2 : ℕ) ≤ (c.1 : ℕ) * (c.2 : ℕ) + 1 := by
    have h1 : 0 < (c.1 : ℕ) := c.1.pos
    have h2 : 0 < (c.2 : ℕ) := c.2.pos
    nlinarith [h1, h2]
  have hpow : ρ ^ ((c.1 : ℕ) * (c.2 : ℕ)) ≤ ρ ^ ((c.1 : ℕ) + (c.2 : ℕ) - 1) := by
    apply pow_le_pow_of_le_one hρ0.le hρ1.le
    omega
  have hexp : ρ ^ ((c.1 : ℕ) + (c.2 : ℕ) - 1) = ρ⁻¹ * (ρ ^ (c.1 : ℕ) * ρ ^ (c.2 : ℕ)) := by
    have hc1 : 0 < (c.1 : ℕ) := c.1.pos
    have h1 : 1 ≤ (c.1 : ℕ) + (c.2 : ℕ) := by omega
    rw [← pow_add, inv_mul_eq_div, eq_div_iff hρ0.ne', ← pow_succ, Nat.sub_add_cancel h1]
  calc ((c.1 : ℕ) : ℝ) ^ (r + 1) * ((c.2 : ℕ) : ℝ) ^ r * ρ ^ ((c.1 : ℕ) * (c.2 : ℕ))
      ≤ ((c.1 : ℕ) : ℝ) ^ (r + 1) * ((c.2 : ℕ) : ℝ) ^ r * ρ ^ ((c.1 : ℕ) + (c.2 : ℕ) - 1) := by
        apply mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (ρ⁻¹ * (((c.1 : ℕ) : ℝ) ^ (r + 1) * ρ ^ (c.1 : ℕ)))
          * (((c.2 : ℕ) : ℝ) ^ r * ρ ^ (c.2 : ℕ)) := by rw [hexp]; ring


/-- **Weighted divisor Fubini**: `M_r(t) = Σ_a Σ_b a^{r+1} b^r (e^{−t})^{ab}`. -/
lemma sigmaMoment_eq_prod_tsum (r : ℕ) {t : ℝ} (ht : 0 < t) :
    sigmaMoment r t
      = ∑' a : ℕ+, ∑' b : ℕ+,
          ((a : ℕ) : ℝ) ^ (r + 1) * ((b : ℕ) : ℝ) ^ r * (Real.exp (-t)) ^ ((a : ℕ) * (b : ℕ)) := by
  set ρ : ℝ := Real.exp (-t) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρdef, Real.exp_lt_one_iff]; linarith
  have hsumm := summable_weighted_antidiag r hρ0 hρ1
  -- LHS in ℕ+ σ-form
  have hrm : ∀ m : ℕ, Real.exp (-t * (m : ℝ)) = ρ ^ m := by
    intro m; rw [hρdef, ← Real.exp_nat_mul]; congr 1; ring
  have hL : sigmaMoment r t
      = ∑' e : ℕ+, ((e : ℕ) : ℝ) ^ r * ((ArithmeticFunction.sigma 1 (e : ℕ) : ℕ) : ℝ)
          * ρ ^ (e : ℕ) := by
    rw [sigmaMoment, tsum_if_ne_zero_eq_pnat
      (f := fun m : ℕ => (m : ℝ) ^ r * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))]
    refine tsum_congr fun e => ?_
    rw [sigmaR_eq_sigma_one, hrm]
  rw [hL, ← hsumm.tsum_prod]
  -- reindex Σ_{(a,b)} F = Σ_e [Σ_{x∈antidiag e} F(factors)]
  rw [← Equiv.tsum_eq _root_.sigmaAntidiagonalEquivProd
    (fun c : ℕ+ × ℕ+ => ((c.1 : ℕ) : ℝ) ^ (r + 1) * ((c.2 : ℕ) : ℝ) ^ r * ρ ^ ((c.1 : ℕ) * (c.2 : ℕ)))]
  have hg : Summable (fun c : Σ n : ℕ+, ↥((n : ℕ).divisorsAntidiagonal) =>
      ((((_root_.sigmaAntidiagonalEquivProd c).1 : ℕ) : ℝ)) ^ (r + 1)
        * ((((_root_.sigmaAntidiagonalEquivProd c).2 : ℕ) : ℝ)) ^ r
        * ρ ^ (((_root_.sigmaAntidiagonalEquivProd c).1 : ℕ) * ((_root_.sigmaAntidiagonalEquivProd c).2 : ℕ))) :=
    (Equiv.summable_iff _root_.sigmaAntidiagonalEquivProd).mpr hsumm
  rw [hg.tsum_sigma]
  unfold _root_.sigmaAntidiagonalEquivProd _root_.divisorsAntidiagonalFactors
  simp only [Equiv.coe_fn_mk, PNat.mk_coe]
  refine (tsum_congr fun e => ?_).symm
  -- Σ_{x∈antidiag e} x.1^{r+1} x.2^r ρ^{x.1·x.2} = e^r σ(e) ρ^e
  rw [tsum_fintype]
  rw [Finset.sum_coe_sort (e : ℕ).divisorsAntidiagonal
    (fun x : ℕ × ℕ => ((x.1 : ℝ)) ^ (r + 1) * ((x.2 : ℝ)) ^ r * ρ ^ (x.1 * x.2))]
  rw [@Nat.sum_divisorsAntidiagonal ℝ _
    (fun a b => ((a : ℝ)) ^ (r + 1) * ((b : ℝ)) ^ r * ρ ^ (a * b)) (e : ℕ)]
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  rw [show ((e : ℕ) : ℝ) ^ r * (∑ d ∈ (e : ℕ).divisors, (d : ℝ)) * ρ ^ (e : ℕ)
      = ∑ d ∈ (e : ℕ).divisors, ((e : ℕ) : ℝ) ^ r * (d : ℝ) * ρ ^ (e : ℕ) from by
    rw [Finset.mul_sum, Finset.sum_mul]]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ (e : ℕ) := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdc : d * ((e : ℕ) / d) = (e : ℕ) := Nat.mul_div_cancel' hdvd
  rw [hdc]
  -- d^{r+1} (e/d)^r ρ^e = (e/d) * (e^r ρ^e)? want = e^r * d * ρ^e summed... per-term: d^{r+1}(e/d)^r = e^r·d
  have hkey : ((d : ℝ)) ^ (r + 1) * (((e : ℕ) / d : ℕ) : ℝ) ^ r
      = ((e : ℕ) : ℝ) ^ r * (d : ℝ) := by
    have hediv : (((e : ℕ) / d : ℕ) : ℝ) = ((e : ℕ) : ℝ) / (d : ℝ) := by
      rw [Nat.cast_div hdvd (by exact_mod_cast hd0.ne')]
    rw [hediv, div_pow, pow_succ]
    field_simp
  rw [hkey]

/-- Inner geometric bound (with the `x`-decay factor): `Σ'_{b≥1} b^r x^b ≤ x·2^r(r!+1)/(1−x)^{r+1}`
for `0 ≤ x < 1`. -/
lemma tsum_pnat_pow_mul_geometric_le (r : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' b : ℕ+, ((b : ℕ) : ℝ) ^ r * x ^ (b : ℕ))
      ≤ x * (2 ^ r * (Nat.factorial r + 1)) / (1 - x) ^ (r + 1) := by
  have hxn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1mx : (0:ℝ) < 1 - x := by linarith
  -- Σ'_{b:ℕ+} b^r x^b = x · Σ'_{c:ℕ} (c+1)^r x^c
  have hstep : (∑' b : ℕ+, ((b : ℕ) : ℝ) ^ r * x ^ (b : ℕ))
      = x * ∑' c : ℕ, ((c : ℝ) + 1) ^ r * x ^ c := by
    rw [tsum_pnat_eq_tsum_succ (f := fun b : ℕ => ((b : ℝ)) ^ r * x ^ b)]
    rw [← tsum_mul_left]
    refine tsum_congr fun c => ?_
    push_cast
    rw [pow_succ]
    ring
  rw [hstep]
  -- Σ_c (c+1)^r x^c ≤ 2^r(r!+1)/(1-x)^{r+1}
  have hcr : Summable (fun c : ℕ => (c : ℝ) ^ r * x ^ c) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) r hxn
  have hgeo : Summable (fun c : ℕ => x ^ c) := summable_geometric_of_lt_one hx0 hx1
  have hterm : ∀ c : ℕ, ((c : ℝ) + 1) ^ r * x ^ c
      ≤ 2 ^ r * ((c : ℝ) ^ r * x ^ c) + 2 ^ r * x ^ c := by
    intro c
    have hxc : (0:ℝ) ≤ x ^ c := by positivity
    have hcr1 : ((c : ℝ) + 1) ^ r ≤ 2 ^ r * ((c : ℝ) ^ r + 1) := by
      have h2 : (c : ℝ) + 1 ≤ 2 * max (c : ℝ) (1:ℝ) := by
        rcases le_or_gt (c : ℝ) 1 with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h.le]; linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ (c:ℝ))]
      calc ((c : ℝ) + 1) ^ r ≤ (2 * max (c : ℝ) (1:ℝ)) ^ r := by gcongr
        _ = 2 ^ r * (max (c : ℝ) (1:ℝ)) ^ r := by rw [mul_pow]
        _ ≤ 2 ^ r * ((c : ℝ) ^ r + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rcases le_or_gt (c : ℝ) 1 with h | h
            · rw [max_eq_right h]; simp only [one_pow]
              linarith [pow_nonneg (Nat.cast_nonneg c : (0:ℝ) ≤ (c:ℝ)) r]
            · rw [max_eq_left h.le]
              nlinarith [pow_nonneg (Nat.cast_nonneg c : (0:ℝ) ≤ (c:ℝ)) r]
    calc ((c : ℝ) + 1) ^ r * x ^ c ≤ (2 ^ r * ((c : ℝ) ^ r + 1)) * x ^ c :=
          mul_le_mul_of_nonneg_right hcr1 hxc
      _ = 2 ^ r * ((c : ℝ) ^ r * x ^ c) + 2 ^ r * x ^ c := by ring
  have hdom : Summable (fun c : ℕ => 2 ^ r * ((c : ℝ) ^ r * x ^ c) + 2 ^ r * x ^ c) :=
    (hcr.mul_left _).add (hgeo.mul_left _)
  have hsummC : Summable (fun c : ℕ => ((c : ℝ) + 1) ^ r * x ^ c) :=
    Summable.of_nonneg_of_le (fun c => by positivity) hterm hdom
  have hbnd : (∑' c : ℕ, ((c : ℝ) + 1) ^ r * x ^ c)
      ≤ (2 ^ r * (Nat.factorial r + 1)) / (1 - x) ^ (r + 1) := by
    have hmono := hsummC.tsum_le_tsum hterm hdom
    refine hmono.trans ?_
    rw [(hcr.mul_left _).tsum_add (hgeo.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one hx0 hx1]
    have hpbnd := tsum_pow_mul_geometric_le r hx0 hx1
    have hpow_le : (1 - x) ^ (r + 1) ≤ 1 - x := by
      calc (1 - x) ^ (r + 1) ≤ (1 - x) ^ 1 :=
            pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
        _ = 1 - x := pow_one _
    have hinv : (1 - x)⁻¹ ≤ 1 / (1 - x) ^ (r + 1) := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hpow_le
    have hpbnd' : (∑' c : ℕ, (c : ℝ) ^ r * x ^ c) ≤ (Nat.factorial r : ℝ) / (1 - x) ^ (r + 1) :=
      hpbnd
    have hfr : (0:ℝ) ≤ (2:ℝ) ^ r := by positivity
    have he1 : (2:ℝ) ^ r * (∑' c : ℕ, (c : ℝ) ^ r * x ^ c)
        ≤ 2 ^ r * ((Nat.factorial r : ℝ) / (1 - x) ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left hpbnd' hfr
    have he2 : (2:ℝ) ^ r * (1 - x)⁻¹ ≤ 2 ^ r * (1 / (1 - x) ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left hinv hfr
    have hcombine : 2 ^ r * ((Nat.factorial r : ℝ) / (1 - x) ^ (r + 1))
        + 2 ^ r * (1 / (1 - x) ^ (r + 1))
        = (2 ^ r * (Nat.factorial r + 1)) / (1 - x) ^ (r + 1) := by
      field_simp
    linarith [he1, he2, hcombine.le, hcombine.ge]
  calc x * ∑' c : ℕ, ((c : ℝ) + 1) ^ r * x ^ c
      ≤ x * ((2 ^ r * (Nat.factorial r + 1)) / (1 - x) ^ (r + 1)) :=
        mul_le_mul_of_nonneg_left hbnd hx0
    _ = x * (2 ^ r * (Nat.factorial r + 1)) / (1 - x) ^ (r + 1) := by ring

/-- **Sharp moment bound**: `M_r(t) ≤ K_r/t^{r+2}` on `0 < t ≤ 1`. Global dominator
`F(a) ≤ E·2^{r+1}(ρ^a/t^{r+1} + a^{r+1}ρ^a)` using `1−e^{−ta} ≥ ta/(1+ta)`. -/
lemma sigmaMoment_le_power_sharp (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      sigmaMoment r t ≤ K / t ^ (r + 2) := by
  refine ⟨(2 ^ r * (Nat.factorial r + 1)) * 2 ^ (r + 1)
      * (2 + Nat.factorial (r + 1) * 2 ^ (r + 2)), by positivity, fun t ht0 ht1 => ?_⟩
  set ρ : ℝ := Real.exp (-t) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρdef, Real.exp_lt_one_iff]; linarith
  have hρn : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hρ0]
  set E : ℝ := 2 ^ r * (Nat.factorial r + 1) with hEdef
  have hEpos : 0 ≤ E := by rw [hEdef]; positivity
  have h1ρ : (0:ℝ) < 1 - ρ := by linarith
  have h1ρhalf : t / 2 ≤ 1 - ρ := by
    rw [hρdef]; have := one_sub_exp_neg_ge_half ht0 ht1; linarith
  rw [sigmaMoment_eq_prod_tsum r ht0]
  -- abbreviations
  set h : ℕ+ × ℕ+ → ℝ := fun c =>
    ((c.1 : ℕ) : ℝ) ^ (r + 1) * ((c.2 : ℕ) : ℝ) ^ r * ρ ^ ((c.1 : ℕ) * (c.2 : ℕ)) with hhdef
  have hh_nonneg : ∀ c, 0 ≤ h c := fun c => by rw [hhdef]; positivity
  have hh_summ : Summable h := summable_weighted_antidiag r hρ0 hρ1
  have hF_summ : Summable (fun a : ℕ+ => ∑' b : ℕ+, h (a, b)) :=
    ((summable_prod_of_nonneg hh_nonneg).mp hh_summ).2
  set D : ℕ+ → ℝ := fun a => E * 2 ^ (r + 1)
    * (ρ ^ (a : ℕ) / t ^ (r + 1) + ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ)) with hDdef
  -- per-a: F a ≤ D a
  have hga : ∀ a : ℕ+, (∑' b : ℕ+, h (a, b)) ≤ D a := by
    intro a
    have hapos : (0:ℝ) < (a : ℕ) := by exact_mod_cast a.pos
    have hρa0 : (0:ℝ) ≤ ρ ^ (a : ℕ) := by positivity
    have hρa1 : ρ ^ (a : ℕ) < 1 := pow_lt_one₀ hρ0.le hρ1 (by positivity)
    have hinner := tsum_pnat_pow_mul_geometric_le r hρa0 hρa1
    have hFeq : (∑' b : ℕ+, h (a, b))
        = ((a : ℕ) : ℝ) ^ (r + 1)
          * ∑' b : ℕ+, ((b : ℕ) : ℝ) ^ r * (ρ ^ (a : ℕ)) ^ (b : ℕ) := by
      rw [hhdef, ← tsum_mul_left]
      refine tsum_congr fun b => ?_
      rw [← pow_mul]; ring
    rw [hFeq]
    have hstep1 : ((a : ℕ) : ℝ) ^ (r + 1)
        * ∑' b : ℕ+, ((b : ℕ) : ℝ) ^ r * (ρ ^ (a : ℕ)) ^ (b : ℕ)
        ≤ ((a : ℕ) : ℝ) ^ (r + 1)
          * (ρ ^ (a : ℕ) * (2 ^ r * (Nat.factorial r + 1)) / (1 - ρ ^ (a : ℕ)) ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    refine hstep1.trans ?_
    -- 1 - ρ^a ≥ ta/(1+ta)
    have hta : (0:ℝ) < t * (a : ℕ) := by positivity
    have hρa_eq : ρ ^ (a : ℕ) = Real.exp (-(t * (a : ℕ))) := by
      rw [hρdef, ← Real.exp_nat_mul]; congr 1; ring
    have h1px : 1 + t * (a : ℕ) ≤ Real.exp (t * (a : ℕ)) := by
      have := Real.add_one_le_exp (t * (a : ℕ)); linarith
    have hden : t * (a : ℕ) / (1 + t * (a : ℕ)) ≤ 1 - ρ ^ (a : ℕ) := by
      have hle : ρ ^ (a : ℕ) ≤ 1 / (1 + t * (a : ℕ)) := by
        rw [hρa_eq, Real.exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by positivity) h1px
      have heq : (1:ℝ) - 1 / (1 + t * (a : ℕ)) = t * (a : ℕ) / (1 + t * (a : ℕ)) := by
        field_simp
      linarith [hle, heq.ge, heq.le]
    have hden0 : (0:ℝ) < 1 - ρ ^ (a : ℕ) := lt_of_lt_of_le (by positivity) hden
    -- 1/(1-ρ^a)^{r+1} ≤ ((1+ta)/(ta))^{r+1}
    have hpow_den : (t * (a : ℕ) / (1 + t * (a : ℕ))) ^ (r + 1) ≤ (1 - ρ ^ (a : ℕ)) ^ (r + 1) :=
      pow_le_pow_left₀ (by positivity) hden (r + 1)
    have hinvpow : (1 - ρ ^ (a : ℕ))⁻¹ ^ (r + 1) ≤ ((1 + t * (a : ℕ)) / (t * (a : ℕ))) ^ (r + 1) := by
      rw [← inv_pow, ← inv_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_le_inv₀ hden0 (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at hpow_den ⊢
      nlinarith [hpow_den]
    -- chain: a^{r+1}·(ρ^a·E/(1-ρ^a)^{r+1}) ≤ E·2^{r+1}(ρ^a/t^{r+1}+a^{r+1}ρ^a)
    have hkey : ((a : ℕ) : ℝ) ^ (r + 1)
        * (ρ ^ (a : ℕ) * E / (1 - ρ ^ (a : ℕ)) ^ (r + 1)) ≤ D a := by
      rw [hDdef]
      have hexpand : ((a : ℕ) : ℝ) ^ (r + 1) * (ρ ^ (a : ℕ) * E / (1 - ρ ^ (a : ℕ)) ^ (r + 1))
          = E * (ρ ^ (a : ℕ) * (((a : ℕ) : ℝ) ^ (r + 1) * ((1 - ρ ^ (a : ℕ))⁻¹) ^ (r + 1))) := by
        rw [div_eq_mul_inv, inv_pow]; ring
      rw [hexpand]
      have hb1 : ((a : ℕ) : ℝ) ^ (r + 1) * ((1 - ρ ^ (a : ℕ))⁻¹) ^ (r + 1)
          ≤ ((a : ℕ) : ℝ) ^ (r + 1) * ((1 + t * (a : ℕ)) / (t * (a : ℕ))) ^ (r + 1) :=
        mul_le_mul_of_nonneg_left hinvpow (by positivity)
      have haeq : ((a : ℕ) : ℝ) ^ (r + 1) * ((1 + t * (a : ℕ)) / (t * (a : ℕ))) ^ (r + 1)
          = (1 + t * (a : ℕ)) ^ (r + 1) / t ^ (r + 1) := by
        rw [div_pow, mul_pow]
        field_simp
        ring
      have hbnd2 : (1 + t * (a : ℕ)) ^ (r + 1) ≤ 2 ^ (r + 1) * (1 + (t * (a : ℕ)) ^ (r + 1)) := by
        have hmx : 1 + t * (a : ℕ) ≤ 2 * max 1 (t * (a : ℕ)) := by
          rcases le_or_gt (t * (a : ℕ)) 1 with hh | hh
          · rw [max_eq_left hh]; linarith
          · rw [max_eq_right hh.le]; linarith
        calc (1 + t * (a : ℕ)) ^ (r + 1) ≤ (2 * max 1 (t * (a : ℕ))) ^ (r + 1) := by gcongr
          _ = 2 ^ (r + 1) * (max 1 (t * (a : ℕ))) ^ (r + 1) := by rw [mul_pow]
          _ ≤ 2 ^ (r + 1) * (1 + (t * (a : ℕ)) ^ (r + 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rcases le_or_gt (t * (a : ℕ)) 1 with hh | hh
              · rw [max_eq_left hh]; simp only [one_pow]; positivity
              · rw [max_eq_right hh.le]; nlinarith [pow_nonneg hta.le (r+1)]
      have htapow : (t * (a : ℕ)) ^ (r + 1) = t ^ (r + 1) * ((a : ℕ) : ℝ) ^ (r + 1) := by
        rw [mul_pow]
      have hfinal : (1 + t * (a : ℕ)) ^ (r + 1) / t ^ (r + 1)
          ≤ 2 ^ (r + 1) * (1 / t ^ (r + 1) + ((a : ℕ) : ℝ) ^ (r + 1)) := by
        rw [div_le_iff₀ (by positivity)]
        have h2 := hbnd2
        rw [htapow] at h2
        have htpow : (0:ℝ) < t ^ (r + 1) := by positivity
        nlinarith [h2, htpow, mul_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^(r+1)) (pow_nonneg hapos.le (r+1))]
      calc E * (ρ ^ (a : ℕ) * (((a : ℕ) : ℝ) ^ (r + 1) * ((1 - ρ ^ (a : ℕ))⁻¹) ^ (r + 1)))
          ≤ E * (ρ ^ (a : ℕ) * ((1 + t * (a : ℕ)) ^ (r + 1) / t ^ (r + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hEpos
            apply mul_le_mul_of_nonneg_left _ hρa0
            rw [← haeq]; exact hb1
        _ ≤ E * (ρ ^ (a : ℕ) * (2 ^ (r + 1) * (1 / t ^ (r + 1) + ((a : ℕ) : ℝ) ^ (r + 1)))) := by
            apply mul_le_mul_of_nonneg_left _ hEpos
            apply mul_le_mul_of_nonneg_left hfinal hρa0
        _ = E * 2 ^ (r + 1) * (ρ ^ (a : ℕ) / t ^ (r + 1) + ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ)) := by
            ring
    exact hkey
  -- D summable
  have hgeo_pnat : Summable (fun a : ℕ+ => ρ ^ (a : ℕ)) :=
    (summable_geometric_of_lt_one hρ0.le hρ1).comp_injective PNat.coe_injective
  have hpow_pnat : Summable (fun a : ℕ+ => ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r + 1) hρn).comp_injective PNat.coe_injective
  have hD_summ : Summable D := by
    rw [hDdef]
    exact ((hgeo_pnat.mul_right (t ^ (r + 1))⁻¹).congr (fun a => by rw [div_eq_mul_inv]) |>.add hpow_pnat).mul_left (E * 2 ^ (r + 1))
  -- Σ F ≤ Σ D
  have hmain := hF_summ.tsum_le_tsum hga hD_summ
  refine hmain.trans ?_
  -- Σ D = E2^{r+1}(Σρ^a/t^{r+1} + Σ a^{r+1}ρ^a) ≤ K/t^{r+2}
  have hDsum_eq : (∑' a : ℕ+, D a)
      = E * 2 ^ (r + 1)
        * ((∑' a : ℕ+, ρ ^ (a : ℕ)) / t ^ (r + 1)
          + ∑' a : ℕ+, ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ)) := by
    rw [hDdef, ← tsum_mul_left]
    rw [Summable.tsum_add ((hgeo_pnat.mul_right (t ^ (r + 1))⁻¹).congr (fun a => by rw [div_eq_mul_inv]))
      hpow_pnat]
    rw [← tsum_div_const, ← tsum_mul_left, ← tsum_mul_left]
    congr 1
  rw [hDsum_eq]
  -- bounds: Σρ^a ≤ ρ/(1-ρ) ≤ 2/t ; Σ a^{r+1}ρ^a ≤ (r+1)!/(1-ρ)^{r+2} ≤ (r+1)!2^{r+2}/t^{r+2}
  have hgeobnd : (∑' a : ℕ+, ρ ^ (a : ℕ)) ≤ 2 / t := by
    have hle : (∑' a : ℕ+, ρ ^ (a : ℕ)) ≤ ∑' n : ℕ, ρ ^ n :=
      (summable_geometric_of_lt_one hρ0.le hρ1).tsum_comp_le_tsum_of_inj
        (fun n => by positivity) PNat.coe_injective
    rw [tsum_geometric_of_lt_one hρ0.le hρ1] at hle
    have hinv2 : (1 - ρ)⁻¹ ≤ 2 / t := by
      rw [inv_eq_one_div, div_le_div_iff₀ h1ρ ht0]; nlinarith [h1ρhalf]
    linarith
  have hpowbnd : (∑' a : ℕ+, ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ))
      ≤ (Nat.factorial (r + 1) * 2 ^ (r + 2)) / t ^ (r + 2) := by
    have hle : (∑' a : ℕ+, ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ))
        ≤ ∑' n : ℕ, (n : ℝ) ^ (r + 1) * ρ ^ n :=
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r + 1) hρn).tsum_comp_le_tsum_of_inj
        (fun n => by positivity) PNat.coe_injective
    have hb := tsum_pow_mul_geometric_le (r + 1) hρ0.le hρ1
    have hpow : (t / 2) ^ (r + 2) ≤ (1 - ρ) ^ (r + 2) :=
      pow_le_pow_left₀ (by positivity) h1ρhalf _
    have hdiv2 : (t / 2) ^ (r + 2) = t ^ (r + 2) / 2 ^ (r + 2) := by rw [div_pow]
    have hb2 : (Nat.factorial (r + 1) : ℝ) / (1 - ρ) ^ (r + 2)
        ≤ (Nat.factorial (r + 1) * 2 ^ (r + 2)) / t ^ (r + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hfr : (0:ℝ) ≤ (Nat.factorial (r + 1) : ℝ) := by positivity
      nlinarith [hpow, hdiv2.ge, hdiv2.le, pow_pos h1ρ (r + 2), pow_pos ht0 (r + 2),
        mul_nonneg hfr (pow_pos h1ρ (r+2)).le]
    linarith [hle, hb, hb2]
  -- combine
  have hge0 : (0:ℝ) ≤ E * 2 ^ (r + 1) := by positivity
  have hh1 : (∑' a : ℕ+, ρ ^ (a : ℕ)) / t ^ (r + 1) ≤ 2 / t ^ (r + 2) := by
    have := div_le_div_of_nonneg_right hgeobnd (pow_pos ht0 (r + 1))
    have heq : (2 / t) / t ^ (r + 1) = 2 / t ^ (r + 2) := by
      rw [div_div, ← pow_succ']
    linarith [this, heq.ge, heq.le]
  have hstep : (∑' a : ℕ+, ρ ^ (a : ℕ)) / t ^ (r + 1)
      + ∑' a : ℕ+, ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ)
      ≤ (2 + Nat.factorial (r + 1) * 2 ^ (r + 2)) / t ^ (r + 2) := by
    rw [add_div]
    linarith [hh1, hpowbnd]
  calc E * 2 ^ (r + 1)
        * ((∑' a : ℕ+, ρ ^ (a : ℕ)) / t ^ (r + 1)
          + ∑' a : ℕ+, ((a : ℕ) : ℝ) ^ (r + 1) * ρ ^ (a : ℕ))
      ≤ E * 2 ^ (r + 1) * ((2 + Nat.factorial (r + 1) * 2 ^ (r + 2)) / t ^ (r + 2)) :=
        mul_le_mul_of_nonneg_left hstep hge0
    _ = (2 ^ r * (Nat.factorial r + 1)) * 2 ^ (r + 1)
          * (2 + Nat.factorial (r + 1) * 2 ^ (r + 2)) / t ^ (r + 2) := by
        rw [hEdef]; ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
