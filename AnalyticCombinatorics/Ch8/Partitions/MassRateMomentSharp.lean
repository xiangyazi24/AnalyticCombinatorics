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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
