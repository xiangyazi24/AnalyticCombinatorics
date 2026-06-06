import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMoments

/-!
# Mass-rate campaign: the Lambert identity for `M₀` (R8 §2.1)

`M₀(t) = Σ_m σ(m)e^{−tm} = Σ_k boseKernel(tk)` — via Mathlib's
`tsum_prod_pow_eq_tsum_sigma` (divisors-antidiagonal Lambert machinery from the
Eisenstein q-expansion development) at `k = 1`, `r = e^{−t}`, with the
geometric-derivative inner sum `Σ'_{c:ℕ+} c·y^c = y/(1−y)²`.  Opus-authored.
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset
open scoped BigOperators Topology ArithmeticFunction.sigma

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- `σR` agrees with the arithmetic-function `σ 1` (cast). -/
lemma sigmaR_eq_sigma_one (m : ℕ) : Sigma.sigmaR m = ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) := rfl

/-- Drop-the-zero bridge: `Σ'_{m:ℕ} [m≠0]·f m = Σ'_{c:ℕ+} f c` (no summability needed). -/
lemma tsum_if_ne_zero_eq_pnat (f : ℕ → ℝ) :
    ∑' m : ℕ, (if m = 0 then 0 else f m) = ∑' c : ℕ+, f (c : ℕ) := by
  have hinj : Function.Injective (fun c : ℕ+ => (c : ℕ)) :=
    fun a b h => PNat.coe_injective h
  have hsupp : Function.support (fun m : ℕ => if m = 0 then 0 else f m)
      ⊆ Set.range (fun c : ℕ+ => (c : ℕ)) := by
    intro x hx
    rw [Function.mem_support] at hx
    have hx0 : x ≠ 0 := by
      intro h0
      apply hx
      rw [h0, if_pos rfl]
    exact ⟨⟨x, Nat.pos_of_ne_zero hx0⟩, rfl⟩
  have h := hinj.tsum_eq hsupp
  rw [← h]
  refine tsum_congr fun c => ?_
  rw [if_neg (PNat.ne_zero c)]

/-- The inner geometric-derivative sum: `Σ'_{c:ℕ+} c·y^c = y/(1−y)²` for `‖y‖ < 1`. -/
lemma tsum_pnat_coe_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' c : ℕ+, ((c : ℕ) : ℝ) * y ^ (c : ℕ) = y / (1 - y) ^ 2 := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) * y ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hy).summable
  have hbase : ∑' n : ℕ, (n : ℝ) * y ^ n = y / (1 - y) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hy
  have hshift := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℝ) * y ^ n)
  rw [hshift]
  have hzero := hsum.tsum_eq_zero_add
  rw [← hbase, hzero]
  simp

/--
**The Lambert identity for `M₀`** (R8 §2.1):

  `Σ_m σ(m)e^{−tm} = Σ_k e^{−tk}/(1−e^{−tk})²`.
-/
theorem sigmaMoment_zero_lambert {t : ℝ} (ht : 0 < t) :
    sigmaMoment 0 t = ∑' k : ℕ, if k = 0 then 0 else boseKernel (t * (k : ℝ)) := by
  set r : ℝ := Real.exp (-t) with hrdef
  have hr : ‖r‖ < 1 := by
    rw [hrdef, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hrm : ∀ m : ℕ, Real.exp (-t * (m : ℝ)) = r ^ m := by
    intro m
    rw [hrdef, ← Real.exp_nat_mul]
    congr 1
    ring
  -- LHS in ℕ+ σ-form
  have hL : sigmaMoment 0 t
      = ∑' e : ℕ+, ((ArithmeticFunction.sigma 1 (e : ℕ) : ℕ) : ℝ) * r ^ (e : ℕ) := by
    rw [sigmaMoment, tsum_if_ne_zero_eq_pnat
      (f := fun m : ℕ => (m : ℝ) ^ 0 * Sigma.sigmaR m * Real.exp (-t * (m : ℝ)))]
    refine tsum_congr fun e => ?_
    rw [pow_zero, one_mul, hrm, sigmaR_eq_sigma_one]
  -- RHS in ℕ+ Bose form
  have hR : (∑' k : ℕ, if k = 0 then 0 else boseKernel (t * (k : ℝ)))
      = ∑' d : ℕ+, boseKernel (t * ((d : ℕ) : ℝ)) :=
    tsum_if_ne_zero_eq_pnat (f := fun k : ℕ => boseKernel (t * (k : ℝ)))
  rw [hL, hR]
  -- each Bose term is the inner geometric-derivative sum
  have hinner : ∀ d : ℕ+, boseKernel (t * ((d : ℕ) : ℝ))
      = ∑' c : ℕ+, ((c : ℕ) : ℝ) * r ^ ((d : ℕ) * (c : ℕ)) := by
    intro d
    have hyd : ‖r ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg r) hr (PNat.ne_zero d)
    have hexp_eq : Real.exp (-(t * ((d : ℕ) : ℝ))) = r ^ (d : ℕ) := by
      rw [show -(t * ((d : ℕ) : ℝ)) = -t * ((d : ℕ) : ℝ) by ring]
      exact hrm (d : ℕ)
    have h2 : boseKernel (t * ((d : ℕ) : ℝ)) = r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2 := by
      rw [boseKernel, hexp_eq]
    rw [h2, ← tsum_pnat_coe_mul_geometric hyd]
    refine tsum_congr fun c => ?_
    rw [pow_mul]
  rw [tsum_congr hinner]
  -- Mathlib's Lambert rearrangement at k = 1
  have hML := tsum_prod_pow_eq_tsum_sigma (𝕜 := ℝ) 1 hr
  rw [← hML]
  refine tsum_congr fun d => tsum_congr fun c => ?_
  push_cast
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
