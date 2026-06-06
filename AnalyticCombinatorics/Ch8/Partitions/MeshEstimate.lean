import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.ModelAssembly

/-!
# The mesh estimate and the model-kernel window limit

The Riemann–Stieltjes mesh estimate: both endpoint sums `lowerMesh`/`upperMesh` on the
uniform mesh approximate `modelIntegral C a b = ∫ a..b (π²/6) y e^{−(C/2)y} dy` to any
tolerance for `N` large.  Proof: per-block sandwich `e^{−(C/2)α_{k+1}}·Q·Δ(y²) ≤
∫_block ≤ e^{−(C/2)α_k}·Q·Δ(y²)` (monotonicity of `e^{−x}`), and the upper−lower gap is
`≤ Σ (C/2)h·Q·2b·h = C·Q·b·(b−a)·h` by the Lipschitz bound `e^{−u}−e^{−v} ≤ v−u`.

Combined with the banked `blockSum_eventually_between_mesh_eps`, this yields the
model-kernel window limit `model_kernel_window`:

  `(1/n)·Σ_{(a√n,b√n]} σ(m)·e^{−(C/2)m/√n} → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.

Opus-authored (replaces the mesh-estimate axiom in the ChatGPT draft with a real proof).
-/

set_option maxHeartbeats 800000

noncomputable section

open Filter Finset intervalIntegral
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

/-- `π²/6 = 2Q`. -/
private lemma two_Q : Real.pi ^ 2 / 6 = 2 * Q := by
  simp only [Q]; ring

private lemma Q_pos' : (0 : ℝ) < Q := by
  simp only [Q]
  positivity

/-- The model density is interval-integrable. -/
private lemma density_intervalIntegrable (C α β : ℝ) :
    IntervalIntegrable (fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      MeasureTheory.volume α β := by
  have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
    have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
      continuous_const.mul continuous_id
    have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    exact h1.mul h2
  exact hc.intervalIntegrable α β

/-- Linear integrands are interval-integrable. -/
private lemma linear_intervalIntegrable (c α β : ℝ) :
    IntervalIntegrable (fun y : ℝ => c * y) MeasureTheory.volume α β :=
  (continuous_const.mul continuous_id).intervalIntegrable α β

/-- Lipschitz bound for `e^{−x}` on the nonnegative half-line. -/
private lemma exp_neg_sub_exp_neg_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.exp (-u) - Real.exp (-v) ≤ v - u := by
  have h1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - (v - u) ≤ Real.exp (-(v - u)) := by
    have := Real.add_one_le_exp (-(v - u))
    linarith
  have h4 : Real.exp (-(v - u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-v) = Real.exp (-u) * Real.exp (-(v - u)) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4), Real.exp_pos (-u)]

/-- The constant-exponential block integral: `∫_α^β (2QK)·y dy = QK(β²−α²)`. -/
private lemma block_const_integral (K α β : ℝ) :
    ∫ y in α..β, (2 * Q * K) * y = Q * K * (β ^ 2 - α ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- Lower block bound: `e^{−(C/2)β}·Q·(β²−α²) ≤ ∫_α^β (π²/6) y e^{−(C/2)y} dy`. -/
private lemma block_lower_le_integral {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    Real.exp (-(C / 2) * β) * Q * (β ^ 2 - α ^ 2)
      ≤ ∫ y in α..β, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
  have hK : Real.exp (-(C / 2) * β) * Q * (β ^ 2 - α ^ 2)
      = ∫ y in α..β, (2 * Q * Real.exp (-(C / 2) * β)) * y := by
    rw [block_const_integral]
    ring
  rw [hK]
  apply intervalIntegral.integral_mono_on hαβ
  · exact linear_intervalIntegrable _ _ _
  · exact density_intervalIntegrable _ _ _
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hα hy.1
    have hexp : Real.exp (-(C / 2) * β) ≤ Real.exp (-(C / 2) * y) := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ (C / 2) * (β - y) := mul_nonneg (by linarith) (by linarith [hy.2])
      nlinarith [h0]
    rw [two_Q]
    calc (2 * Q * Real.exp (-(C / 2) * β)) * y
        = (2 * Q * y) * Real.exp (-(C / 2) * β) := by ring
      _ ≤ (2 * Q * y) * Real.exp (-(C / 2) * y) := by
          apply mul_le_mul_of_nonneg_left hexp
          have := Q_pos'.le
          positivity
      _ = 2 * Q * y * Real.exp (-(C / 2) * y) := by ring

/-- Upper block bound: `∫_α^β (π²/6) y e^{−(C/2)y} dy ≤ e^{−(C/2)α}·Q·(β²−α²)`. -/
private lemma block_integral_le_upper {C α β : ℝ} (hC : 0 < C) (hα : 0 ≤ α) (hαβ : α ≤ β) :
    (∫ y in α..β, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      ≤ Real.exp (-(C / 2) * α) * Q * (β ^ 2 - α ^ 2) := by
  have hK : Real.exp (-(C / 2) * α) * Q * (β ^ 2 - α ^ 2)
      = ∫ y in α..β, (2 * Q * Real.exp (-(C / 2) * α)) * y := by
    rw [block_const_integral]
    ring
  rw [hK]
  apply intervalIntegral.integral_mono_on hαβ
  · exact density_intervalIntegrable _ _ _
  · exact linear_intervalIntegrable _ _ _
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hα hy.1
    have hexp : Real.exp (-(C / 2) * y) ≤ Real.exp (-(C / 2) * α) := by
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ (C / 2) * (y - α) := mul_nonneg (by linarith) (by linarith [hy.1])
      nlinarith [h0]
    rw [two_Q]
    calc 2 * Q * y * Real.exp (-(C / 2) * y)
        = (2 * Q * y) * Real.exp (-(C / 2) * y) := by ring
      _ ≤ (2 * Q * y) * Real.exp (-(C / 2) * α) := by
          apply mul_le_mul_of_nonneg_left hexp
          have := Q_pos'.le
          positivity
      _ = (2 * Q * Real.exp (-(C / 2) * α)) * y := by ring

/-- Mesh points are monotone in the index (for `h ≥ 0`). -/
private lemma meshPoint_mono {a h : ℝ} (hh : 0 ≤ h) {k N : ℕ} (hkN : k ≤ N) :
    meshPoint a h k ≤ meshPoint a h N := by
  dsimp [meshPoint]
  have hcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have := mul_le_mul_of_nonneg_right hcast hh
  linarith

/-- The right end of the mesh is `b` when `h = (b−a)/N`. -/
private lemma meshPoint_last {a b : ℝ} {N : ℕ} (hN : 0 < N) :
    meshPoint a ((b - a) / (N : ℝ)) N = b := by
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  dsimp [meshPoint]
  field_simp
  ring

/-- The integral splits over the mesh and is sandwiched by the endpoint sums. -/
private lemma mesh_sandwich {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) :
    lowerMesh C a ((b - a) / (N : ℝ)) N ≤ modelIntegral C a b ∧
      modelIntegral C a b ≤ upperMesh C a ((b - a) / (N : ℝ)) N := by
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhnonneg : 0 ≤ h := by
    rw [hdef]
    have : 0 ≤ b - a := by linarith
    positivity
  have hlast : meshPoint a h N = b := meshPoint_last hN
  have hfirst : meshPoint a h 0 = a := by simp [meshPoint]
  -- split the integral over the mesh
  have hsplit :
      (∑ k ∈ Finset.range N,
        ∫ y in meshPoint a h k..meshPoint a h (k + 1),
          (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
        = modelIntegral C a b := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k => meshPoint a h k) (n := N)
      (f := fun y => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y))
      (fun k _hk => density_intervalIntegrable C _ _)
    rw [this]
    dsimp only
    rw [hfirst, hlast]
    rfl
  constructor
  · -- lowerMesh ≤ ∫
    rw [← hsplit, lowerMesh]
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    exact block_lower_le_integral hC hαk hαβ
  · -- ∫ ≤ upperMesh
    rw [← hsplit, upperMesh]
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    exact block_integral_le_upper hC hαk hαβ

/-- The upper−lower mesh gap is at most `C·Q·b·(b−a)·h`. -/
private lemma mesh_gap_le {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) :
    upperMesh C a ((b - a) / (N : ℝ)) N - lowerMesh C a ((b - a) / (N : ℝ)) N
      ≤ C * Q * b * (b - a) * ((b - a) / (N : ℝ)) := by
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hhnonneg : 0 ≤ h := by
    rw [hdef]
    have : 0 ≤ b - a := by linarith
    positivity
  have hNh : (N : ℝ) * h = b - a := by
    rw [hdef]
    field_simp
  have hlast : meshPoint a h N = b := meshPoint_last hN
  have hb_pos : 0 < b := lt_of_le_of_lt ha hab
  -- per-term bound
  have hterm : ∀ k ∈ Finset.range N,
      Real.exp (-(C / 2) * meshPoint a h k) * Q *
          (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
        Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
          (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)
        ≤ (C / 2) * h * (Q * (2 * b * h)) := by
    intro k hk
    have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
    have hαk : 0 ≤ meshPoint a h k := meshPoint_nonneg ha hhnonneg k
    have hαk1 : 0 ≤ meshPoint a h (k + 1) := meshPoint_nonneg ha hhnonneg (k + 1)
    have hαβ : meshPoint a h k ≤ meshPoint a h (k + 1) :=
      meshPoint_mono hhnonneg (Nat.le_succ k)
    have hkb : meshPoint a h k ≤ b := by
      rw [← hlast]
      exact meshPoint_mono hhnonneg (le_trans (Nat.le_succ k) hkN)
    have hk1b : meshPoint a h (k + 1) ≤ b := by
      rw [← hlast]
      exact meshPoint_mono hhnonneg hkN
    have hstep : meshPoint a h (k + 1) - meshPoint a h k = h := by
      dsimp [meshPoint]
      push_cast
      ring
    -- Lipschitz bound on the exponential difference
    have hlip :
        Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1))
          ≤ (C / 2) * h := by
      have hu : 0 ≤ (C / 2) * meshPoint a h k := by positivity
      have huv : (C / 2) * meshPoint a h k ≤ (C / 2) * meshPoint a h (k + 1) :=
        mul_le_mul_of_nonneg_left hαβ (by positivity)
      have := exp_neg_sub_exp_neg_le hu huv
      have heq1 : -(C / 2) * meshPoint a h k = -((C / 2) * meshPoint a h k) := by ring
      have heq2 : -(C / 2) * meshPoint a h (k + 1) =
          -((C / 2) * meshPoint a h (k + 1)) := by ring
      rw [heq1, heq2]
      calc Real.exp (-((C / 2) * meshPoint a h k)) -
              Real.exp (-((C / 2) * meshPoint a h (k + 1)))
          ≤ (C / 2) * meshPoint a h (k + 1) - (C / 2) * meshPoint a h k := this
        _ = (C / 2) * (meshPoint a h (k + 1) - meshPoint a h k) := by ring
        _ = (C / 2) * h := by rw [hstep]
    -- the squared-difference factor
    have hsq : meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 ≤ 2 * b * h := by
      have : meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 =
          (meshPoint a h (k + 1) - meshPoint a h k) *
            (meshPoint a h (k + 1) + meshPoint a h k) := by ring
      rw [this, hstep]
      have hsum : meshPoint a h (k + 1) + meshPoint a h k ≤ 2 * b := by linarith
      calc h * (meshPoint a h (k + 1) + meshPoint a h k)
          ≤ h * (2 * b) := mul_le_mul_of_nonneg_left hsum hhnonneg
        _ = 2 * b * h := by ring
    have hsq_nonneg : 0 ≤ meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2 := by
      nlinarith [hαβ, hαk]
    have hexp_diff_nonneg :
        0 ≤ Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1)) := by
      have : -(C / 2) * meshPoint a h (k + 1) ≤ -(C / 2) * meshPoint a h k := by
        nlinarith [hαβ]
      linarith [Real.exp_le_exp.mpr this]
    have hQ := Q_pos'.le
    calc Real.exp (-(C / 2) * meshPoint a h k) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
          Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)
        = (Real.exp (-(C / 2) * meshPoint a h k) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1))) * Q *
            (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) := by ring
      _ ≤ ((C / 2) * h) * Q * (2 * b * h) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hlip hQ
          · exact hsq
          · exact hsq_nonneg
          · positivity
      _ = (C / 2) * h * (Q * (2 * b * h)) := by ring
  -- sum the per-term bounds
  have hsum_le :
      upperMesh C a h N - lowerMesh C a h N
        ≤ (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := by
    rw [upperMesh, lowerMesh, ← Finset.sum_sub_distrib]
    calc (∑ k ∈ Finset.range N,
          (Real.exp (-(C / 2) * meshPoint a h k) * Q *
              (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2) -
            Real.exp (-(C / 2) * meshPoint a h (k + 1)) * Q *
              (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)))
        ≤ ∑ _k ∈ Finset.range N, (C / 2) * h * (Q * (2 * b * h)) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc upperMesh C a h N - lowerMesh C a h N
      ≤ (N : ℝ) * ((C / 2) * h * (Q * (2 * b * h))) := hsum_le
    _ = C * Q * b * ((N : ℝ) * h) * h := by ring
    _ = C * Q * b * (b - a) * h := by rw [hNh]

/--
**The mesh estimate** (formerly the draft's axiom): for every `ε > 0` there is a mesh
size `N` for which both endpoint sums are within `ε` of the model integral.
-/
theorem mesh_endpoint_sums_approx_integral
    {C : ℝ} (hC : 0 < C) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∀ ε > 0, ∃ N : ℕ, 0 < N ∧
      upperMesh C a ((b - a) / (N : ℝ)) N
        ≤ modelIntegral C a b + ε ∧
      modelIntegral C a b - ε
        ≤ lowerMesh C a ((b - a) / (N : ℝ)) N := by
  intro ε hε
  have hb_pos : 0 < b := lt_of_le_of_lt ha hab
  obtain ⟨M, hM⟩ := exists_nat_gt (C * Q * b * (b - a) ^ 2 / ε)
  refine ⟨M + 1, Nat.succ_pos M, ?_⟩
  set N : ℕ := M + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos M
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMN : C * Q * b * (b - a) ^ 2 / ε < (N : ℝ) := by
    have : (M : ℝ) < (N : ℝ) := by
      rw [hNdef]
      push_cast
      linarith
    linarith
  -- the gap bound is < ε for this N
  have hgap_lt : C * Q * b * (b - a) * ((b - a) / (N : ℝ)) < ε := by
    have hkey : C * Q * b * (b - a) ^ 2 < (N : ℝ) * ε := by
      have := (div_lt_iff₀ hε).mp hMN
      linarith [this]
    have hform : C * Q * b * (b - a) * ((b - a) / (N : ℝ))
        = (C * Q * b * (b - a) ^ 2) / (N : ℝ) := by
      ring
    rw [hform, div_lt_iff₀ hNposR]
    linarith [hkey]
  obtain ⟨hlow_le, hle_up⟩ := mesh_sandwich (C := C) hC ha hab hN
  have hgap := mesh_gap_le (C := C) hC ha hab hN
  constructor
  · -- upperMesh ≤ ∫ + ε
    linarith
  · -- ∫ − ε ≤ lowerMesh
    linarith

/--
**The model-kernel window limit** (HR Stage I.3, final assembly):

  `(1/n) Σ_{(a√n, b√n]} σ(m) e^{−(C/2)m/√n} → ∫_a^b (π²/6) y e^{−(C/2)y} dy`.
-/
theorem model_kernel_window
    {C : ℝ} (hC : 0 < C) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (blockSum C a b) atTop (𝓝 (modelIntegral C a b)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨N, hNpos, hUpper, hLower⟩ :=
    mesh_endpoint_sums_approx_integral hC a b ha hab (ε / 3) hε3
  have hevent :=
    blockSum_eventually_between_mesh_eps
      (C := C) (a := a) (b := b) hC ha hab hNpos hε3
  rcases eventually_atTop.1 hevent with ⟨N0, hN0⟩
  refine ⟨N0, fun n hn => ?_⟩
  have hb := hN0 n hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hb.1]
  · linarith [hb.2]

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
