import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.BlockSqueeze
import AnalyticCombinatorics.Ch8.Partitions.ErdosIntegral

/-!
# Mesh assembly for the model-kernel window limit

This file assembles the banked block squeeze and half-open mass limit over a uniform
arithmetic mesh: the half-open block `(a√n, b√n]` partitions into `N` mesh blocks, each
block is squeezed by endpoint exponentials times its half-open mass, and as `n → ∞` the
mesh sums converge to the Stieltjes endpoint sums `lowerMesh`/`upperMesh`.

Main result: `blockSum_eventually_between_mesh_eps` — for any fixed mesh and `ε > 0`,
eventually `lowerMesh − ε ≤ blockSum n ≤ upperMesh + ε`.

The remaining real-variable step (mesh sums → ∫ a..b (π²/6) y e^{−(C/2)y} dy as the mesh
refines) is the next brick; combining the two yields the model-kernel window limit.
ChatGPT-draft + Opus-fix.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- The weighted half-open model block `(α√n, β√n]`. -/
noncomputable def blockSum (C α β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ m ∈ Finset.Icc 1 (n - 1),
      (if α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
          (m : ℝ) ≤ β * Real.sqrt (n : ℝ)
       then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
       else 0)

/-- The target interval integral. -/
noncomputable def modelIntegral (C a b : ℝ) : ℝ :=
  ∫ y in a..b, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y)

/-- Uniform arithmetic mesh point `a + k h`. -/
noncomputable def meshPoint (a h : ℝ) (k : ℕ) : ℝ :=
  a + (k : ℝ) * h

/-- Lower Stieltjes endpoint sum on the uniform mesh. -/
noncomputable def lowerMesh (C a h : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
      Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)

/-- Upper Stieltjes endpoint sum on the uniform mesh. -/
noncomputable def upperMesh (C a h : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.exp (-(C / 2) * meshPoint a h k) *
      Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2)

/-- Lower endpoint mass sequence for one mesh block. -/
noncomputable def lowerSeq (C a h : ℝ) (k n : ℕ) : ℝ :=
  Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
    halfOpenMass (meshPoint a h k) (meshPoint a h (k + 1)) n

/-- Upper endpoint mass sequence for one mesh block. -/
noncomputable def upperSeq (C a h : ℝ) (k n : ℕ) : ℝ :=
  Real.exp (-(C / 2) * meshPoint a h k) *
    halfOpenMass (meshPoint a h k) (meshPoint a h (k + 1)) n

private lemma meshPoint_nonneg
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) :
    0 ≤ meshPoint a h k := by
  dsimp [meshPoint]
  have hk : 0 ≤ (k : ℝ) := by positivity
  nlinarith [mul_nonneg hk hh]

private lemma meshPoint_succ_lt
    {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    meshPoint a h k < meshPoint a h (k + 1) := by
  dsimp [meshPoint]
  have hk : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self k
  have := mul_lt_mul_of_pos_right hk hh
  linarith

private lemma blockSum_self (C α : ℝ) (n : ℕ) :
    blockSum C α α n = 0 := by
  classical
  dsimp [blockSum]
  have hsum :
      (∑ m ∈ Finset.Icc 1 (n - 1),
        (if α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ α * Real.sqrt (n : ℝ)
         then σR m * Real.exp (-(C / 2) * (m : ℝ) / Real.sqrt (n : ℝ))
         else 0)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hnot :
        ¬ (α * Real.sqrt (n : ℝ) < (m : ℝ) ∧
            (m : ℝ) ≤ α * Real.sqrt (n : ℝ)) := by
      intro h
      linarith [h.1, h.2]
    rw [if_neg hnot]
  rw [hsum, mul_zero]

/-- Two adjacent half-open windows add exactly. -/
private lemma blockSum_add
    (C a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (n : ℕ) :
    blockSum C a b n =
      blockSum C a c n + blockSum C c b n := by
  classical
  dsimp [blockSum]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  have hs_nonneg : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hacs : a * Real.sqrt (n : ℝ) ≤ c * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hac hs_nonneg
  have hcbs : c * Real.sqrt (n : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hcb hs_nonneg
  by_cases h1 : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ c * Real.sqrt (n : ℝ)
  · have hab : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
      ⟨h1.1, le_trans h1.2 hcbs⟩
    have h2 : ¬ (c * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) := by
      intro h
      exact absurd h1.2 (not_le.mpr h.1)
    rw [if_pos hab, if_pos h1, if_neg h2, add_zero]
  · by_cases h2 : c * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)
    · have hab : a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ) :=
        ⟨lt_of_le_of_lt hacs h2.1, h2.2⟩
      rw [if_pos hab, if_neg h1, if_pos h2, zero_add]
    · have hab : ¬ (a * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (n : ℝ)) := by
        intro h
        rcases le_or_lt (m : ℝ) (c * Real.sqrt (n : ℝ)) with hc | hc
        · exact h1 ⟨h.1, hc⟩
        · exact h2 ⟨hc, h.2⟩
      rw [if_neg hab, if_neg h1, if_neg h2, add_zero]

/--
Arithmetic mesh decomposition:

`(a, a + N h]` is the disjoint union of the half-open blocks
`(a + k h, a + (k+1)h]`.
-/
private lemma blockSum_arith_partition
    (C a h : ℝ) (hh : 0 ≤ h) :
    ∀ N n : ℕ,
      blockSum C a (a + (N : ℝ) * h) n =
        ∑ k ∈ Finset.range N,
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
  intro N
  induction N with
  | zero =>
      intro n
      simp [meshPoint, blockSum_self]
  | succ N ih =>
      intro n
      have hac : a ≤ a + (N : ℝ) * h := by
        have hmul : 0 ≤ (N : ℝ) * h := by positivity
        linarith
      have hcb :
          a + (N : ℝ) * h ≤ a + ((N + 1 : ℕ) : ℝ) * h := by
        have hk : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ N
        have hmul := mul_le_mul_of_nonneg_right hk hh
        linarith
      calc
        blockSum C a (a + ((N + 1 : ℕ) : ℝ) * h) n
            =
          blockSum C a (a + (N : ℝ) * h) n +
            blockSum C (a + (N : ℝ) * h)
              (a + ((N + 1 : ℕ) : ℝ) * h) n :=
              blockSum_add C a (a + (N : ℝ) * h)
                (a + ((N + 1 : ℕ) : ℝ) * h) hac hcb n
        _ =
          (∑ k ∈ Finset.range N,
            blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n) +
            blockSum C (meshPoint a h N) (meshPoint a h (N + 1)) n := by
              rw [ih n]
              simp [meshPoint]
        _ =
          ∑ k ∈ Finset.range (N + 1),
            blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
              rw [Finset.sum_range_succ]

private lemma lowerSeq_tendsto
    {C a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (k : ℕ) :
    Tendsto
      (fun n : ℕ => lowerSeq C a h k n)
      atTop
      (𝓝
        (Real.exp (-(C / 2) * meshPoint a h (k + 1)) *
          Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2))) := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hm := halfOpenMass_tendsto hα hαβ
  simpa [lowerSeq, mul_assoc] using
    ((tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ => Real.exp (-(C / 2) * meshPoint a h (k + 1)))
        atTop
        (𝓝 (Real.exp (-(C / 2) * meshPoint a h (k + 1))))).mul hm)

private lemma upperSeq_tendsto
    {C a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (k : ℕ) :
    Tendsto
      (fun n : ℕ => upperSeq C a h k n)
      atTop
      (𝓝
        (Real.exp (-(C / 2) * meshPoint a h k) *
          Q * (meshPoint a h (k + 1) ^ 2 - meshPoint a h k ^ 2))) := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hm := halfOpenMass_tendsto hα hαβ
  simpa [upperSeq, mul_assoc] using
    ((tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ => Real.exp (-(C / 2) * meshPoint a h k))
        atTop
        (𝓝 (Real.exp (-(C / 2) * meshPoint a h k)))).mul hm)

private lemma weighted_block_squeeze_mesh
    {C a h : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hh : 0 < h)
    (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      lowerSeq C a h k n
        ≤ blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n ∧
      blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n
        ≤ upperSeq C a h k n := by
  have hα : 0 ≤ meshPoint a h k :=
    meshPoint_nonneg ha hh.le k
  have hαβ : meshPoint a h k < meshPoint a h (k + 1) :=
    meshPoint_succ_lt hh k
  have hs :=
    weighted_window_block_squeeze
      (C := C)
      (α := meshPoint a h k)
      (β := meshPoint a h (k + 1))
      hC hα hαβ
  filter_upwards [hs] with n hn
  simpa [blockSum, lowerSeq, upperSeq, halfOpenMass, mul_assoc] using hn

/--
For a fixed uniform mesh, the full block is eventually squeezed between the
lower and upper mesh sums, with an arbitrary additive tolerance coming only
from the convergence of the block masses.
-/
theorem blockSum_eventually_between_mesh_eps
    {C a b : ℝ} (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      lowerMesh C a ((b - a) / (N : ℝ)) N - ε
        ≤ blockSum C a b n ∧
      blockSum C a b n
        ≤ upperMesh C a ((b - a) / (N : ℝ)) N + ε := by
  classical
  set h : ℝ := (b - a) / (N : ℝ) with hdef
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hhpos : 0 < h := by
    rw [hdef]
    exact div_pos (sub_pos.mpr hab) hNposR
  have hhnonneg : 0 ≤ h := hhpos.le
  have hb_eq : b = a + (N : ℝ) * h := by
    rw [hdef]
    field_simp
  have hlow_tendsto :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range N, lowerSeq C a h k n)
        atTop
        (𝓝 (lowerMesh C a h N)) := by
    dsimp only [lowerMesh]
    exact tendsto_finset_sum (Finset.range N) (by
      intro k _hk
      exact lowerSeq_tendsto (C := C) (a := a) (h := h) ha hhpos k)
  have hup_tendsto :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range N, upperSeq C a h k n)
        atTop
        (𝓝 (upperMesh C a h N)) := by
    dsimp only [upperMesh]
    exact tendsto_finset_sum (Finset.range N) (by
      intro k _hk
      exact upperSeq_tendsto (C := C) (a := a) (h := h) ha hhpos k)
  have hsq_all :
      ∀ᶠ n : ℕ in atTop,
        ∀ k ∈ Finset.range N,
          lowerSeq C a h k n
            ≤ blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n ∧
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n
            ≤ upperSeq C a h k n := by
    rw [Filter.eventually_all_finset]
    intro k _hk
    exact weighted_block_squeeze_mesh (C := C) (a := a) (h := h) hC ha hhpos k
  have hlow_close :
      ∀ᶠ n : ℕ in atTop,
        |(∑ k ∈ Finset.range N, lowerSeq C a h k n) -
          lowerMesh C a h N| < ε := by
    simpa [Real.dist_eq] using
      hlow_tendsto.eventually (Metric.ball_mem_nhds (lowerMesh C a h N) hε)
  have hup_close :
      ∀ᶠ n : ℕ in atTop,
        |(∑ k ∈ Finset.range N, upperSeq C a h k n) -
          upperMesh C a h N| < ε := by
    simpa [Real.dist_eq] using
      hup_tendsto.eventually (Metric.ball_mem_nhds (upperMesh C a h N) hε)
  filter_upwards [hsq_all, hlow_close, hup_close] with n hsq hlow hup
  have hpartition :
      blockSum C a b n =
        ∑ k ∈ Finset.range N,
          blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
    conv_lhs => rw [hb_eq]
    exact blockSum_arith_partition C a h hhnonneg N n
  have hlow_sum :
      (∑ k ∈ Finset.range N, lowerSeq C a h k n)
        ≤
      ∑ k ∈ Finset.range N,
        blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (hsq k hk).1
  have hup_sum :
      (∑ k ∈ Finset.range N,
        blockSum C (meshPoint a h k) (meshPoint a h (k + 1)) n)
        ≤
      ∑ k ∈ Finset.range N, upperSeq C a h k n := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (hsq k hk).2
  constructor
  · have hclose_lower :
        lowerMesh C a h N - ε
          <
        ∑ k ∈ Finset.range N, lowerSeq C a h k n := by
      have h1 := (abs_lt.mp hlow).1
      linarith
    rw [hpartition]
    exact le_trans hclose_lower.le hlow_sum
  · have hclose_upper :
        (∑ k ∈ Finset.range N, upperSeq C a h k n)
          <
        upperMesh C a h N + ε := by
      have h1 := (abs_lt.mp hup).2
      linarith
    rw [hpartition]
    exact le_trans hup_sum hclose_upper.le

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model
