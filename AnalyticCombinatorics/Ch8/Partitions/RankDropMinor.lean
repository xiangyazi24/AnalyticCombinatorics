import AnalyticCombinatorics.Ch8.Partitions.RankDropKer
import AnalyticCombinatorics.Ch8.Partitions.KernelWindow

/-!
# T2.1 Step 1a: the phase-uniform per-drop minorization

The pointwise rank-drop local limit `rankDropKer v d → p d` is FALSE for the floor rank
`rnk v = ⌊3√v⌋` (the drop-`d` set is a `y = m/√v`-window whose edges SLIDE with `frac(3√v)`).
The engine, however, only needs a one-sided pair: the exp-tail majorant (banked in
`RankDropKer.lean`, `Pker_rankDrop_tail_majorant`) and a **phase-uniform per-drop minorization**

  `∃ η > 0, ∀ᶠ v, η ≤ rankDropKer v 1 ∧ η ≤ rankDropKer v 2`,

which is this file's `Pker_rankDrop_minorization`.

The minorization is TRUE but cannot use the banked per-`(a,b)` window limit `erdos_kernel_window`
directly: no *single* fixed `(a,b)` y-sub-window lies in the drop-1 set for all phases (the drop-1
windows over phases have empty intersection: `frac=0` gives `(0,2/3]`, `frac→1` gives `(2/3,4/3]`).

**Strategy (uniform-in-endpoints via a finite phase cover).**  A fixed y-sub-window `(a,b]` maps
entirely into the floor-induced drop-`d` set exactly when the phase `t = 3√v − ⌊3√v⌋` lies in the
open interval `(3b/2 − d, 3a/2 − d + 1)`.  Finitely many fixed sub-windows whose `t`-intervals cover
`[0,1)` therefore certify, for *every* phase, at least one sub-window entirely inside the drop-`d`
set; its window mass is bounded below by the banked positive limit `modelIntegral C a b`.  Taking
`η := min over the finite family of (modelIntegral C a b)/2 > 0` gives a phase-uniform bound.

The analytic heart is `drop_eq_of_window_mem`: every integer `m ∈ (a√v, b√v]`, under the phase
condition, has rank-drop exactly `d`.  This uses the sqrt-gap algebra of `window_rank_drop`
two-sidedly (`√v − √(v−m) = m/(√v+√(v−m))`, sandwiched by `m/(2√v)` and `m/(2√v−b)`).

Opus-authored.  Imports the banked bricks; does not modify them.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Filter Topology BigOperators Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- **Sqrt-gap two-sided bound.**  For `1 ≤ m`, `m < v`, the sqrt gap `g = √v − √(v−m)` satisfies
`m/(2√v) ≤ g ≤ m/(2√v − √v·(m/v))`… we use the cleaner pair: `m/(2√v) ≤ g` and, when
`m ≤ b√v < 2v`, `g ≤ m/(2√v − b√v/√v·…)`.  Concretely: `g·(√v + √(v−m)) = m`, and
`√v − b ≤ √(v−m) ≤ √v`. -/
lemma sqrt_gap_bounds {v m : ℕ} (hm1 : 1 ≤ m) (hmv : m < v) :
    Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ)
        = (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ)) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hcast : ((v - m : ℕ) : ℝ) = (v : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hmv)]
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hsvm : 0 ≤ Real.sqrt ((v - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsumpos : 0 < Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by linarith
  have hprod : (Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ))
      * (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ)) = (m : ℝ) := by
    have e1 : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hvpos.le
    have e2 : Real.sqrt ((v - m : ℕ) : ℝ) ^ 2 = (v : ℝ) - (m : ℝ) := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  rw [eq_div_iff (ne_of_gt hsumpos)]
  exact hprod

/-- **Membership in the drop-`d` set.**  Fix `0 < a < b` and `d ≥ 1`.  Suppose `v` is large enough
that `√v ≥ b` (so `2√v − b ≥ √v > 0`) and the **phase conditions** hold:

* (A, lower) `(rnk v : ℝ) − d + 3b/2 + 3b²/(2√v) ≤ 3√v`,
* (B, upper) `3√v ≤ (rnk v : ℝ) − d + 1 + 3a/2`.

Then every integer `m` with `a√v < m ≤ b√v` has rank-drop exactly `d`: `rnk v − rnk (v−m) = d`. -/
lemma drop_eq_of_window_mem {a b : ℝ} (ha : 0 < a) (hab : a < b) {d v m : ℕ}
    (hd : 1 ≤ d) (hrnkd : d ≤ rnk v) (hsvb : b < Real.sqrt (v : ℝ))
    (hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) ≤ 3 * Real.sqrt (v : ℝ))
    (hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2)
    (hmlo : a * Real.sqrt (v : ℝ) < (m : ℝ)) (hmhi : (m : ℝ) ≤ b * Real.sqrt (v : ℝ)) :
    rnk v - rnk (v - m) = d := by
  have hsv : 0 < Real.sqrt (v : ℝ) := lt_trans (by linarith) hsvb
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    by_contra h
    push_neg at h
    have : (v : ℝ) = 0 := le_antisymm h (by positivity)
    rw [this, Real.sqrt_zero] at hsv; exact (lt_irrefl _ hsv)
  have hvN : 0 < v := by exact_mod_cast hvpos
  -- m ≥ 1 and m < v
  have hm1 : 1 ≤ m := by
    by_contra h
    push_neg at h
    interval_cases m
    · simp only [Nat.cast_zero] at hmlo
      nlinarith [hmlo, ha, hsv]
  have hmlt : m < v := by
    -- m ≤ b√v ≤ √v·√v = v, and strict since b<√v... use m ≤ b√v and b ≤ √v
    have hmv : (m : ℝ) ≤ b * Real.sqrt (v : ℝ) := hmhi
    have hbsv : b * Real.sqrt (v : ℝ) < Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) := by
      nlinarith [hsv, hsvb]
    have : (m : ℝ) < (v : ℝ) := by
      rw [Real.mul_self_sqrt hvpos.le] at hbsv; linarith
    exact_mod_cast this
  -- gap algebra
  have hsvm0 : 0 ≤ Real.sqrt ((v - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsvm_le : Real.sqrt ((v - m : ℕ) : ℝ) ≤ Real.sqrt (v : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le v m)
  have hgap := sqrt_gap_bounds hm1 hmlt
  set g : ℝ := Real.sqrt (v : ℝ) - Real.sqrt ((v - m : ℕ) : ℝ) with hgdef
  -- bound √(v−m) ≥ √v − b  (since g ≤ m/√v ≤ b)
  have hg_ub_simple : g ≤ b := by
    rw [hgap]
    -- m/(√v+√(v−m)) ≤ m/√v ≤ b
    have hden : Real.sqrt (v : ℝ) ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by linarith
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / Real.sqrt (v : ℝ) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hsv hden
    have h2 : (m : ℝ) / Real.sqrt (v : ℝ) ≤ b := by
      rw [div_le_iff₀ hsv]; linarith [hmhi]
    linarith [h1, h2]
  have hsvm_lb : Real.sqrt (v : ℝ) - b ≤ Real.sqrt ((v - m : ℕ) : ℝ) := by
    have : g ≤ b := hg_ub_simple
    rw [hgdef] at this; linarith
  -- UPPER side: 3√(v−m) < 3√v − 3a/2,  via g > a/2
  have hg_lb : (a : ℝ) / 2 < g := by
    rw [hgap]
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))]
    -- a/2·(√v+√(v−m)) ≤ a/2·(2√v) = a√v < m
    have : a / 2 * (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ a / 2 * (2 * Real.sqrt (v : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ a/2)
      linarith [hsvm_le]
    have ha2 : a / 2 * (2 * Real.sqrt (v : ℝ)) = a * Real.sqrt (v : ℝ) := by ring
    linarith [hmlo]
  have hupper : 3 * Real.sqrt ((v - m : ℕ) : ℝ) < 3 * Real.sqrt (v : ℝ) - 3 * a / 2 := by
    have : Real.sqrt ((v - m : ℕ) : ℝ) = Real.sqrt (v : ℝ) - g := by rw [hgdef]; ring
    rw [this]; linarith [hg_lb]
  -- LOWER side: 3√(v−m) ≥ 3√v − 3b/2 − 3b²/(2√v),  via g ≤ b√v/(2√v−b)
  have hg_ub : g ≤ 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2 := by
    -- g = m/(√v+√(v−m)) ≤ b√v/(2√v−b);  b√v/(2√v−b) − b/2 = b²/(2(2√v−b)) ≤ b²/(2√v)
    rw [hgap]
    have hden_lb : 2 * Real.sqrt (v : ℝ) - b ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by
      linarith [hsvm_lb]
    have hden_pos : 0 < 2 * Real.sqrt (v : ℝ) - b := by linarith [hsvb, hab, ha]
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hden_pos hden_lb
    have h2 : (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) ≤ b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      gcongr
    have h3 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
        ≤ 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2 := by
      -- RHS = b²/(2√v) + b/2;  LHS − b/2 = b²/(2(2√v−b)) ≤ b²/(2√v)
      have hrhs_eq : 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2
          = b ^ 2 / (2 * Real.sqrt (v : ℝ)) + b / 2 := by ring
      rw [hrhs_eq]
      have hstep1 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
          = b ^ 2 / (2 * (2 * Real.sqrt (v : ℝ) - b)) + b / 2 := by
        rw [div_add_div _ _ (by positivity : 2 * (2 * Real.sqrt (v:ℝ) - b) ≠ 0)
              (by norm_num : (2:ℝ) ≠ 0), div_eq_div_iff (by positivity) (by positivity)]
        ring
      rw [hstep1]
      have hmono : b ^ 2 / (2 * (2 * Real.sqrt (v : ℝ) - b)) ≤ b ^ 2 / (2 * Real.sqrt (v : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hsvb, hab, ha]
      linarith [hmono]
    linarith [h1, h2, h3]
  have hlower : 3 * Real.sqrt (v : ℝ) - 3 * b / 2 - 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
      ≤ 3 * Real.sqrt ((v - m : ℕ) : ℝ) := by
    have : Real.sqrt ((v - m : ℕ) : ℝ) = Real.sqrt (v : ℝ) - g := by rw [hgdef]; ring
    rw [this]; nlinarith [hg_ub]
  -- Now convert to rnk via floor and phase conditions
  -- rnk(v−m) = ⌊3√(v−m)⌋
  have hrnk_eq : rnk (v - m) = ⌊3 * Real.sqrt ((v - m : ℕ) : ℝ)⌋₊ := rfl
  -- L := rnk v; L ≤ 3√v < L+1
  obtain ⟨hLle, hLlt⟩ := rnk_sqrt_bounds v
  -- d ≤ rnk v (so rnk v - d is a sensible ℕ subtraction) : from phase A and B
  -- Upper bound on rnk(v−m): 3√(v−m) < L − d + 1  ⟹  rnk(v−m) ≤ L − d
  have hupper2 : 3 * Real.sqrt ((v - m : ℕ) : ℝ) < (rnk v : ℝ) - (d : ℝ) + 1 := by
    linarith [hupper, hB]
  have hlower2 : (rnk v : ℝ) - (d : ℝ) ≤ 3 * Real.sqrt ((v - m : ℕ) : ℝ) := by
    linarith [hlower, hA]
  -- need rnk v ≥ d
  have hdleN : d ≤ rnk v := hrnkd
  have hdle : (d : ℝ) ≤ (rnk v : ℝ) := by exact_mod_cast hdleN
  -- rnk(v−m) ≤ rnk v − d
  have hub_nat : rnk (v - m) ≤ rnk v - d := by
    rw [hrnk_eq]
    -- ⌊3√(v−m)⌋ < (rnk v − d) + 1 in ℕ, from 3√(v−m) < rnk v − d + 1 in ℝ
    have hfl : ⌊3 * Real.sqrt ((v - m : ℕ) : ℝ)⌋₊ < (rnk v - d) + 1 := by
      apply Nat.floor_lt' (by omega : (rnk v - d) + 1 ≠ 0) |>.mpr
      push_cast
      rw [Nat.cast_sub hdleN]
      linarith [hupper2]
    omega
  -- rnk(v−m) ≥ rnk v − d
  have hlb_nat : rnk v - d ≤ rnk (v - m) := by
    rw [hrnk_eq]
    apply Nat.le_floor
    push_cast
    have : ((rnk v - d : ℕ) : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) := by
      rw [Nat.cast_sub hdleN]
    linarith [hlower2, this]
  have : rnk (v - m) = rnk v - d := le_antisymm hub_nat hlb_nat
  omega

/-- **Window-mass minorization of one drop.**  Under the phase conditions of
`drop_eq_of_window_mem` (for a fixed `(a,b)` and drop `d`), the rank-drop mass at `d` is at least
the (reflected) window mass `kernelWindow a b v / kernelMass v`: every step into the y-window
`(a√v, b√v]` is a drop-`d` step. -/
lemma rankDropKer_ge_window {a b : ℝ} (ha : 0 < a) (hab : a < b) {d v : ℕ}
    (hd : 1 ≤ d) (hrnkd : d ≤ rnk v) (hsvb : b < Real.sqrt (v : ℝ))
    (hkpos : 0 < kernelMass v)
    (hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
        ≤ 3 * Real.sqrt (v : ℝ))
    (hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2) :
    kernelWindow a b v / kernelMass v ≤ rankDropKer v d := by
  classical
  have hsvpos : (0 : ℝ) < Real.sqrt (v : ℝ) := by linarith [hsvb, ha, hab]
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt (Nat.cast_nonneg v)
    nlinarith [hsvpos, hsq]
  have hvN : 0 < v := by exact_mod_cast hvpos
  -- reflect the window mass / kernelMass into the predecessor coordinate as a masked Pker-sum
  have hreflect : kernelWindow a b v / kernelMass v
      = ∑ k ∈ Finset.Icc 1 (v - 1),
          (if a * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ)
              ∧ ((v - k : ℕ) : ℝ) ≤ b * Real.sqrt (v : ℝ)
            then Pker v k else 0) := by
    rw [kernelWindow, ← sum_Icc_reflect_sub v
      (fun m => if a * Real.sqrt (v : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ b * Real.sqrt (v : ℝ)
        then erdosWeight v m else 0), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hw : a * Real.sqrt (v : ℝ) < ((v - k : ℕ) : ℝ)
        ∧ ((v - k : ℕ) : ℝ) ≤ b * Real.sqrt (v : ℝ)
    · rw [if_pos hw, if_pos hw]
      unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
    · rw [if_neg hw, if_neg hw, zero_div]
  rw [hreflect, ← Finset.sum_filter]
  unfold rankDropKer
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · -- the window-filter ⊆ the drop-d filter
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    -- m := v − k ∈ (a√v, b√v] ⟹ drop = d
    have hdrop := drop_eq_of_window_mem ha hab (d := d) (v := v) (m := v - k)
      hd hrnkd hsvb hA hB hw1 hw2
    rwa [Nat.sub_sub_self (by omega : k ≤ v)] at hdrop
  · intro k _ _; exact Pker_nonneg v k

/-- The integral of the positive Erdős density over a nondegenerate interval is positive. -/
lemma modelIntegral_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : 0 < Model.modelIntegral C a b := by
  have hC := C_pos
  rw [Model.modelIntegral]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · have hc : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y) := by
      have h1 : Continuous fun y : ℝ => (Real.pi ^ 2 / 6) * y :=
        continuous_const.mul continuous_id
      have h2 : Continuous fun y : ℝ => Real.exp (-(C / 2) * y) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
      exact h1.mul h2
    exact hc.intervalIntegrable _ _
  · intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_le_of_lt ha hy.1
    have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
    have he : (0 : ℝ) < Real.exp (-(C / 2) * y) := Real.exp_pos _
    nlinarith [mul_pos (mul_pos hπ hy0) he]
  · exact hab

/-- **Eventual window-mass-over-total lower bound** for a fixed nondegenerate `(a,b)`:
`kernelWindow a b v / kernelMass v ≥ modelIntegral C a b / 2 > 0` eventually in `v`. -/
lemma window_div_mass_ge_eventually {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ v : ℕ in atTop,
      Model.modelIntegral C a b / 2 ≤ kernelWindow a b v / kernelMass v := by
  have hIpos := modelIntegral_pos ha hab
  -- window mass → modelIntegral, so eventually ≥ (3/4)·I
  have hwin := Model.erdos_kernel_window (a := a) (b := b) ha hab
  have hwin_ge : ∀ᶠ v : ℕ in atTop,
      (3 / 4) * Model.modelIntegral C a b ≤ kernelWindow a b v := by
    have hev := (tendsto_order.1 hwin).1 ((3 / 4) * Model.modelIntegral C a b) (by nlinarith [hIpos])
    filter_upwards [hev] with v hv
    -- kernelWindow a b v is definitionally the masked sum
    exact hv.le
  -- kernelMass → 1, so eventually kernelMass ≤ 3/2 and ≥ 1/2 > 0
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hKsmall : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  filter_upwards [hwin_ge, hKev, hKsmall, eventually_ge_atTop 1] with v hwinv hKv hKsv hv1
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKv
  have hSge : (1 : ℝ) / 2 ≤ kernelMass v := by linarith [hKsv]
  have hSle : kernelMass v ≤ 3 / 2 := by linarith [hKsv]
  have hSpos : (0 : ℝ) < kernelMass v := by linarith
  -- I/2 ≤ (3/4)I / (3/2) ≤ kernelWindow / kernelMass
  rw [le_div_iff₀ hSpos]
  -- I/2 · kernelMass ≤ I/2 · (3/2) = (3/4)I ≤ kernelWindow
  calc Model.modelIntegral C a b / 2 * kernelMass v
      ≤ Model.modelIntegral C a b / 2 * (3 / 2) := by
        apply mul_le_mul_of_nonneg_left hSle (by linarith [hIpos])
    _ = (3 / 4) * Model.modelIntegral C a b := by ring
    _ ≤ kernelWindow a b v := hwinv

/-- **Subwindow drop bound, in `t`-band form.**  Fix `0 < a < b`, drop `d ≥ 1`, and rational
`t`-band endpoints `tlo ≤ thi` with strict margins
`3b/2 − d < tlo` and `thi < 3a/2 − d + 1`.  Then eventually in `v`: whenever the phase
`t := 3√v − rnk v` lies in `[tlo, thi]`, the rank-drop mass at `d` is `≥ modelIntegral C a b / 2`. -/
lemma rankDropKer_ge_const_of_tband {a b tlo thi : ℝ} (ha : 0 < a) (hab : a < b)
    {d : ℕ} (hd : 1 ≤ d) (htle : tlo ≤ thi)
    (hmA : 3 * b / 2 - (d : ℝ) < tlo) (hmB : thi < 3 * a / 2 - (d : ℝ) + 1) :
    ∀ᶠ v : ℕ in atTop,
      (tlo ≤ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ)
        ∧ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) ≤ thi) →
      Model.modelIntegral C a b / 2 ≤ rankDropKer v d := by
  have hIge := window_div_mass_ge_eventually (a := a) (b := b) ha.le hab
  -- error term ε_v = 3b²/(2√v) → 0; need ε_v < tlo − (3b/2 − d)
  set εmar : ℝ := tlo - (3 * b / 2 - (d : ℝ)) with hεdef
  have hεpos : 0 < εmar := by rw [hεdef]; linarith [hmA]
  have herr : ∀ᶠ v : ℕ in atTop, 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) ≤ εmar := by
    have htend : Tendsto (fun v : ℕ => 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_le_const hεpos
  -- need √v > b and rnk v ≥ d eventually
  have hsvb : ∀ᶠ v : ℕ in atTop, b < Real.sqrt (v : ℝ) := by
    have htend : Tendsto (fun v : ℕ => Real.sqrt (v : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact htend.eventually_gt_atTop b
  have hrnkd : ∀ᶠ v : ℕ in atTop, d ≤ rnk v := by
    -- rnk v = ⌊3√v⌋ ≥ d as soon as 3√v ≥ d
    have hsq : Tendsto (fun v : ℕ => 3 * Real.sqrt (v : ℝ)) atTop atTop := by
      apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 3)
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsq.eventually_ge_atTop ((d : ℝ))] with v hv
    show d ≤ ⌊3 * Real.sqrt (v : ℝ)⌋₊
    exact Nat.le_floor (by push_cast; linarith [hv])
  have hkpos : ∀ᶠ v : ℕ in atTop, 0 < kernelMass v := by
    obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
    have hKsmall : ∀ᶠ v : ℕ in atTop, K / (v : ℝ) ≤ 1 / 2 := by
      have htend : Tendsto (fun v : ℕ => K / (v : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
      exact htend.eventually_le_const (by norm_num)
    filter_upwards [hKev, hKsmall] with v hKv hKsv
    obtain ⟨hSlo, _⟩ := abs_le.1 hKv
    linarith [hKsv]
  filter_upwards [hIge, herr, hsvb, hrnkd, hkpos] with v hIgev herrv hsvbv hrnkdv hkposv
  intro ⟨htlo, hthi⟩
  -- derive phase conditions A, B from t-band + margins
  have hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ))
      ≤ 3 * Real.sqrt (v : ℝ) := by
    -- 3√v − rnk v ≥ tlo ≥ 3b/2 − d + ε_v
    have : tlo ≥ 3 * b / 2 - (d : ℝ) + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) := by
      rw [hεdef] at *; linarith [herrv]
    linarith [htlo, this]
  have hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2 := by
    -- 3√v − rnk v ≤ thi < 3a/2 − d + 1
    linarith [hthi, hmB]
  exact le_trans hIgev (rankDropKer_ge_window ha hab hd hrnkdv hsvbv hkposv hA hB)

/-! ### The eight subwindows of the finite phase cover

For drop `d = 1` (four windows) and drop `d = 2` (four windows), each with rational endpoints whose
`t`-band `[3b/2−d, 3a/2−d+1]` covers a piece of `[0,1)`; the eight `t`-bands together cover `[0,1)`
twice (once for each drop), as verified numerically.  We package each subwindow's `t`-band drop
bound and take `η` to be the minimum of the eight `modelIntegral/2` values. -/

/-- **T2.1 Step 1a — phase-uniform per-drop minorization.**  There is `η > 0` such that, eventually
in `v`, both `rankDropKer v 1 ≥ η` and `rankDropKer v 2 ≥ η`.  The drop-`d` `m`-window slides with
`frac(3√v)`, so no single fixed sub-window certifies the mass; instead a finite family of fixed
sub-windows whose phase `t`-bands cover `[0,1)` (separately for `d = 1` and `d = 2`) is used, and
`η` is the minimum of their (positive) window half-masses. -/
theorem Pker_rankDrop_minorization :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ v : ℕ in atTop,
      η ≤ rankDropKer v 1 ∧ η ≤ rankDropKer v 2 := by
  -- the eight half-integrals
  set I1 := Model.modelIntegral C 0.10 0.40 / 2 with hI1
  set I2 := Model.modelIntegral C 0.40 0.66 / 2 with hI2
  set I3 := Model.modelIntegral C 0.62 0.90 / 2 with hI3
  set I4 := Model.modelIntegral C 0.86 1.14 / 2 with hI4
  set J1 := Model.modelIntegral C 0.72 1.00 / 2 with hJ1
  set J2 := Model.modelIntegral C 0.96 1.24 / 2 with hJ2
  set J3 := Model.modelIntegral C 1.20 1.48 / 2 with hJ3
  set J4 := Model.modelIntegral C 1.44 1.74 / 2 with hJ4
  -- positivity of each
  have pI1 : 0 < I1 := by rw [hI1]; have := modelIntegral_pos (a := 0.10) (b := 0.40) (by norm_num) (by norm_num); linarith
  have pI2 : 0 < I2 := by rw [hI2]; have := modelIntegral_pos (a := 0.40) (b := 0.66) (by norm_num) (by norm_num); linarith
  have pI3 : 0 < I3 := by rw [hI3]; have := modelIntegral_pos (a := 0.62) (b := 0.90) (by norm_num) (by norm_num); linarith
  have pI4 : 0 < I4 := by rw [hI4]; have := modelIntegral_pos (a := 0.86) (b := 1.14) (by norm_num) (by norm_num); linarith
  have pJ1 : 0 < J1 := by rw [hJ1]; have := modelIntegral_pos (a := 0.72) (b := 1.00) (by norm_num) (by norm_num); linarith
  have pJ2 : 0 < J2 := by rw [hJ2]; have := modelIntegral_pos (a := 0.96) (b := 1.24) (by norm_num) (by norm_num); linarith
  have pJ3 : 0 < J3 := by rw [hJ3]; have := modelIntegral_pos (a := 1.20) (b := 1.48) (by norm_num) (by norm_num); linarith
  have pJ4 : 0 < J4 := by rw [hJ4]; have := modelIntegral_pos (a := 1.44) (b := 1.74) (by norm_num) (by norm_num); linarith
  -- η := min of the eight
  set η : ℝ := min (min (min I1 I2) (min I3 I4)) (min (min J1 J2) (min J3 J4)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (lt_min pI1 pI2) (lt_min pI3 pI4))
      (lt_min (lt_min pJ1 pJ2) (lt_min pJ3 pJ4))
  -- the eight t-band drop bounds
  have b1 := rankDropKer_ge_const_of_tband (a := 0.10) (b := 0.40) (tlo := 0) (thi := 0.1)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b2 := rankDropKer_ge_const_of_tband (a := 0.40) (b := 0.66) (tlo := 0.1) (thi := 0.5)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rankDropKer_ge_const_of_tband (a := 0.62) (b := 0.90) (tlo := 0.5) (thi := 0.85)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b4 := rankDropKer_ge_const_of_tband (a := 0.86) (b := 1.14) (tlo := 0.85) (thi := 1)
    (by norm_num) (by norm_num) (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c1 := rankDropKer_ge_const_of_tband (a := 0.72) (b := 1.00) (tlo := 0) (thi := 0.05)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 := rankDropKer_ge_const_of_tband (a := 0.96) (b := 1.24) (tlo := 0.05) (thi := 0.4)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c3 := rankDropKer_ge_const_of_tband (a := 1.20) (b := 1.48) (tlo := 0.4) (thi := 0.75)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c4 := rankDropKer_ge_const_of_tband (a := 1.44) (b := 1.74) (tlo := 0.75) (thi := 1)
    (by norm_num) (by norm_num) (d := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- t ∈ [0,1) always
  have hphase : ∀ᶠ v : ℕ in atTop,
      0 ≤ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) ∧ 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) < 1 := by
    filter_upwards with v
    obtain ⟨h1, h2⟩ := rnk_sqrt_bounds v
    exact ⟨by linarith, by linarith⟩
  refine ⟨η, hηpos, ?_⟩
  filter_upwards [b1, b2, b3, b4, c1, c2, c3, c4, hphase]
    with v hb1 hb2 hb3 hb4 hc1 hc2 hc3 hc4 ⟨ht0, ht1⟩
  set t : ℝ := 3 * Real.sqrt (v : ℝ) - (rnk v : ℝ) with htdef
  -- η ≤ each I/J value
  have leI1 : η ≤ I1 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have leI2 : η ≤ I2 := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have leI3 : η ≤ I3 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have leI4 : η ≤ I4 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have leJ1 : η ≤ J1 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have leJ2 : η ≤ J2 := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have leJ3 : η ≤ J3 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have leJ4 : η ≤ J4 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  constructor
  · -- drop 1: pick subwindow by where t lies
    rcases le_or_gt t 0.1 with h | h
    · exact le_trans leI1 (hb1 ⟨ht0, h⟩)
    · rcases le_or_gt t 0.5 with h2 | h2
      · exact le_trans leI2 (hb2 ⟨le_of_lt h, h2⟩)
      · rcases le_or_gt t 0.85 with h3 | h3
        · exact le_trans leI3 (hb3 ⟨le_of_lt h2, h3⟩)
        · exact le_trans leI4 (hb4 ⟨le_of_lt h3, le_of_lt ht1⟩)
  · -- drop 2
    rcases le_or_gt t 0.05 with h | h
    · exact le_trans leJ1 (hc1 ⟨ht0, h⟩)
    · rcases le_or_gt t 0.4 with h2 | h2
      · exact le_trans leJ2 (hc2 ⟨le_of_lt h, h2⟩)
      · rcases le_or_gt t 0.75 with h3 | h3
        · exact le_trans leJ3 (hc3 ⟨le_of_lt h2, h3⟩)
        · exact le_trans leJ4 (hc4 ⟨le_of_lt h3, le_of_lt ht1⟩)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
