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
    (hd : 1 ≤ d) (hsvb : b ≤ Real.sqrt (v : ℝ))
    (hA : (rnk v : ℝ) - (d : ℝ) + 3 * b / 2 + 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) ≤ 3 * Real.sqrt (v : ℝ))
    (hB : 3 * Real.sqrt (v : ℝ) ≤ (rnk v : ℝ) - (d : ℝ) + 1 + 3 * a / 2)
    (hmlo : a * Real.sqrt (v : ℝ) < (m : ℝ)) (hmhi : (m : ℝ) ≤ b * Real.sqrt (v : ℝ)) :
    rnk v - rnk (v - m) = d := by
  have hsv : 0 < Real.sqrt (v : ℝ) := lt_of_lt_of_le (by linarith) hsvb
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
      have : b < Real.sqrt (v : ℝ) := lt_of_lt_of_le hab (by linarith [hsvb, hab])
      nlinarith [hsv]
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
    rw [hgdef]; rw [hgap]
    -- m/(√v+√(v−m)) ≤ m/√v ≤ b
    have hden : Real.sqrt (v : ℝ) ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by linarith
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / Real.sqrt (v : ℝ) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hsv hden
    have h2 : (m : ℝ) / Real.sqrt (v : ℝ) ≤ b := by
      rw [div_le_iff₀ hsv]; linarith [hmhi]
    rw [hgap] at *; linarith [h1, h2]
  have hsvm_lb : Real.sqrt (v : ℝ) - b ≤ Real.sqrt ((v - m : ℕ) : ℝ) := by
    rw [hgdef] at hg_ub_simple; linarith
  -- UPPER side: 3√(v−m) < 3√v − 3a/2,  via g > a/2
  have hg_lb : (a : ℝ) / 2 < g := by
    rw [hgdef, hgap]
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
    rw [hgdef, hgap]
    have hden_lb : 2 * Real.sqrt (v : ℝ) - b ≤ Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ) := by
      linarith [hsvm_lb]
    have hden_pos : 0 < 2 * Real.sqrt (v : ℝ) - b := by linarith [hsvb, hab, ha]
    have h1 : (m : ℝ) / (Real.sqrt (v : ℝ) + Real.sqrt ((v - m : ℕ) : ℝ))
        ≤ (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      apply div_le_div_of_nonneg_left (by exact_mod_cast Nat.zero_le m) hden_pos hden_lb
    have h2 : (m : ℝ) / (2 * Real.sqrt (v : ℝ) - b) ≤ b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b) := by
      apply div_le_div_of_nonneg_right hmhi hden_pos
    have h3 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
        ≤ 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2 := by
      -- RHS = b²/(2√v) + b/2;  LHS − b/2 = b²/(2(2√v−b)) ≤ b²/(2√v)
      have hrhs_eq : 3 * b ^ 2 / (2 * Real.sqrt (v : ℝ)) / 3 + b / 2
          = b ^ 2 / (2 * Real.sqrt (v : ℝ)) + b / 2 := by ring
      rw [hrhs_eq]
      have hstep1 : b * Real.sqrt (v : ℝ) / (2 * Real.sqrt (v : ℝ) - b)
          = b ^ 2 / (2 * (2 * Real.sqrt (v : ℝ) - b)) + b / 2 := by
        field_simp
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
  have hdle : (d : ℝ) ≤ (rnk v : ℝ) := by
    have : (0:ℝ) ≤ 3 * Real.sqrt ((v - m : ℕ) : ℝ) := by positivity
    linarith [hlower2]
  have hdleN : d ≤ rnk v := by exact_mod_cast hdle
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

end AnalyticCombinatorics.Ch8.Partitions.Erdos
