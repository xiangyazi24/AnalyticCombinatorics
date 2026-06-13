import AnalyticCombinatorics.Ch8.Partitions.PartitionRenewal
import AnalyticCombinatorics.Ch8.Partitions.RankBandEntrance

/-!
# TASK 11, Step E (partial): the local bounded-rank-drop lower bound

The honest local kernel content available from the banked window mass: from a state `n`, a uniformly
positive `Pker`-mass (`≥ ν/2`) lands at a predecessor whose rank drops by a **bounded** amount
(at most `7`) — the window steps `m ∈ (√n, 2√n]` drop rank by `rnk n − rnk(n−m) ∈ [1, 7]`.  This is the
local-limit lower bound the entrance-overlap analysis needs *at the ceiling* (a state sitting just
above a band lands inside it with positive mass).

This does **not** by itself give the first-entrance *overlap between two different starts*, nor does it
kill the overshoot escape at fixed band width — those are the renewal-overshoot equidistribution
content documented in `HANDOFF/TASK11-gap.md`.  It is the strongest fragment of Step E derivable from
the banked window mass, and is reusable for any renewal-coupling attempt.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- A window step `m ∈ (√n, 2√n]` drops rank by at most `7`: `rnk n − rnk (n−m) ≤ 7`, equivalently
`rnk n ≤ rnk (n−m) + 7`. -/
lemma window_rank_drop_bounded {n m : ℕ} (hn : 1 ≤ n) (hmn : m < n)
    (hmub : (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)) :
    rnk n ≤ rnk (n - m) + 7 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- √n − √(n−m) = m/(√n+√(n−m)) ≤ 2√n/√n = 2
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by rw [Nat.cast_sub (le_of_lt hmn)]
  have hsa : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsble : Real.sqrt ((n - m : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n m)
  have hsbnn : 0 ≤ Real.sqrt ((n - m : ℕ) : ℝ) := Real.sqrt_nonneg _
  -- (√n − √(n−m))·(√n + √(n−m)) = m
  have hprod : (Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ))
      * (Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ)) = (m:ℝ) := by
    have e1 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hnpos.le
    have e2 : Real.sqrt ((n-m:ℕ):ℝ) ^ 2 = (n:ℝ) - m := by
      rw [Real.sq_sqrt (by positivity), hcast]
    nlinarith [e1, e2]
  have hsumpos : 0 < Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ) := by linarith
  have hgap_le : Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ) ≤ 2 := by
    -- (√n − √(n−m)) = m / (√n+√(n−m)) ≤ 2√n / √n = 2
    have hgap_eq : Real.sqrt (n:ℝ) - Real.sqrt ((n-m:ℕ):ℝ)
        = (m:ℝ) / (Real.sqrt (n:ℝ) + Real.sqrt ((n-m:ℕ):ℝ)) := by
      rw [eq_div_iff (ne_of_gt hsumpos)]; exact hprod
    rw [hgap_eq, div_le_iff₀ hsumpos]
    nlinarith [hmub, hsble, hsbnn, hsa]
  -- rnk n = ⌊3√n⌋ ≤ 3√n < 3√(n−m) + 6 + 1 ≤ (rnk(n−m)+1) + 6 + ... carefully via floors
  have hfn : (rnk n : ℝ) ≤ 3 * Real.sqrt (n:ℝ) := (rnk_sqrt_bounds n).1
  have hfnm : 3 * Real.sqrt ((n-m:ℕ):ℝ) < (rnk (n-m) : ℝ) + 1 := (rnk_sqrt_bounds (n-m)).2
  -- 3√n ≤ 3√(n−m) + 6  (since √n − √(n−m) ≤ 2)
  have h3 : 3 * Real.sqrt (n:ℝ) ≤ 3 * Real.sqrt ((n-m:ℕ):ℝ) + 6 := by nlinarith [hgap_le]
  have hlt : (rnk n : ℝ) < (rnk (n-m) : ℝ) + 7 := by linarith
  have hnat : (rnk n : ℝ) < ((rnk (n-m) + 7 : ℕ) : ℝ) := by push_cast; linarith
  have : rnk n < rnk (n-m) + 7 := by exact_mod_cast hnat
  omega

/-- **Local bounded-rank-drop lower bound (the honest fragment of Step E).**  A uniformly positive
`Pker`-mass lands at a predecessor whose rank drops by a *bounded* amount (`∈ [1, 7]`): the window
steps `m ∈ (√n, 2√n]` carry mass `≥ ν > 0` and strictly drop rank (`window_rank_drop`) by at most `7`
(`window_rank_drop_bounded`).  After normalizing by `kernelMass n ≤ 2` the predecessor mass on the
bounded-drop band is `≥ ν/2`.  This is the local-limit lower bound an entrance-overlap argument needs
*at the ceiling*; it does not by itself give the cross-start overlap or kill the overshoot escape
(see `HANDOFF/TASK11-gap.md`). -/
theorem Pker_bounded_drop_mass_pos :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ n : ℕ in atTop,
      μ ≤ ∑ k ∈ (Finset.range n).filter
            (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k := by
  obtain ⟨ν, hνpos, hνmass⟩ := kernelWindow_one_two_pos
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  have hone : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  refine ⟨ν / 2, by positivity, ?_⟩
  filter_upwards [hνmass, hKev, hone, Filter.eventually_ge_atTop 2] with n hνn hKn hKn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKn
  have hS2 : kernelMass n ≤ 2 := by linarith [hSup, hKn1]
  have hSge : (1 : ℝ) / 2 ≤ kernelMass n := by linarith [hSlo, hKn1]
  have hSpos : (0 : ℝ) < kernelMass n := by linarith
  have hkey : kernelWindow 1 2 n / kernelMass n
      ≤ ∑ k ∈ (Finset.range n).filter
          (fun k => rnk n ≤ rnk k + 7 ∧ rnk k < rnk n), Pker n k := by
    have hreflect : kernelWindow 1 2 n / kernelMass n
        = ∑ k ∈ Finset.Icc 1 (n - 1),
            (if 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
                ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
              then Pker n k else 0) := by
      rw [kernelWindow, ← sum_Icc_reflect_sub n
        (fun m => if 1 * Real.sqrt (n : ℝ) < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
          then erdosWeight n m else 0), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases hw : 1 * Real.sqrt (n : ℝ) < ((n - k : ℕ) : ℝ)
          ∧ ((n - k : ℕ) : ℝ) ≤ 2 * Real.sqrt (n : ℝ)
      · rw [if_pos hw, if_pos hw]
        unfold Pker; rw [if_pos ⟨hk.1, by omega⟩]
      · rw [if_neg hw, if_neg hw, zero_div]
    rw [hreflect, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hw1, hw2⟩ := hk
      rw [Finset.mem_filter, Finset.mem_range]
      have hmlt : n - k < n := by omega
      have hsubeq : n - (n - k) = k := Nat.sub_sub_self (by omega : k ≤ n)
      -- strict drop
      have hdrop := window_rank_drop (n := n) (m := n - k) (by omega) hmlt (by
        rw [one_mul] at hw1; exact hw1)
      rw [hsubeq] at hdrop
      -- bounded drop ≤ 7
      have hbnd := window_rank_drop_bounded (n := n) (m := n - k) (by omega) hmlt (by
        exact hw2)
      rw [hsubeq] at hbnd
      exact ⟨by omega, hbnd, hdrop⟩
    · intro k _ _; exact Pker_nonneg n k
  refine le_trans ?_ hkey
  rw [le_div_iff₀ hSpos]
  nlinarith [hνn, hS2, hνpos]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
