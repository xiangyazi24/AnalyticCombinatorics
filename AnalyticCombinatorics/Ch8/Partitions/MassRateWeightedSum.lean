import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateMomentBound
import AnalyticCombinatorics.Ch8.Partitions.MassRateTailInvSq

/-!
# Mass-rate campaign: the weighted-decay summation bound (keystone for M₁, M₂)

For `f` bounded by `Cf` on `(0,1]` and by `Bf·e^{−z/2} + Df/z^{j+2}` on `(1,∞)`,

  `Σ'_{k≥1} k^j·|f(tk)| ≤ K/t^{j+1}`  on `0 < t ≤ 1`,

with `K = Cf·2^{j+1} + Bf·j!·4^{j+1} + 2 Df`.  Three buckets: near-origin (`k ≤ 1/t`, the
`Cf` bound), exponential tail (`tsum_pow_mul_geometric_le`), polynomial tail (`tail_inv_sq_shift`).
Instantiated for `M₁` (`j=1`, `f=boseReg0′`) and `M₂` (`j=2`, `f=boseReg0″`).  Opus-authored.
-/

set_option maxHeartbeats 4000000

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **Weighted-decay summation bound** (keystone). -/
lemma weighted_decay_sum_bound (j : ℕ) (f : ℝ → ℝ) (Cf Bf Df : ℝ)
    (hCf : 0 ≤ Cf) (hBf : 0 ≤ Bf) (hDf : 0 ≤ Df)
    (h01 : ∀ z : ℝ, 0 < z → z ≤ 1 → |f z| ≤ Cf)
    (htail : ∀ z : ℝ, 1 < z → |f z| ≤ Bf * Real.exp (-z / 2) + Df / z ^ (j + 2))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∑' k : ℕ, if k = 0 then (0:ℝ) else (k : ℝ) ^ j * |f (t * (k : ℝ))|)
      ≤ (Cf * 2 ^ (j + 1) + Bf * (Nat.factorial j) * 4 ^ (j + 1) + 2 * Df)
          / t ^ (j + 1) := by
  classical
  set a : ℕ → ℝ := fun k => if k = 0 then (0:ℝ) else (k : ℝ) ^ j * |f (t * (k : ℝ))| with hadef
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    simp only [hadef]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]; positivity
  -- N = ⌊1/t⌋
  have htinv_pos : 0 < 1 / t := by positivity
  set N : ℕ := ⌊1 / t⌋₊ with hNdef
  have htinv_ge1 : (1:ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact Nat.le_floor (by exact_mod_cast htinv_ge1)
  have hNle : (N : ℝ) ≤ 1 / t := Nat.floor_le htinv_pos.le
  have hNlt : 1 / t < (N : ℝ) + 1 := by
    rw [hNdef]; exact Nat.lt_floor_add_one (1 / t)
  have htN_le1 : t * (N : ℝ) ≤ 1 := by
    rw [mul_comm, ← le_div_iff₀ ht0]; exact hNle
  have htNp1_gt1 : 1 < t * ((N : ℝ) + 1) := by
    rw [mul_comm, ← div_lt_iff₀ ht0]; exact hNlt
  -- exp dominator summability
  have hr0 : (0:ℝ) ≤ Real.exp (-t / 2) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hexp_summ : Summable (fun k : ℕ => (k : ℝ) ^ j * Real.exp (-t / 2) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have hbasel_summ : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  -- tail summand bound (k = i+N+1 ≥ N+1, so t·k > 1)
  have htail_term : ∀ i : ℕ,
      a (i + N + 1) ≤ ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf
        + Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hk0 : (i + N + 1 : ℕ) ≠ 0 := by positivity
    simp only [hadef, if_neg hk0]
    set k : ℕ := i + N + 1 with hkdef
    have hkge : (N : ℝ) + 1 ≤ (k : ℝ) := by rw [hkdef]; push_cast; linarith
    have htk1 : 1 < t * (k : ℝ) :=
      lt_of_lt_of_le htNp1_gt1 (mul_le_mul_of_nonneg_left hkge ht0.le)
    have hb := htail (t * (k : ℝ)) htk1
    have hkpos : (0:ℝ) < (k : ℝ) := by positivity
    have hexp_eq : Real.exp (-(t * (k : ℝ)) / 2) = Real.exp (-t / 2) ^ k := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
    have htne : t ≠ 0 := ht0.ne'
    have hpoly_eq : (k : ℝ) ^ j * (Df / (t * (k : ℝ)) ^ (j + 2))
        = Df / t ^ (j + 2) * (1 / (k : ℝ) ^ 2) := by
      rw [mul_pow, show (k : ℝ) ^ (j + 2) = (k : ℝ) ^ j * (k : ℝ) ^ 2 from by rw [pow_add]]
      field_simp
    calc (k : ℝ) ^ j * |f (t * (k : ℝ))|
        ≤ (k : ℝ) ^ j * (Bf * Real.exp (-(t * (k : ℝ)) / 2) + Df / (t * (k : ℝ)) ^ (j + 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf
            + Df / t ^ (j + 2) * (1 / (k : ℝ) ^ 2) := by
          rw [mul_add, hexp_eq, hpoly_eq]; ring
  -- summable shifted dominators
  have hshift_exp : Summable (fun i : ℕ =>
      ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf) := by
    have hsh := (summable_nat_add_iff (N + 1)).mpr hexp_summ
    have := hsh.mul_right Bf
    refine this.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by ring
    rw [he]
  have hshift_poly : Summable (fun i : ℕ =>
      Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have hsh : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have := (summable_nat_add_iff (N + 1)).mpr hbasel_summ
      refine this.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]
    exact hsh.mul_left _
  -- summability of a
  have ha_summ : Summable a := by
    rw [← summable_nat_add_iff (N + 1)]
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hshift_exp.add hshift_poly)
    · have := ha_nonneg (i + N + 1)
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]; exact this
    · have := htail_term i
      have he : i + (N + 1) = i + N + 1 := by ring
      rw [he]; exact this
  -- decomposition
  have hsplit := (Summable.sum_add_tsum_nat_add (N + 1) ha_summ).symm
  rw [hsplit]
  -- FINITE BUCKET
  have hfin : (∑ k ∈ Finset.range (N + 1), a k) ≤ Cf * 2 ^ (j + 1) / t ^ (j + 1) := by
    have hterm : ∀ k ∈ Finset.range (N + 1), a k ≤ Cf * (N : ℝ) ^ j := by
      intro k hk
      simp only [hadef]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]; positivity
      · rw [if_neg hk0]
        have hkpos : (0:ℝ) < (k : ℝ) := by
          have : 0 < k := Nat.pos_of_ne_zero hk0; exact_mod_cast this
        have hkN : k ≤ N := by have := Finset.mem_range.mp hk; omega
        have htkpos : 0 < t * (k : ℝ) := by positivity
        have htk1 : t * (k : ℝ) ≤ 1 := by
          calc t * (k : ℝ) ≤ t * (N : ℝ) :=
                mul_le_mul_of_nonneg_left (by exact_mod_cast hkN) ht0.le
            _ ≤ 1 := htN_le1
        have hfb := h01 (t * (k : ℝ)) htkpos htk1
        have hkjN : (k : ℝ) ^ j ≤ (N : ℝ) ^ j :=
          pow_le_pow_left₀ hkpos.le (by exact_mod_cast hkN) j
        calc (k : ℝ) ^ j * |f (t * (k : ℝ))| ≤ (N : ℝ) ^ j * Cf :=
              mul_le_mul hkjN hfb (abs_nonneg _) (by positivity)
          _ = Cf * (N : ℝ) ^ j := by ring
    have hsum_le := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
    rw [Nat.cast_add, Nat.cast_one] at hsum_le
    refine le_trans hsum_le ?_
    have hNp1 : ((N : ℝ) + 1) ≤ 2 / t := by
      have h1 : (N : ℝ) + 1 ≤ 1 / t + 1 := by linarith [hNle]
      have h2 : 1 / t + 1 ≤ 2 / t := by
        rw [div_add' _ _ _ ht0.ne', div_le_div_iff₀ ht0 ht0]; nlinarith [htinv_ge1]
      linarith
    have hNjt : (N : ℝ) ^ j ≤ 1 / t ^ j := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (N:ℝ)) hNle j
      rwa [div_pow, one_pow] at h
    have hprod : ((N : ℝ) + 1) * (N : ℝ) ^ j ≤ (2 / t) * (1 / t ^ j) :=
      mul_le_mul hNp1 hNjt (by positivity) (by positivity)
    have hrw : (2 / t) * (1 / t ^ j) = 2 / t ^ (j + 1) := by rw [pow_succ]; field_simp
    calc ((N : ℝ) + 1) * (Cf * (N : ℝ) ^ j)
        = Cf * (((N : ℝ) + 1) * (N : ℝ) ^ j) := by ring
      _ ≤ Cf * (2 / t ^ (j + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hCf; rw [← hrw]; exact hprod
      _ = Cf * 2 / t ^ (j + 1) := by ring
      _ ≤ Cf * 2 ^ (j + 1) / t ^ (j + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hCf
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- TAIL BUCKET
  have htail_le : (∑' i : ℕ, a (i + N + 1))
      ≤ (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
        + (∑' i : ℕ, Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have ha_tail_summ : Summable (fun i : ℕ => a (i + N + 1)) :=
      (summable_nat_add_iff (N + 1)).mpr ha_summ
    rw [← Summable.tsum_add hshift_exp hshift_poly]
    exact ha_tail_summ.tsum_le_tsum htail_term (hshift_exp.add hshift_poly)
  -- exp bucket
  have hexp_tail : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
      ≤ Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by
    have hwhole_summ : Summable (fun k : ℕ => (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf) :=
      hexp_summ.mul_right Bf
    have hle_whole : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
        ≤ (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf) := by
      have hshift_eq : (∑' i : ℕ, ((i + N + 1 : ℕ) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + N + 1) * Bf)
          = ∑' i : ℕ, (((i + (N + 1) : ℕ)) : ℝ) ^ j * Real.exp (-t / 2) ^ (i + (N + 1)) * Bf := by
        apply tsum_congr; intro i
        have he : i + N + 1 = i + (N + 1) := by ring
        rw [he]
      rw [hshift_eq, (Summable.sum_add_tsum_nat_add (N + 1) hwhole_summ).symm]
      have hfin_nonneg : 0 ≤ ∑ k ∈ Finset.range (N + 1),
          (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf := by
        apply Finset.sum_nonneg; intro k _; positivity
      linarith
    refine le_trans hle_whole ?_
    have htsum_eq : (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k * Bf)
        = Bf * ∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k := by
      rw [← tsum_mul_left]; apply tsum_congr; intro k; ring
    rw [htsum_eq]
    have hbase := tsum_pow_mul_geometric_le j hr0 hr1
    have hden : t / 4 ≤ 1 - Real.exp (-t / 2) := by
      have h1 : t / 2 / 2 ≤ 1 - Real.exp (-(t / 2)) :=
        one_sub_exp_neg_ge_half (by linarith) (by linarith)
      rw [show -(t / 2) = -t / 2 from by ring] at h1
      linarith
    have hpow : (t / 4) ^ (j + 1) ≤ (1 - Real.exp (-t / 2)) ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) hden _
    have hbase2 : (∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k)
        ≤ (Nat.factorial j : ℝ) / (t / 4) ^ (j + 1) :=
      le_trans hbase (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
    have hrw : (Nat.factorial j : ℝ) / (t / 4) ^ (j + 1)
        = (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by rw [div_pow]; field_simp
    rw [hrw] at hbase2
    calc Bf * ∑' k : ℕ, (k : ℝ) ^ j * Real.exp (-t / 2) ^ k
        ≤ Bf * ((Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1)) :=
          mul_le_mul_of_nonneg_left hbase2 hBf
      _ = Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) := by ring
  -- poly bucket
  have hpoly_tail : (∑' i : ℕ, Df / t ^ (j + 2) * (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2))
      ≤ 2 * Df / t ^ (j + 1) := by
    rw [tsum_mul_left]
    have hbasel := tail_inv_sq_shift N
    have hstep : Df / t ^ (j + 2) * (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
        ≤ Df / t ^ (j + 2) * (2 / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hbasel (by positivity)
    refine le_trans hstep ?_
    have hN1t : 2 / ((N : ℝ) + 1) ≤ 2 * t := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hNlt, ht0, mul_pos ht0 (show (0:ℝ) < (N:ℝ)+1 by positivity)]
    calc Df / t ^ (j + 2) * (2 / ((N : ℝ) + 1))
        ≤ Df / t ^ (j + 2) * (2 * t) :=
          mul_le_mul_of_nonneg_left hN1t (by positivity)
      _ = 2 * Df / t ^ (j + 1) := by rw [pow_succ]; field_simp
  -- assemble
  have htailbd : (∑' i : ℕ, a (i + N + 1))
      ≤ Bf * (Nat.factorial j) * 4 ^ (j + 1) / t ^ (j + 1) + 2 * Df / t ^ (j + 1) :=
    le_trans htail_le (add_le_add hexp_tail hpoly_tail)
  have hfinal := add_le_add hfin htailbd
  refine le_trans hfinal (le_of_eq ?_)
  field_simp
  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
