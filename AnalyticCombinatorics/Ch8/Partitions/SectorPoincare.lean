import AnalyticCombinatorics.Ch8.Partitions.GreenComparison

/-!
# Discrete Poincaré on an integer interval (renewal route B, Layer-2 sector Hardy support)

The discrete Poincaré chain (ChatGPT ac2 R14), built on the banked `sq_diff_le_path_energy_nat`:

* `point_sq_le_path_energy` — pointwise from a zero basepoint: `f x² ≤ (x−a)·∑edge²`;
* `interval_l2_le_L2_edgeEnergy` — interval `L²` bound: `∑_{[a,b]} f² ≤ M²·∑edge²`, `M = (b−a+2)`.

These feed the sector/Hardy estimate `Hcut_l2_le` (`∑ Hcut² ≤ C·B·Γ²·L²·E_edge`) which converts a
crossing-variation bound into the antisymmetric-form sector bound.  Pure finite-sum + Cauchy–Schwarz.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Pointwise discrete Poincaré from a zero basepoint (`f a = 0`). -/
lemma point_sq_le_path_energy {a x : ℤ} (hax : a ≤ x) (f : ℤ → ℝ) (hbase : f a = 0) :
    f x ^ 2 ≤ (((x - a).toNat : ℝ)) * ∑ e ∈ Finset.Icc a (x - 1), (f (e + 1) - f e) ^ 2 := by
  classical
  let n : ℕ := (x - a).toNat
  have hnonneg : 0 ≤ x - a := by omega
  have hnZ : (n : ℤ) = x - a := by dsimp [n]; exact Int.toNat_of_nonneg hnonneg
  have haxn : a + (n : ℤ) = x := by omega
  have hleft : f x ^ 2 = (f (a + (n : ℤ)) - f a) ^ 2 := by rw [← haxn, hbase]; ring
  have hpath := sq_diff_le_path_energy_nat f a n
  have himage :
      (∑ e ∈ (Finset.range n).image (fun k : ℕ => a + (k : ℤ)), (f (e + 1) - f e) ^ 2)
        = ∑ k ∈ Finset.range n, (f (a + (k : ℤ) + 1) - f (a + (k : ℤ))) ^ 2 := by
    rw [Finset.sum_image]
    intro u hu v hv huv
    simp only [add_right_inj, Nat.cast_inj] at huv
    exact huv
  have hsub :
      (Finset.range n).image (fun k : ℕ => a + (k : ℤ)) ⊆ Finset.Icc a (x - 1) := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨k, hk, rfl⟩
    rw [Finset.mem_Icc]
    have hklt : k < n := Finset.mem_range.mp hk
    have hkltZ : (k : ℤ) < (n : ℤ) := by exact_mod_cast hklt
    constructor
    · omega
    · omega
  have hsum_le :
      (∑ k ∈ Finset.range n, (f (a + (k : ℤ) + 1) - f (a + (k : ℤ))) ^ 2)
        ≤ ∑ e ∈ Finset.Icc a (x - 1), (f (e + 1) - f e) ^ 2 := by
    rw [← himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => sq_nonneg (f (e + 1) - f e))
  calc f x ^ 2 = (f (a + (n : ℤ)) - f a) ^ 2 := hleft
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, (f (a + (k : ℤ) + 1) - f (a + (k : ℤ))) ^ 2 := by
        simpa using hpath
    _ ≤ (n : ℝ) * ∑ e ∈ Finset.Icc a (x - 1), (f (e + 1) - f e) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (((x - a).toNat : ℝ)) * ∑ e ∈ Finset.Icc a (x - 1), (f (e + 1) - f e) ^ 2 := rfl

/-- Interval `L²` Poincaré bound from a zero value at the left ghost point `a−1`, with coarse constant
`M = (b − a + 2)`. -/
lemma interval_l2_le_L2_edgeEnergy {a b : ℤ} (hab : a ≤ b) (f : ℤ → ℝ) (hbase : f (a - 1) = 0) :
    (∑ x ∈ Finset.Icc a b, f x ^ 2)
      ≤ (((b - a + 2 : ℤ).toNat : ℝ)) ^ 2
          * ∑ e ∈ Finset.Icc (a - 1) (b - 1), (f (e + 1) - f e) ^ 2 := by
  classical
  let M : ℕ := (b - a + 2).toNat
  let E : ℝ := ∑ e ∈ Finset.Icc (a - 1) (b - 1), (f (e + 1) - f e) ^ 2
  have hMnonnegZ : 0 ≤ b - a + 2 := by omega
  have hMZ : (M : ℤ) = b - a + 2 := by dsimp [M]; exact Int.toNat_of_nonneg hMnonnegZ
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]; exact Finset.sum_nonneg (fun e _ => sq_nonneg (f (e + 1) - f e))
  have hpoint_bound : ∀ x ∈ Finset.Icc a b, f x ^ 2 ≤ (M : ℝ) * E := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hbase_le : a - 1 ≤ x := by omega
    have hpt := point_sq_le_path_energy (a := a - 1) (x := x) hbase_le f hbase
    have hsub : Finset.Icc (a - 1) (x - 1) ⊆ Finset.Icc (a - 1) (b - 1) := by
      intro e he
      rw [Finset.mem_Icc] at he ⊢
      exact ⟨he.1, by omega⟩
    have hsmall_le_E :
        (∑ e ∈ Finset.Icc (a - 1) (x - 1), (f (e + 1) - f e) ^ 2) ≤ E := by
      dsimp [E]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => sq_nonneg (f (e + 1) - f e))
    have hlen_nonnegZ : 0 ≤ x - (a - 1) := by omega
    have hlenZ : (((x - (a - 1)).toNat : ℕ) : ℤ) = x - (a - 1) := Int.toNat_of_nonneg hlen_nonnegZ
    have hlen_le_Z : (((x - (a - 1)).toNat : ℕ) : ℤ) ≤ (M : ℤ) := by rw [hlenZ, hMZ]; omega
    have hlen_le : (((x - (a - 1)).toNat : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hlen_le_Z
    calc f x ^ 2
          ≤ (((x - (a - 1)).toNat : ℝ))
              * ∑ e ∈ Finset.Icc (a - 1) (x - 1), (f (e + 1) - f e) ^ 2 := hpt
      _ ≤ (((x - (a - 1)).toNat : ℝ)) * E := mul_le_mul_of_nonneg_left hsmall_le_E (by positivity)
      _ ≤ (M : ℝ) * E := mul_le_mul_of_nonneg_right hlen_le hE_nonneg
  have hsum_points :
      (∑ x ∈ Finset.Icc a b, f x ^ 2) ≤ ∑ _x ∈ Finset.Icc a b, (M : ℝ) * E :=
    Finset.sum_le_sum hpoint_bound
  have hcard_le : (Finset.Icc a b).card ≤ M := by dsimp [M]; rw [Int.card_Icc]; omega
  have hcard_le_R : ((Finset.Icc a b).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcard_le
  have hME_nonneg : 0 ≤ (M : ℝ) * E := mul_nonneg (by positivity) hE_nonneg
  calc (∑ x ∈ Finset.Icc a b, f x ^ 2)
        ≤ ∑ _x ∈ Finset.Icc a b, (M : ℝ) * E := hsum_points
    _ = ((Finset.Icc a b).card : ℝ) * ((M : ℝ) * E) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * ((M : ℝ) * E) := mul_le_mul_of_nonneg_right hcard_le_R hME_nonneg
    _ = (M : ℝ) ^ 2 * E := by ring
    _ = (((b - a + 2 : ℤ).toNat : ℝ)) ^ 2
          * ∑ e ∈ Finset.Icc (a - 1) (b - 1), (f (e + 1) - f e) ^ 2 := rfl

end AnalyticCombinatorics.Ch8.Partitions.Erdos
