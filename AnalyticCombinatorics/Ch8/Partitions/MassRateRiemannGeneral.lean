import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.MassRateLambert

noncomputable section

open Filter Finset Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

set_option maxHeartbeats 1000000

private lemma pairwise_disjoint_Ioc_mul_nat_succ {t : ℝ} (ht : 0 ≤ t) :
    Pairwise (Disjoint on fun k : ℕ =>
      Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : i + 1 ≤ j := by omega
    have hreal : (((i + 1 : ℕ) : ℝ) ≤ (j : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((i + 1 : ℕ) : ℝ) ≤ t * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxi.2.trans hle) hxj.1
  · refine Set.disjoint_left.mpr ?_
    intro x hxi hxj
    have hnat : j + 1 ≤ i := by omega
    have hreal : (((j + 1 : ℕ) : ℝ) ≤ (i : ℝ)) := by
      exact_mod_cast hnat
    have hle : t * ((j + 1 : ℕ) : ℝ) ≤ t * (i : ℝ) :=
      mul_le_mul_of_nonneg_left hreal ht
    exact not_lt_of_ge (hxj.2.trans hle) hxi.1

private lemma iUnion_Ioc_mul_nat_succ_eq_Ioi {t : ℝ} (ht : 0 < t) :
    (⋃ k : ℕ, Set.Ioc (t * (k : ℝ)) (t * ((k + 1 : ℕ) : ℝ))) =
      Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    have hk_nonneg : 0 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.zero_le k)
    exact (mul_nonneg ht.le hk_nonneg).trans_lt hk.1
  · intro hx
    let y : ℝ := x / t
    have hy_pos : 0 < y := by
      dsimp [y]
      exact div_pos hx ht
    let n : ℕ := Nat.ceil y
    have hn_pos : 0 < n := by
      have : 0 < Nat.ceil y := (Nat.ceil_pos (a := y)).mpr hy_pos
      simpa [n] using this
    let k : ℕ := n - 1
    have hk_succ : k + 1 = n := by
      dsimp [k]
      omega
    have hlt_nat : k < Nat.ceil y := by
      dsimp [k, n]
      omega
    have hk_lt_y : ((k : ℕ) : ℝ) < y :=
      (Nat.lt_ceil (a := y) (n := k)).mp hlt_nat
    have hy_le_n : y ≤ (n : ℝ) := by
      have hnn : Nat.ceil y ≤ n := by
        simp [n]
      exact (Nat.ceil_le (a := y) (n := n)).mp hnn
    have hy_le_succ : y ≤ (((k + 1 : ℕ) : ℝ)) := by
      simpa [hk_succ] using hy_le_n
    have hmul : t * y = x := by
      dsimp [y]
      field_simp [ht.ne']
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [← hmul]
    constructor
    · exact mul_lt_mul_of_pos_left hk_lt_y ht
    · exact mul_le_mul_of_nonneg_left hy_le_succ ht.le

theorem riemann_sum_Ioi_sub_integral_bound
    {f f' : ℝ → ℝ} {M η : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hf'int : IntegrableOn f' (Set.Ioi 0))
    (hfint : IntegrableOn f (Set.Ioi 0))
    (hbdd : ∀ x : ℝ, 0 < x → x ≤ η → |f x| ≤ M) :
    ∀ t : ℝ, 0 < t → t < η →
      |(∑' k : ℕ, if k = 0 then 0 else f (t * (k : ℝ)))
        - (1 / t) * ∫ x in Set.Ioi 0, f x| ≤
          (∫ x in Set.Ioi 0, |f' x|) + M := by
  intro t ht htη
  classical

  let a : ℕ → ℝ := fun k : ℕ => t * (k : ℝ)
  let b : ℕ → ℝ := fun k : ℕ => t * ((k + 1 : ℕ) : ℝ)
  let cell : ℕ → Set ℝ := fun k : ℕ => Set.Ioc (a k) (b k)
  let A : ℕ → ℝ := fun k : ℕ => if k = 0 then 0 else f (a k)
  let B : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, f x
  let D : ℕ → ℝ := fun k : ℕ => ∫ x in cell k, |f' x|
  let G : ℕ → ℝ := fun k : ℕ => (if k = 0 then M * t else 0) + t * D k

  have hUnion : (⋃ k : ℕ, cell k) = Set.Ioi (0 : ℝ) := by
    simpa [cell, a, b] using iUnion_Ioc_mul_nat_succ_eq_Ioi (t := t) ht
  have hmeas : ∀ k : ℕ, MeasurableSet (cell k) := by
    intro k
    simp [cell, a, b]
  have hpair : Pairwise (Disjoint on cell) := by
    simpa [cell, a, b] using pairwise_disjoint_Ioc_mul_nat_succ (t := t) ht.le

  have hf'int_abs : IntegrableOn (fun x : ℝ => |f' x|) (Set.Ioi (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using hf'int.norm

  have hcells_f : HasSum B (∫ x in Set.Ioi (0 : ℝ), f x) := by
    have h_int_union : IntegrableOn f (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hfint
    simpa [B, hUnion] using
      (hasSum_integral_iUnion (μ := volume) (f := f) hmeas hpair h_int_union)

  have hcells_D : HasSum D (∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h_int_union :
        IntegrableOn (fun x : ℝ => |f' x|) (⋃ k : ℕ, cell k) := by
      simpa [hUnion] using hf'int_abs
    simpa [D, hUnion] using
      (hasSum_integral_iUnion
        (μ := volume) (f := fun x : ℝ => |f' x|) hmeas hpair h_int_union)

  have hD_nonneg : ∀ k : ℕ, 0 ≤ D k := by
    intro k
    dsimp [D]
    exact integral_nonneg (fun x : ℝ => abs_nonneg (f' x))

  have hab_ab : ∀ k : ℕ, a k ≤ b k := by
    intro k
    dsimp [a, b]
    have hnat : k ≤ k + 1 := Nat.le_succ k
    have hreal : ((k : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hreal ht.le

  have hpos_a : ∀ k : ℕ, k ≠ 0 → 0 < a k := by
    intro k hk
    dsimp [a]
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    exact mul_pos ht hkpos

  have hpoint :
      ∀ (k : ℕ), k ≠ 0 → ∀ x : ℝ, x ∈ cell k → |f x - f (a k)| ≤ D k := by
    intro k hk x hx
    have ha_pos : 0 < a k := hpos_a k hk
    have hax : a k ≤ x := le_of_lt hx.1
    have hxb : x ≤ b k := hx.2
    have hderiv' : ∀ y ∈ Set.uIcc (a k) x, HasDerivAt f (f' y) y := by
      intro y hy
      have hy' : y ∈ Set.Icc (a k) x := by
        simpa [Set.uIcc_of_le hax] using hy
      exact hderiv y (ha_pos.trans_le hy'.1)
    have hint : IntervalIntegrable f' volume (a k) x := by
      have hsub : Set.uIcc (a k) x ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) x := by
          simpa [Set.uIcc_of_le hax] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := f) (f' := f') (a := a k) (b := x) hderiv' hint
    have hnorm1 : |f x - f (a k)| ≤ ∫ u in a k..x, |f' u| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs
        (μ := volume) (f := f') hax
    have hint_ab : IntervalIntegrable f' volume (a k) (b k) := by
      have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
        intro y hy
        have hy' : y ∈ Set.Icc (a k) (b k) := by
          simpa [Set.uIcc_of_le (hab_ab k)] using hy
        exact ha_pos.trans_le hy'.1
      exact (hf'int.mono_set hsub).intervalIntegrable
    have hint_abs_ab :
        IntervalIntegrable (fun u : ℝ => |f' u|) volume (a k) (b k) :=
      hint_ab.abs
    have hmono :
        ∫ u in a k..x, |f' u| ≤ ∫ u in a k..b k, |f' u| := by
      exact intervalIntegral.integral_mono_interval
        (μ := volume) (f := fun u : ℝ => |f' u|)
        (a := a k) (b := x) (c := a k) (d := b k)
        le_rfl hax hxb
        (Eventually.of_forall (fun u : ℝ => abs_nonneg (f' u)))
        hint_abs_ab
    have hright_eq : ∫ u in a k..b k, |f' u| = D k := by
      rw [intervalIntegral.integral_of_le (hab_ab k)]
    exact hnorm1.trans (hmono.trans_eq hright_eq)

  have hhead_interval : |∫ x in (0 : ℝ)..t, f x| ≤ M * t := by
    have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖f x‖ ≤ M := by
      intro x hx
      have hx' : x ∈ Set.Ioc (0 : ℝ) t := by
        simpa [Set.uIoc_of_le ht.le] using hx
      simpa [Real.norm_eq_abs] using hbdd x hx'.1 (hx'.2.trans htη.le)
    have hnorm :
        ‖∫ x in (0 : ℝ)..t, f x‖ ≤ M * |t - (0 : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := t) (C := M) (f := f) hbound
    simpa [Real.norm_eq_abs, abs_of_pos ht] using hnorm

  have hcell_error : ∀ k : ℕ, |t * A k - B k| ≤ G k := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hB0_eq : B 0 = ∫ x in (0 : ℝ)..t, f x := by
        dsimp [B, cell, a, b]
        rw [intervalIntegral.integral_of_le ht.le]
        simp
      calc
        |t * A 0 - B 0| = |B 0| := by
          simp [A]
        _ = |∫ x in (0 : ℝ)..t, f x| := by
          rw [hB0_eq]
        _ ≤ M * t := hhead_interval
        _ ≤ M * t + t * D 0 := by
          exact le_add_of_nonneg_right (mul_nonneg ht.le (hD_nonneg 0))
        _ = G 0 := by
          simp [G]
    · have hB_eq : B k = ∫ x in a k..b k, f x := by
        dsimp [B, cell]
        rw [intervalIntegral.integral_of_le (hab_ab k)]
      have hconst : (∫ x in a k..b k, A k) = t * A k := by
        rw [intervalIntegral.integral_const]
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba]
        simp [smul_eq_mul]
      have hf_interval : IntervalIntegrable f volume (a k) (b k) := by
        have hsub : Set.uIcc (a k) (b k) ⊆ Set.Ioi (0 : ℝ) := by
          intro y hy
          have hy' : y ∈ Set.Icc (a k) (b k) := by
            simpa [Set.uIcc_of_le (hab_ab k)] using hy
          exact (hpos_a k hk).trans_le hy'.1
        exact (hfint.mono_set hsub).intervalIntegrable
      have hconst_int :
          IntervalIntegrable (fun _ : ℝ => A k) volume (a k) (b k) :=
        intervalIntegrable_const
      have hdiff :
          (∫ x in a k..b k, f x - A k) =
            (∫ x in a k..b k, f x) - (∫ x in a k..b k, A k) := by
        exact intervalIntegral.integral_sub hf_interval hconst_int
      have hbound_int : ∀ x ∈ Set.uIoc (a k) (b k), ‖f x - A k‖ ≤ D k := by
        intro x hx
        have hxcell : x ∈ cell k := by
          simpa [cell, Set.uIoc_of_le (hab_ab k)] using hx
        simpa [A, hk, Real.norm_eq_abs] using hpoint k hk x hxcell
      have hnorm_bound :
          ‖∫ x in a k..b k, f x - A k‖ ≤ D k * |b k - a k| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a k) (b := b k) (C := D k)
          (f := fun x : ℝ => f x - A k) hbound_int
      have hrepr :
          t * A k - B k = - (∫ x in a k..b k, f x - A k) := by
        rw [hB_eq, ← hconst, hdiff]
        ring
      have habs : |b k - a k| = t := by
        have hba : b k - a k = t := by
          dsimp [a, b]
          push_cast
          ring
        rw [hba, abs_of_pos ht]
      have hmain : |t * A k - B k| ≤ t * D k := by
        calc
          |t * A k - B k| = ‖∫ x in a k..b k, f x - A k‖ := by
            rw [hrepr, Real.norm_eq_abs, abs_neg]
          _ ≤ D k * |b k - a k| := hnorm_bound
          _ = t * D k := by
            rw [habs]
            ring
      calc
        |t * A k - B k| ≤ t * D k := hmain
        _ = G k := by
          simp [G, hk]

  have hsumm_B : Summable B := hcells_f.summable
  have hhas_tD :
      HasSum (fun k : ℕ => t * D k)
        (t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := HasSum.const_smul t hcells_D
    simpa [smul_eq_mul] using h
  have hsingle : HasSum (fun k : ℕ => if k = 0 then M * t else 0) (M * t) :=
    hasSum_ite_eq (0 : ℕ) (M * t)
  have hhas_G :
      HasSum G (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) := by
    have h := hsingle.add hhas_tD
    simpa [G, add_comm, add_left_comm, add_assoc] using h

  have hsumm_abs_error : Summable (fun k : ℕ => |t * A k - B k|) :=
    Summable.of_nonneg_of_le
      (fun k : ℕ => abs_nonneg (t * A k - B k))
      (fun k : ℕ => hcell_error k)
      hhas_G.summable
  have hsumm_error : Summable (fun k : ℕ => t * A k - B k) :=
    Summable.of_abs hsumm_abs_error

  have hsumm_tA : Summable (fun k : ℕ => t * A k) := by
    have h := hsumm_error.add hsumm_B
    refine h.congr ?_
    intro k
    ring

  have hsumm_A : Summable A := by
    have h := Summable.const_smul (1 / t) hsumm_tA
    refine h.congr ?_
    intro k
    change (1 / t) * (t * A k) = A k
    field_simp [ht.ne']

  have hhas_tA :
      HasSum (fun k : ℕ => t * A k) (t * (∑' k : ℕ, A k)) := by
    have h := HasSum.const_smul t hsumm_A.hasSum
    simpa [smul_eq_mul] using h

  have hhas_error :
      HasSum (fun k : ℕ => t * A k - B k)
        (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) :=
    hhas_tA.sub hcells_f

  have herror_eq :
      (∑' k : ℕ, (t * A k - B k)) =
        t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x :=
    HasSum.tsum_eq hhas_error

  have hsum_abs_has :
      HasSum (fun k : ℕ => |t * A k - B k|)
        (∑' k : ℕ, |t * A k - B k|) :=
    hsumm_abs_error.hasSum

  have habs_tsum :
      |∑' k : ℕ, (t * A k - B k)|
        ≤ ∑' k : ℕ, |t * A k - B k| := by
    have hupper :
        (∑' k : ℕ, (t * A k - B k))
          ≤ ∑' k : ℕ, |t * A k - B k| := by
      exact hasSum_le
        (fun k : ℕ => le_abs_self (t * A k - B k))
        hsumm_error.hasSum hsum_abs_has
    have hlower :
        -(∑' k : ℕ, |t * A k - B k|)
          ≤ ∑' k : ℕ, (t * A k - B k) := by
      have hneg :
          HasSum (fun k : ℕ => - |t * A k - B k|)
            (-(∑' k : ℕ, |t * A k - B k|)) :=
        hsum_abs_has.neg
      exact hasSum_le
        (fun k : ℕ => neg_abs_le (t * A k - B k))
        hneg hsumm_error.hasSum
    exact abs_le.mpr ⟨hlower, hupper⟩

  have habs_le_G :
      (∑' k : ℕ, |t * A k - B k|)
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    exact hasSum_le
      (fun k : ℕ => hcell_error k)
      hsum_abs_has hhas_G

  have hscaled :
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
        ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
    calc
      |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x|
          = |∑' k : ℕ, (t * A k - B k)| := by
            rw [← herror_eq]
      _ ≤ ∑' k : ℕ, |t * A k - B k| := habs_tsum
      _ ≤ M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x| := habs_le_G

  have htinv_pos : 0 < 1 / t := one_div_pos.mpr ht

  change
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x| ≤
      (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M

  calc
    |(∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x|
        = (1 / t) *
            |t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x| := by
          have hscale :
              (∑' k : ℕ, A k) - (1 / t) * ∫ x in Set.Ioi (0 : ℝ), f x =
                (1 / t) *
                  (t * (∑' k : ℕ, A k) - ∫ x in Set.Ioi (0 : ℝ), f x) := by
            field_simp [ht.ne']
          rw [hscale, abs_mul, abs_of_pos htinv_pos]
    _ ≤ (1 / t) *
          (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|) :=
          mul_le_mul_of_nonneg_left hscaled htinv_pos.le
    _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
          calc
            (1 / t) * (M * t + t * ∫ x in Set.Ioi (0 : ℝ), |f' x|)
                = (1 / t) *
                    (t * (M + ∫ x in Set.Ioi (0 : ℝ), |f' x|)) := by
                  ring
            _ = M + ∫ x in Set.Ioi (0 : ℝ), |f' x| := by
                  field_simp [ht.ne']
            _ = (∫ x in Set.Ioi (0 : ℝ), |f' x|) + M := by
                  ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
