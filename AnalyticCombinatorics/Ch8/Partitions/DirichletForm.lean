import AnalyticCombinatorics.Ch8.Partitions.GreenComparison

/-!
# Bounded-jump Dirichlet-form comparison (renewal route B, Layer-2 Stage 3c)

The kernel-side upper bound of the finite-interval Green/Harnack comparison (ChatGPT ac2 R11): for a
nonnegative bounded-jump kernel `Kc` on the integer interval `[-L,L]` with row mass `≤ 1`, the energy
form is dominated by the nearest-neighbor edge energy,

  `∑_{d,e} Kc(d,e)·(f e − f d)² ≤ B(2B+1)·∑_r (f(r+1) − f r)²   (≤ 3B²·… for B ≥ 1)`.

One factor `B` is the path Cauchy–Schwarz (the banked `sq_diff_le_path_energy_nat`); the `2B+1` is the
edge-charging count (`crossing_charge_le`: only starts within `B` of an edge can cross it, each with
row mass `≤ 1`).  No symmetry needed.  This is the `E_K ≤ Λ·E_edge` half of the form sandwich feeding
`GreenForm.green_domination_of_form_le`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Vertex interval `[-L,L] ⊂ ℤ`. -/
def intVerts (L : ℕ) : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ)

/-- Edge interval `[-L,L) ⊂ ℤ`; edge `r` means `(r,r+1)`. -/
def intEdges (L : ℕ) : Finset ℤ := Finset.Ico (-(L : ℤ)) (L : ℤ)

/-- Nearest-neighbor edge energy. -/
def edgeSq (f : ℤ → ℝ) (r : ℤ) : ℝ := (f (r + 1) - f r) ^ 2

/-- Edge `r` lies on the monotone integer path between `d` and `e`. -/
def crossesEdge (d e r : ℤ) : Prop := (d ≤ r ∧ r < e) ∨ (e ≤ r ∧ r < d)

instance (d e r : ℤ) : Decidable (crossesEdge d e r) := by unfold crossesEdge; infer_instance

lemma edgeSq_nonneg (f : ℤ → ℝ) (r : ℤ) : 0 ≤ edgeSq f r := by
  unfold edgeSq; exact sq_nonneg _

/-- If an edge `r` is crossed by a jump `d → e`, the start `d` is within the jump length of `r`. -/
lemma abs_start_le_jump_of_crosses {d e r : ℤ} (hcross : crossesEdge d e r) :
    |r - d| ≤ |e - d| := by
  rcases hcross with h | h
  · rcases h with ⟨hdr, hre⟩
    have hrd_nonneg : 0 ≤ r - d := by omega
    have hed_nonneg : 0 ≤ e - d := by omega
    rw [abs_of_nonneg hrd_nonneg, abs_of_nonneg hed_nonneg]; omega
  · rcases h with ⟨her, hrd⟩
    have hrd_nonpos : r - d ≤ 0 := by omega
    have hed_nonpos : e - d ≤ 0 := by omega
    rw [abs_of_nonpos hrd_nonpos, abs_of_nonpos hed_nonpos]; omega

/-- If `d,e ∈ [-L,L]`, every crossed edge is in `[-L,L)`. -/
lemma crossed_edge_mem_edges {L : ℕ} {d e r : ℤ}
    (hd : d ∈ intVerts L) (he : e ∈ intVerts L) (hcross : crossesEdge d e r) :
    r ∈ intEdges L := by
  simp only [intVerts, intEdges, Finset.mem_Icc, Finset.mem_Ico] at hd he ⊢
  rcases hcross with h | h
  · rcases h with ⟨hdr, hre⟩; exact ⟨le_trans hd.1 hdr, lt_of_lt_of_le hre he.2⟩
  · rcases h with ⟨her, hrd⟩; exact ⟨le_trans he.1 her, lt_of_lt_of_le hrd hd.2⟩

/-- Path-energy bound written using crossed edges (the banked path lemma in two orientations). -/
lemma sq_diff_le_crossed_edge_energy
    (f : ℤ → ℝ) {L : ℕ} {d e : ℤ}
    (hd : d ∈ intVerts L) (he : e ∈ intVerts L) :
    (f e - f d) ^ 2
      ≤ (|e - d| : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
  classical
  by_cases hde : d ≤ e
  · let n : ℕ := Int.toNat (e - d)
    have hnonneg : 0 ≤ e - d := by omega
    have hn_cast : (n : ℤ) = e - d := by dsimp [n]; exact Int.toNat_of_nonneg hnonneg
    have heq : e = d + n := by norm_num [hn_cast]
    have hpath := sq_diff_le_path_energy_nat f d n
    have hsum_le :
        (∑ k ∈ Finset.range n, edgeSq f (d + k))
          ≤ ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
      rw [← Finset.sum_image]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rcases Finset.mem_image.mp hr with ⟨k, hk, rfl⟩
          rw [Finset.mem_filter]
          have hklt : k < n := Finset.mem_range.mp hk
          have hcross : crossesEdge d e (d + k) := by
            unfold crossesEdge; left; constructor
            · omega
            · rw [heq]; omega
          exact ⟨crossed_edge_mem_edges hd he hcross, hcross⟩
        · intro r _ _; exact edgeSq_nonneg f r
      · intro a _ b _ h; simp only [add_right_inj, Nat.cast_inj] at h; exact h
    calc (f e - f d) ^ 2 = (f (d + n) - f d) ^ 2 := by rw [heq]
      _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, edgeSq f (d + k) := by simpa [edgeSq] using hpath
      _ ≤ (n : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (|e - d| : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
        have hne : (|e - d| : ℝ) = (n : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast hnonneg : (0:ℝ) ≤ (e:ℝ) - (d:ℝ))]
          exact_mod_cast hn_cast.symm
        rw [hne]
  · have hed : e ≤ d := by omega
    let n : ℕ := Int.toNat (d - e)
    have hnonneg : 0 ≤ d - e := by omega
    have hn_cast : (n : ℤ) = d - e := by dsimp [n]; exact Int.toNat_of_nonneg hnonneg
    have hdeq : d = e + n := by norm_num [hn_cast]
    have hpath := sq_diff_le_path_energy_nat f e n
    have hsum_le :
        (∑ k ∈ Finset.range n, edgeSq f (e + k))
          ≤ ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
      rw [← Finset.sum_image]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rcases Finset.mem_image.mp hr with ⟨k, hk, rfl⟩
          rw [Finset.mem_filter]
          have hklt : k < n := Finset.mem_range.mp hk
          have hcross : crossesEdge d e (e + k) := by
            unfold crossesEdge; right; constructor
            · omega
            · rw [hdeq]; omega
          exact ⟨crossed_edge_mem_edges hd he hcross, hcross⟩
        · intro r _ _; exact edgeSq_nonneg f r
      · intro a _ b _ h; simp only [add_right_inj, Nat.cast_inj] at h; exact h
    calc (f e - f d) ^ 2 = (f d - f e) ^ 2 := by ring
      _ = (f (e + n) - f e) ^ 2 := by rw [hdeq]
      _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, edgeSq f (e + k) := by simpa [edgeSq] using hpath
      _ ≤ (n : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (|e - d| : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
        have hne : (|e - d| : ℝ) = (n : ℝ) := by
          rw [abs_of_nonpos (by exact_mod_cast (by omega : e - d ≤ 0) : (e:ℝ) - (d:ℝ) ≤ 0)]
          have h2 : (n : ℝ) = (d : ℝ) - (e : ℝ) := by exact_mod_cast hn_cast
          linarith [h2]
        rw [hne]

/-- Cardinality of an integer interval centered at `r`. -/
lemma card_int_Icc_center (r : ℤ) (B : ℕ) :
    (Finset.Icc (r - (B : ℤ)) (r + (B : ℤ))).card = 2 * B + 1 := by
  rw [Int.card_Icc]; omega

/-- Starts `d ∈ [-L,L]` within distance `B` of edge `r` are at most `2B+1`. -/
lemma card_near_starts_le (L B : ℕ) (r : ℤ) :
    ((intVerts L).filter (fun d => |r - d| ≤ (B : ℤ))).card ≤ 2 * B + 1 := by
  classical
  have hsub :
      (intVerts L).filter (fun d => |r - d| ≤ (B : ℤ))
        ⊆ Finset.Icc (r - (B : ℤ)) (r + (B : ℤ)) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    have h : |r - d| ≤ (B : ℤ) := hd.2
    rw [abs_le] at h
    constructor <;> omega
  calc ((intVerts L).filter (fun d => |r - d| ≤ (B : ℤ))).card
        ≤ (Finset.Icc (r - (B : ℤ)) (r + (B : ℤ))).card := Finset.card_le_card hsub
    _ = 2 * B + 1 := card_int_Icc_center r B

/-- Edge-charge bound: for fixed edge `r`, the total kernel weight of jumps crossing `r` is `≤ 2B+1`. -/
lemma crossing_charge_le
    (Kc : ℤ → ℤ → ℝ) (L B : ℕ) (r : ℤ)
    (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hrow : ∀ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e ≤ 1)
    (hjump : ∀ d ∈ intVerts L, ∀ e ∈ intVerts L, Kc d e ≠ 0 → |e - d| ≤ (B : ℤ)) :
    (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0))
      ≤ (2 * B + 1 : ℝ) := by
  classical
  let Near : Finset ℤ := (intVerts L).filter (fun d => |r - d| ≤ (B : ℤ))
  have hzero_far :
      ∀ d ∈ intVerts L, d ∉ Near →
        (∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0)) = 0 := by
    intro d hd hdNear
    refine Finset.sum_eq_zero ?_
    intro e he
    by_cases hcross : crossesEdge d e r
    · rw [if_pos hcross, mul_one]
      by_cases hK : Kc d e = 0
      · exact hK
      · have hj := hjump d hd e he hK
        have hnear : |r - d| ≤ (B : ℤ) := le_trans (abs_start_le_jump_of_crosses hcross) hj
        exact False.elim (hdNear (by rw [Finset.mem_filter]; exact ⟨hd, hnear⟩))
    · rw [if_neg hcross, mul_zero]
  have hrestrict :
      (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0))
        = ∑ d ∈ Near, ∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0) := by
    symm
    apply Finset.sum_subset
    · intro d hd; rw [Finset.mem_filter] at hd; exact hd.1
    · intro d hdI hdNotNear; exact hzero_far d hdI hdNotNear
  have hinner :
      ∀ d ∈ Near,
        (∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0)) ≤ 1 := by
    intro d hdNear
    rw [Finset.mem_filter] at hdNear
    calc (∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0))
          ≤ ∑ e ∈ intVerts L, Kc d e := by
          refine Finset.sum_le_sum ?_
          intro e he
          by_cases hcross : crossesEdge d e r
          · rw [if_pos hcross, mul_one]
          · rw [if_neg hcross, mul_zero]; exact hKnn d e
      _ ≤ 1 := hrow d hdNear.1
  calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0))
        = ∑ d ∈ Near, ∑ e ∈ intVerts L, Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0) :=
        hrestrict
    _ ≤ ∑ _d ∈ Near, (1 : ℝ) := Finset.sum_le_sum hinner
    _ = (Near.card : ℝ) := by simp
    _ ≤ (2 * B + 1 : ℝ) := by exact_mod_cast card_near_starts_le L B r

/-- Pairwise bounded-jump path bound in the form used under the kernel sum. -/
lemma weighted_pair_energy_le
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L B : ℕ) {d e : ℤ}
    (hd : d ∈ intVerts L) (he : e ∈ intVerts L)
    (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hjump : ∀ d ∈ intVerts L, ∀ e ∈ intVerts L, Kc d e ≠ 0 → |e - d| ≤ (B : ℤ)) :
    Kc d e * (f e - f d) ^ 2
      ≤ Kc d e *
          ((B : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r) := by
  by_cases hK : Kc d e = 0
  · rw [hK]; simp
  · have hj : |e - d| ≤ (B : ℤ) := hjump d hd e he hK
    have hpath := sq_diff_le_crossed_edge_energy f hd he
    have hB :
        (|e - d| : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r
          ≤ (B : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hj
      · exact Finset.sum_nonneg (fun r _ => edgeSq_nonneg f r)
    exact mul_le_mul_of_nonneg_left (le_trans hpath hB) (hKnn d e)

/-- **Bounded-jump Dirichlet-form comparison.**  Constant `B(2B+1)`; no symmetry needed. -/
theorem bounded_jump_energy_le_edge_energy
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L B : ℕ)
    (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hrow : ∀ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e ≤ 1)
    (hjump : ∀ d ∈ intVerts L, ∀ e ∈ intVerts L, Kc d e ≠ 0 → |e - d| ≤ (B : ℤ)) :
    (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2)
      ≤ (B : ℝ) * (2 * B + 1 : ℝ) * ∑ r ∈ intEdges L, edgeSq f r := by
  classical
  have hpair :
      ∀ d ∈ intVerts L, ∀ e ∈ intVerts L,
        Kc d e * (f e - f d) ^ 2
          ≤ Kc d e *
              ((B : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r) := by
    intro d hd e he
    exact weighted_pair_energy_le Kc f L B hd he hKnn hjump
  calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2)
        ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * ((B : ℝ) * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r) := by
        refine Finset.sum_le_sum ?_
        intro d hd
        refine Finset.sum_le_sum ?_
        intro e he
        exact hpair d hd e he
    _ = (B : ℝ) * ∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * ∑ r ∈ (intEdges L).filter (fun r => crossesEdge d e r), edgeSq f r := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro d _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro e _
        ring
    _ = (B : ℝ) * ∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * ∑ r ∈ intEdges L, (if crossesEdge d e r then edgeSq f r else 0) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro d _
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [Finset.sum_filter]
    _ = (B : ℝ) * ∑ r ∈ intEdges L,
            edgeSq f r *
              (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
                Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0)) := by
        congr 1
        calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
              Kc d e * ∑ r ∈ intEdges L, (if crossesEdge d e r then edgeSq f r else 0))
              = ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, ∑ r ∈ intEdges L,
                Kc d e * (if crossesEdge d e r then edgeSq f r else 0) := by
              refine Finset.sum_congr rfl ?_
              intro d _
              refine Finset.sum_congr rfl ?_
              intro e _
              rw [Finset.mul_sum]
          _ = ∑ r ∈ intEdges L, ∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
                Kc d e * (if crossesEdge d e r then edgeSq f r else 0) := by
              rw [Finset.sum_congr rfl (fun d _ => Finset.sum_comm), Finset.sum_comm]
          _ = ∑ r ∈ intEdges L,
                edgeSq f r *
                  (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
                    Kc d e * (if crossesEdge d e r then (1 : ℝ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro d _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro e _
              by_cases h : crossesEdge d e r
              · rw [if_pos h, if_pos h]; ring
              · rw [if_neg h, if_neg h]; ring
    _ ≤ (B : ℝ) * ∑ r ∈ intEdges L, edgeSq f r * (2 * B + 1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · refine Finset.sum_le_sum ?_
          intro r hr
          exact mul_le_mul_of_nonneg_left
            (crossing_charge_le Kc L B r hKnn hrow hjump) (edgeSq_nonneg f r)
        · positivity
    _ = (B : ℝ) * (2 * B + 1 : ℝ) * ∑ r ∈ intEdges L, edgeSq f r := by
        rw [← Finset.sum_mul]; ring

/-- For `B ≥ 1`, `B(2B+1) ≤ 3B²`. -/
theorem bounded_jump_energy_le_edge_energy_three_B_sq
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L B : ℕ) (hB : 1 ≤ B)
    (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hrow : ∀ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e ≤ 1)
    (hjump : ∀ d ∈ intVerts L, ∀ e ∈ intVerts L, Kc d e ≠ 0 → |e - d| ≤ (B : ℤ)) :
    (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2)
      ≤ 3 * (B : ℝ) ^ 2 * ∑ r ∈ intEdges L, edgeSq f r := by
  have hmain := bounded_jump_energy_le_edge_energy Kc f L B hKnn hrow hjump
  have hcoeff : (B : ℝ) * (2 * B + 1 : ℝ) ≤ 3 * (B : ℝ) ^ 2 := by
    have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    nlinarith
  have henergy_nonneg : 0 ≤ ∑ r ∈ intEdges L, edgeSq f r :=
    Finset.sum_nonneg (fun r _ => edgeSq_nonneg f r)
  calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2)
        ≤ (B : ℝ) * (2 * B + 1 : ℝ) * ∑ r ∈ intEdges L, edgeSq f r := hmain
    _ ≤ 3 * (B : ℝ) ^ 2 * ∑ r ∈ intEdges L, edgeSq f r :=
      mul_le_mul_of_nonneg_right hcoeff henergy_nonneg

end AnalyticCombinatorics.Ch8.Partitions.Erdos
