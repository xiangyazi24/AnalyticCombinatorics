import Mathlib

/-!
# TASK T2-ceiling, L1: the mixture-overlap bridge

The ceiling-level regeneration route (ChatGPT R7) needs to convert
*pairwise* kernel overlap between level states into *mixture* overlap between the two
full entrance laws.  Concretely: if start `n` reaches the ceiling level with a sub-probability
weight `a : ℕ → ℝ` of total mass `≥ α`, start `n'` with weight `b` of total mass `≥ α`, the
continuation kernels `K x` are nonnegative, and any two level states `x, y` have continuation
overlap `≥ β` on the in-band `slice`, then the two mixtures
`A z = ∑_x a x · K x z` and `B z = ∑_y b y · K y z` overlap by `≥ α·β` on the slice.

**Proof (mixture convexity).**  Let `Sa = ∑_L a`, `Sb = ∑_L b` (both `≥ α ≥ 0`).  For each slice
state `z` define the doubly-weighted common mass
`W z = ∑_{x,y ∈ L} a x · b y · min (K x z) (K y z) ≥ 0`.  Then

* `W z ≤ ∑_{x,y} a x · b y · K x z = Sb · A z`, hence `W z / Sb ≤ A z`;
* `W z ≤ ∑_{x,y} a x · b y · K y z = Sa · B z`, hence `W z / Sa ≤ B z`;

so `min (A z) (B z) ≥ W z / max Sa Sb`.  Summing and using
`∑_z W z = ∑_{x,y} a x · b y · (∑_z min (K x z) (K y z)) ≥ β · Sa · Sb` gives
`∑_z min (A z) (B z) ≥ β · Sa · Sb / max Sa Sb = β · min Sa Sb ≥ α · β`.

NEW file; pure Finset algebra (imports only Mathlib).  Opus-authored.
-/

noncomputable section

open scoped BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **L1 — mixture-overlap bridge.**  See the file header for the statement and proof.  The
hypothesis `0 ≤ α` is necessary: with `α < 0` and a negative spurious overlap floor `β` the claim
`α·β ≤ ∑ min` is false (e.g. all data `0`, `α = β = -1`).  At the engine call site `α > 0`. -/
lemma overlap_of_mixtures_of_pairwise_overlap
    {L slice : Finset ℕ} {a b : ℕ → ℝ} {K : ℕ → ℕ → ℝ} {α β : ℝ}
    (hα : 0 ≤ α) (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ y, 0 ≤ b y)
    (ha : α ≤ ∑ x ∈ L, a x) (hb : α ≤ ∑ y ∈ L, b y)
    (hK0 : ∀ x z, 0 ≤ K x z)
    (hpair : ∀ x ∈ L, ∀ y ∈ L, β ≤ ∑ z ∈ slice, min (K x z) (K y z)) :
    α * β ≤ ∑ z ∈ slice, min (∑ x ∈ L, a x * K x z) (∑ y ∈ L, b y * K y z) := by
  classical
  set Sa : ℝ := ∑ x ∈ L, a x with hSa
  set Sb : ℝ := ∑ y ∈ L, b y with hSb
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg (fun x _ => ha0 x)
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun y _ => hb0 y)
  set A : ℕ → ℝ := fun z => ∑ x ∈ L, a x * K x z with hAdef
  set B : ℕ → ℝ := fun z => ∑ y ∈ L, b y * K y z with hBdef
  set W : ℕ → ℝ := fun z => ∑ x ∈ L, ∑ y ∈ L, a x * b y * min (K x z) (K y z) with hWdef
  have hW0 : ∀ z, 0 ≤ W z := by
    intro z
    refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_))
    exact mul_nonneg (mul_nonneg (ha0 x) (hb0 y)) (le_min (hK0 x z) (hK0 y z))
  -- W z ≤ Sb · A z
  have hWA : ∀ z, W z ≤ Sb * A z := by
    intro z
    have hstep : W z ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z := by
      refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg (ha0 x) (hb0 y))
    have hcollapse : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z) = Sb * A z := by
      have hper : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K x z) = ∑ x ∈ L, (a x * K x z) * Sb := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hSb, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => by ring)
      rw [hper, ← Finset.sum_mul, hAdef]; ring
    rw [← hcollapse]; exact hstep
  -- W z ≤ Sa · B z
  have hWB : ∀ z, W z ≤ Sa * B z := by
    intro z
    have hstep : W z ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * K y z := by
      refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (ha0 x) (hb0 y))
    have hcollapse : (∑ x ∈ L, ∑ y ∈ L, a x * b y * K y z) = Sa * B z := by
      rw [Finset.sum_comm]
      have : (∑ y ∈ L, ∑ x ∈ L, a x * b y * K y z) = ∑ y ∈ L, Sa * (b y * K y z) := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hSa, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => by ring)
      rw [this, ← Finset.mul_sum, hBdef]
    rw [← hcollapse]; exact hstep
  -- ∑_z W z ≥ β · Sa · Sb
  have hWsum : β * Sa * Sb ≤ ∑ z ∈ slice, W z := by
    have hWsum_eq : (∑ z ∈ slice, W z)
        = ∑ x ∈ L, ∑ y ∈ L, a x * b y * (∑ z ∈ slice, min (K x z) (K y z)) := by
      rw [hWdef]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum]
    rw [hWsum_eq]
    -- lower-bound each pairwise overlap by β, then collapse ∑ a · ∑ b
    have hlb : ∑ x ∈ L, ∑ y ∈ L, a x * b y * β
        ≤ ∑ x ∈ L, ∑ y ∈ L, a x * b y * (∑ z ∈ slice, min (K x z) (K y z)) := by
      refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => ?_))
      exact mul_le_mul_of_nonneg_left (hpair x hx y hy) (mul_nonneg (ha0 x) (hb0 y))
    refine le_trans ?_ hlb
    -- ∑_x ∑_y a x b y β = β Sa Sb
    have hconst : (∑ x ∈ L, ∑ y ∈ L, a x * b y * β) = β * Sa * Sb := by
      have e1 : (∑ x ∈ L, ∑ y ∈ L, a x * b y * β)
          = ∑ x ∈ L, (a x * (∑ y ∈ L, b y) * β) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [e1, ← Finset.sum_mul, ← Finset.sum_mul, hSa, hSb]; ring
    rw [hconst]
  -- A, B nonneg pointwise
  have hAz : ∀ z, 0 ≤ A z := fun z => Finset.sum_nonneg (fun x _ => mul_nonneg (ha0 x) (hK0 x z))
  have hBz : ∀ z, 0 ≤ B z := fun z => Finset.sum_nonneg (fun y _ => mul_nonneg (hb0 y) (hK0 y z))
  have hsum_nonneg : 0 ≤ ∑ z ∈ slice, min (A z) (B z) :=
    Finset.sum_nonneg (fun z _ => le_min (hAz z) (hBz z))
  -- split on the sign of β: β ≤ 0 makes the claim trivial.
  rcases le_or_gt β 0 with hβ | hβpos
  · -- α ≥ 0, β ≤ 0 ⟹ α·β ≤ 0 ≤ ∑ min
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hα hβ) hsum_nonneg
  · -- β > 0.  Now Sa, Sb > 0 (else β·Sa·Sb ≤ 0 < ... contradicts hWsum giving W≥0 fine, but we
    -- need the division; handle Sa or Sb = 0 by trivial bound too).
    rcases eq_or_lt_of_le hSa0 with hSaz | hSapos
    · -- Sa = 0 ⟹ α ≤ 0, with hα gives α = 0
      have hαz : α = 0 := le_antisymm (le_trans ha (le_of_eq hSaz.symm)) hα
      rw [hαz, zero_mul]; exact hsum_nonneg
    rcases eq_or_lt_of_le hSb0 with hSbz | hSbpos
    · have hαz : α = 0 := le_antisymm (le_trans hb (le_of_eq hSbz.symm)) hα
      rw [hαz, zero_mul]; exact hsum_nonneg
    set D : ℝ := max Sa Sb with hDdef
    have hDpos : 0 < D := lt_of_lt_of_le hSapos (le_max_left _ _)
    -- min (A z) (B z) ≥ W z / D
    have hkey : ∀ z, W z / D ≤ min (A z) (B z) := by
      intro z
      refine le_min ?_ ?_
      · rw [div_le_iff₀ hDpos]
        refine le_trans (hWA z) ?_
        calc Sb * A z ≤ D * A z := mul_le_mul_of_nonneg_right (le_max_right Sa Sb) (hAz z)
          _ = A z * D := by ring
      · rw [div_le_iff₀ hDpos]
        refine le_trans (hWB z) ?_
        calc Sa * B z ≤ D * B z := mul_le_mul_of_nonneg_right (le_max_left Sa Sb) (hBz z)
          _ = B z * D := by ring
    have hsumlb : (∑ z ∈ slice, W z) / D ≤ ∑ z ∈ slice, min (A z) (B z) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun z _ => hkey z)
    refine le_trans ?_ hsumlb
    rw [le_div_iff₀ hDpos]
    refine le_trans ?_ hWsum
    -- goal: α * β * D ≤ β * Sa * Sb.  Use Sa*Sb = D * min Sa Sb and α ≤ min Sa Sb, β > 0.
    have hSaSb : Sa * Sb = D * min Sa Sb := by
      rcases le_total Sa Sb with h | h
      · rw [hDdef, max_eq_right h, min_eq_left h]; ring
      · rw [hDdef, max_eq_left h, min_eq_right h]
    have hminαβ : α ≤ min Sa Sb := le_min ha hb
    have hβD : 0 ≤ β * D := mul_nonneg hβpos.le hDpos.le
    calc α * β * D = (β * D) * α := by ring
      _ ≤ (β * D) * min Sa Sb := mul_le_mul_of_nonneg_left hminαβ hβD
      _ = β * Sa * Sb := by rw [show β * Sa * Sb = β * (Sa * Sb) by ring, hSaSb]; ring

#print axioms overlap_of_mixtures_of_pairwise_overlap

end AnalyticCombinatorics.Ch8.Partitions.Erdos
