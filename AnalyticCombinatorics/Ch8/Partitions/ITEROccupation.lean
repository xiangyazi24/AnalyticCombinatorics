import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# R7 Fact B via Doeblin: the window-occupation form of the ITER bound

The fixed-window single-epoch ITER bound `1 − (1−δ)^m − δ·∑(1−δ)^{m−t−1}b_t` is **insufficient** for the
Erdős constant `C = π/√6`: a one-pass coupling with a fixed window cannot beat the rank-difference walk's
spread (the self-consistency `2 ln v = c v`, `c ≈ ⅔C ≈ 0.855 > 2/e`, has no solution — confirmed
independently).  The fix is to use the *cumulative window occupation* rather than the single-pass bad
mass: telescoping `umass_core` gives

  `umass m ≤ 1 − δ · ∑_{t<m} goodMass t`,

where `goodMass t` is the unmatched mass *inside* the window at step `t`.  This captures the recurrence
gain — every time the rank-difference walk returns to the window it earns another `δ` of coalescence —
so the convergence reduces to the single occupation input `∑_{t<m} goodMass t → 1/δ` (the rank-difference
walk's window local-time → ∞ for high-rank starts).  This file banks the telescoping half.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)

include hPnn hPmass in
/-- **Window-occupation bound.** Telescoping the one-step contraction `umass_core` (with
`badMass = umass − goodMass`) gives that the unmatched mass after `m` steps is at most `1` minus `δ`
times the *cumulative window occupation* `∑_{t<m} goodMass t`.  Unlike the single-pass ITER bound, this
credits every window-return, so it survives the Erdős constant: coalescence follows once the occupation
reaches `1/δ`. -/
theorem umass_le_one_sub_occupation (m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    umass P rnk W i j m ≤ 1 - δ * ∑ t ∈ Finset.range m, goodMass P rnk W i j t := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
    have hu0 : umass P rnk W i j 0 = 1 := by
      unfold umass
      have hx : ∀ x, ∑ y, Umat P rnk W i j 0 x y = if x = i then (1:ℝ) else 0 := by
        intro x; simp only [Umat]; by_cases hx : x = i <;> simp [hx]
      rw [Finset.sum_congr rfl (fun x _ => hx x),
        Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ)), if_pos (Finset.mem_univ i)]
    rw [hu0]
  | succ m ih =>
    have hc := umass_core P rnk W hPnn hPmass i j m δ hδ0 hminor
    have hbad : badMass P rnk W i j m
        = umass P rnk W i j m - goodMass P rnk W i j m := rfl
    have hstep : umass P rnk W i j (m + 1)
        ≤ umass P rnk W i j m - δ * goodMass P rnk W i j m := by
      rw [hbad] at hc; nlinarith [hc]
    rw [Finset.sum_range_succ, mul_add]
    linarith [ih, hstep]

include hPnn hPmass in
/-- **Overlap from occupation.** Restated as a lower bound on the `m`-step overlap: the two killed-chain
laws overlap by at least `δ` times the cumulative window occupation. -/
theorem overlap_ge_occupation (m : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    δ * ∑ t ∈ Finset.range m, goodMass P rnk W i j t
      ≤ overlap (Mpow P m i) (Mpow P m j) := by
  have hocc := umass_le_one_sub_occupation P rnk W hPnn hPmass i j m δ hδ0 hminor
  have hov : ∑ z, rhovec P rnk W i j m z ≤ overlap (Mpow P m i) (Mpow P m j) :=
    rho_mass_le_overlap P rnk W hPnn hPmass i j m
  have heq : umass P rnk W i j m = 1 - ∑ z, rhovec P rnk W i j m z :=
    umass_eq P rnk W hPnn hPmass i j m
  linarith [hocc, hov, heq]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
