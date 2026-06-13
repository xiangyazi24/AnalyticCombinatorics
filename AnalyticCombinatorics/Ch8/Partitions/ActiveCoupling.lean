import AnalyticCombinatorics.Ch8.Partitions.HarmonicOverlap
import AnalyticCombinatorics.Ch8.Partitions.ITERCoupling

/-!
# Active coupling inequality (TASK #9 layer B, abstract core)

The route-independent coupling bound for the windowed pair coupling: if `h` is a bounded function on a
finite state type `α` that equals its `m`-step `Mpow`-average at two starts `i, j` (i.e. `h` is
`Mpow`-harmonic at those starts), then

  `|h i_val − h j_val| ≤ umass(i, j, m) · (2 B)`,

where `umass` is the unmatched (non-coalesced) pair mass of the windowed coupling and `2 B` plays the
role of the oscillation constant `osc(h)` (a FIXED finite constant once `h` is bounded — no `u`
oscillation bootstrap is needed).  This is the abstract content behind the spec's

  `|hitVal_J(i) − hitVal_J(j)| ≤ umass_active(i, j) · osc_J(u)`.

Proof: combine `harmonic_diff_le_overlap` (`|hi − hj| ≤ 2 B (1 − overlap p q)`) with the banked coupling
invariants `umass_eq` (`umass = 1 − ∑ ρ`) and `rho_mass_le_overlap` (`∑ ρ ≤ overlap`), giving
`1 − overlap ≤ umass`.  Pure finite-sum linear algebra.  Opus-authored.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
/-- `1 − overlap(Mpow m i, Mpow m j) ≤ umass(i, j, m)`: the un-shared mass of the two `m`-step laws is
controlled by the unmatched coupling mass. -/
lemma one_sub_overlap_le_umass (i j : α) (m : ℕ) :
    1 - overlap (Mpow P m i) (Mpow P m j) ≤ umass P rnk W i j m := by
  have hov : ∑ z, rhovec P rnk W i j m z ≤ overlap (Mpow P m i) (Mpow P m j) :=
    rho_mass_le_overlap P rnk W hPnn hPmass i j m
  have heq : umass P rnk W i j m = 1 - ∑ z, rhovec P rnk W i j m z :=
    umass_eq P rnk W hPnn hPmass i j m
  linarith

include hPnn hPmass in
/-- **Active coupling inequality (abstract).**  For a bounded `h` that is `Mpow`-harmonic at the two
starts `i, j` (its values are the `m`-step `Mpow`-averages of `h`), the two values differ by at most
`umass · (2 B)`.  Here `2 B` is the fixed oscillation constant `osc(h)`. -/
theorem harmonic_diff_le_umass (h : α → ℝ) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
    (hi hj : ℝ) (i j : α) (m : ℕ)
    (hhi : hi = ∑ z, Mpow P m i z * h z) (hhj : hj = ∑ z, Mpow P m j z * h z) :
    |hi - hj| ≤ umass P rnk W i j m * (2 * B) := by
  have hp : ∑ z, Mpow P m i z = 1 := Mpow_mass P hPmass m i
  have hq : ∑ z, Mpow P m j z = 1 := Mpow_mass P hPmass m j
  have hov := harmonic_diff_le_overlap (p := Mpow P m i) (q := Mpow P m j)
    (h := h) (hi := hi) (hj := hj) (B := B) hp hq hB hhi hhj
  -- `|hi − hj| ≤ 2 B (1 − overlap) ≤ 2 B · umass`
  have hone := one_sub_overlap_le_umass P rnk W hPnn hPmass i j m
  -- B ≥ 0 from |h z| ≤ B
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB i)
  have h2B0 : 0 ≤ 2 * B := by linarith
  calc |hi - hj| ≤ 2 * B * (1 - overlap (Mpow P m i) (Mpow P m j)) := hov
    _ ≤ 2 * B * umass P rnk W i j m :=
        mul_le_mul_of_nonneg_left hone h2B0
    _ = umass P rnk W i j m * (2 * B) := by ring

#print axioms one_sub_overlap_le_umass
#print axioms harmonic_diff_le_umass

end AnalyticCombinatorics.Ch8.Partitions.Erdos
