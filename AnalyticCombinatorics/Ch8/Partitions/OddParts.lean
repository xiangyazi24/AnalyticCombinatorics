import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.DistinctParts

/-!
# Odd-parts partitions: the log-asymptotic via Euler's partition theorem

Mathlib's `Nat.Partition.card_odds_eq_card_distincts` (Euler's theorem: partitions into odd
parts are equinumerous with partitions into distinct parts) transfers the banked distinct-parts
asymptotic verbatim:

  `log o(n) / √n → π √(1/3)`,

where `o(n)` is the genuine number of partitions of `n` into odd parts.
-/

noncomputable section

open Filter
open scoped Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Odd

/-- The number of partitions of `n` into odd parts, as a real. -/
noncomputable def opart (n : ℕ) : ℝ := ((Nat.Partition.odds n).card : ℝ)

/-- The distinct-parts count `qpart` agrees with the cardinality of Mathlib's `distincts` finset. -/
lemma qpart_eq_distincts_card (n : ℕ) :
    Distinct.qpart n = ((Nat.Partition.distincts n).card : ℝ) := by
  unfold Distinct.qpart Nat.Partition.distincts
  norm_cast
  exact Fintype.card_subtype _

/-- Euler's partition theorem, transported to the real-valued counts. -/
theorem opart_eq_qpart (n : ℕ) : opart n = Distinct.qpart n := by
  rw [qpart_eq_distincts_card, opart]
  exact_mod_cast Nat.Partition.card_odds_eq_card_distincts n

/-- **Odd-parts partitions log-asymptotic**: `log o(n)/√n → π√(1/3)`. -/
theorem odd_log_asymptotic :
    Tendsto (fun n : ℕ => Real.log (opart n) / Real.sqrt n) atTop
      (𝓝 (Real.pi * Real.sqrt (1 / 3))) := by
  have h : (fun n : ℕ => Real.log (opart n) / Real.sqrt n)
      = fun n : ℕ => Real.log (Distinct.qpart n) / Real.sqrt n := by
    funext n; rw [opart_eq_qpart]
  rw [h]
  exact Distinct.distinct_log_asymptotic

end AnalyticCombinatorics.Ch8.Partitions.Odd
