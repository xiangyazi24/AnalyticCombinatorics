import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.PartMono
import AnalyticCombinatorics.Ch8.Partitions.ErdosKernel

/-!
# Forward propagation of `u` from partition monotonicity

`u(n+r) ≥ ((n+r)/n)·e^{−C(√(n+r)−√n)}·u(n)` — a high value of `u` propagates forward to
nearby indices, since `p` is monotone and the normalization factors are explicit.
The block-propagation step of the Erdős convergence argument (Stage I.6).  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions

theorem u_local_lower_from_monotone {n : ℕ} (r : ℕ) (hn : 1 ≤ n) :
    ((n + r : ℕ) : ℝ) / (n : ℝ) *
        Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))) * u n
      ≤ u (n + r) := by
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : part n ≤ part (n + r) := part_le_part (Nat.le_add_right n r)
  have hppos : 0 < part n := part_pos n
  have hexp_merge :
      Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))) *
        Real.exp (-C * Real.sqrt (n : ℝ))
        = Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold u
  -- LHS rearranged: (n+r)·p(n)·(E_Δ·E_n), then merge the exponentials
  have hkey :
      ((n + r : ℕ) : ℝ) / (n : ℝ) *
          Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))) *
          ((n : ℝ) * part n * Real.exp (-C * Real.sqrt (n : ℝ)))
        = ((n + r : ℕ) : ℝ) * part n *
            (Real.exp (-C * (Real.sqrt ((n + r : ℕ) : ℝ) - Real.sqrt (n : ℝ))) *
              Real.exp (-C * Real.sqrt (n : ℝ))) := by
    field_simp
    ring
  rw [hkey, hexp_merge]
  -- now compare (n+r)·p(n)·E ≤ (n+r)·p(n+r)·E
  have hfac : (0 : ℝ) ≤ ((n + r : ℕ) : ℝ) *
      Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ)) := by positivity
  calc ((n + r : ℕ) : ℝ) * part n * Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ))
      = (((n + r : ℕ) : ℝ) * Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ))) * part n := by
        ring
    _ ≤ (((n + r : ℕ) : ℝ) * Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ))) * part (n + r) :=
        mul_le_mul_of_nonneg_left hp hfac
    _ = ((n + r : ℕ) : ℝ) * part (n + r) * Real.exp (-C * Real.sqrt ((n + r : ℕ) : ℝ)) := by
        ring

end AnalyticCombinatorics.Ch8.Partitions.Erdos
