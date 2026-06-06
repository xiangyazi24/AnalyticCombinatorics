import Mathlib
import AnalyticCombinatorics.Ch8.Partitions.UpperBound

/-!
# Monotonicity of the partition function

`p(n) ≤ p(n+1)`, via the injection `Partition n ↪ Partition (n+1)` that adds a part `1`.
Needed for the forward-propagation step of the Erdős boundedness argument (Stage I.5/I.6).
Opus-authored.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

/-- Add a part `1` to a partition of `n`, giving a partition of `n+1`. -/
private def addOnePart (n : ℕ) (p : Nat.Partition n) : Nat.Partition (n + 1) where
  parts := 1 ::ₘ p.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hmem
    · norm_num
    · exact p.parts_pos hmem
  parts_sum := by
    rw [Multiset.sum_cons, p.parts_sum]
    omega

private lemma addOnePart_injective (n : ℕ) : Function.Injective (addOnePart n) := by
  intro p q h
  have hparts : (1 ::ₘ p.parts) = (1 ::ₘ q.parts) := by
    have := congrArg Nat.Partition.parts h
    simpa [addOnePart] using this
  exact Nat.Partition.ext ((Multiset.cons_inj_right 1).mp hparts)

/-- `p(n) ≤ p(n+1)`. -/
lemma part_le_part_succ (n : ℕ) : part n ≤ part (n + 1) := by
  dsimp [part]
  exact_mod_cast Fintype.card_le_of_injective (addOnePart n) (addOnePart_injective n)

/-- The partition function is monotone. -/
lemma part_mono : Monotone part :=
  monotone_nat_of_le_succ part_le_part_succ

/-- `p(m) ≤ p(n)` for `m ≤ n`. -/
lemma part_le_part {m n : ℕ} (h : m ≤ n) : part m ≤ part n :=
  part_mono h

end AnalyticCombinatorics.Ch8.Partitions
