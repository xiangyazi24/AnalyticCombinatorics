import AnalyticCombinatorics.Ch1.OGF.SequenceInverse
import Mathlib.Data.Nat.Fib.Basic

/-!
# Ch1 §I.3 — Fibonacci numbers as compositions into parts `1` and `2`

Flajolet & Sedgewick, Part A, Chapter I, §I.3. Let `D` be the class with one
object of size `1` and one of size `2`. Then `SEQ(D)` enumerates compositions of
`n` into parts of size `1` and `2`, and

* `counts_seq_parts12` — there are `F_{n+1}` of them (`Nat.fib (n+1)`), via the
  convolution recursion `counts_seq_succ`, which here is the Fibonacci recurrence;
* `ogf_parts12` / `ogf_seq_parts12` — `D(z) = z + z²` and the OGF is
  `1/(1 - z - z²)`, the Fibonacci generating function.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class with one object of size `1` and one of size `2` (parts of a
composition into `1`s and `2`s). -/
def CombClass.parts12 : CombClass where
  Obj n := Fin (if n = 1 then 1 else if n = 2 then 1 else 0)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_parts12 (n : ℕ) :
    CombClass.parts12.counts n = if n = 1 then 1 else if n = 2 then 1 else 0 :=
  Fintype.card_fin _

/-- The Fibonacci recurrence, read off the convolution recursion for `SEQ`. -/
private lemma parts12_rec (n : ℕ) :
    CombClass.parts12.seq.counts (n + 2)
      = CombClass.parts12.seq.counts (n + 1) + CombClass.parts12.seq.counts n := by
  rw [counts_seq_succ, Fin.sum_univ_succ]
  congr 1
  · simp [CombClass.counts_parts12]
  · rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [CombClass.counts_parts12]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.eq_of_val_eq h)
      rw [CombClass.counts_parts12, if_neg (by simp only [Fin.val_succ]; omega),
        if_neg (by simp only [Fin.val_succ]; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Compositions into `1`s and `2`s are counted by Fibonacci numbers**
(F&S §I.3): `(SEQ D)ₙ = F_{n+1}`. -/
theorem counts_seq_parts12 (n : ℕ) :
    CombClass.parts12.seq.counts n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [counts_seq_zero, Nat.fib_one]
  | one =>
    rw [counts_seq_succ, Fin.sum_univ_one]
    simp [CombClass.counts_parts12, counts_seq_zero, Nat.fib_two]
  | more n ih1 ih2 =>
    rw [parts12_rec, ih1, ih2, show n + 2 + 1 = n + 1 + 2 from rfl]
    have h := Nat.fib_add_two (n := n + 1)
    omega

/-- `D(z) = z + z²`. -/
theorem CombClass.ogf_parts12 : CombClass.parts12.ogf = X + X ^ 2 := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_parts12, map_add, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | n <;> simp

/-- **The Fibonacci generating function** (F&S §I.3): the OGF of compositions into
`1`s and `2`s satisfies `S(z)·(1 - z - z²) = 1`, i.e. `S(z) = 1/(1 - z - z²)`. -/
theorem CombClass.ogf_seq_parts12 :
    CombClass.parts12.seq.ogf * (1 - (X + X ^ 2)) = 1 := by
  have h := CombClass.ogf_seq_mul (C := CombClass.parts12)
    (by simp [CombClass.counts_parts12])
  rwa [CombClass.ogf_parts12] at h

end AnalyticCombinatorics.Ch1
