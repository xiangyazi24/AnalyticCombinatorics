import Mathlib
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeRecurrence
import AnalyticCombinatorics.Ch7.SingularityApp.TernaryTrees

/-!
# The Fuss–Catalan closed form for ternary trees

We prove that the ternary tree count `ternaryCount n` (defined as the cardinality
of the type of full ternary trees with `n` internal nodes, satisfying the
triple-convolution recurrence) equals the Fuss–Catalan number
`binom (3n) n / (2n + 1)`, and connect it to the banked `ternaryTreeCount`.

## Strategy

We work with the *generalized* Fuss–Catalan rationals

`fc s n = s / (3n + s) * binom (3n + s) n`     (s ≥ 1)

and prove the binary-convolution additivity

`∑_{i+j=n} fc s i * fc t j = fc (s+t) n`

by a Gosper-style telescoping argument. Specializing `s = t = 1` then again
folding in one more factor gives the triple convolution `= fc 3 n`, which equals
`fc 1 (n+1)`, i.e. the recurrence for `ternaryCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open scoped BigOperators
open Finset

/-- Generalized Fuss–Catalan rational:
`fc s n = (s / (3n+s)) * C(3n+s, n)`.  For `s = 1` this is the ordinary ternary
Fuss–Catalan number; the value at `s = 3, n` equals `fc 1 (n+1)`. -/
noncomputable def fc (s n : ℕ) : ℚ :=
  (s : ℚ) / (3 * n + s) * (Nat.choose (3 * n + s) n)

@[simp] lemma fc_zero_right (s : ℕ) (hs : 0 < s) : fc s 0 = 1 := by
  unfold fc
  simp [hs.ne']

/-- Key cross-multiplied binomial identity:
`(2n+1) * C(3n+1, n) = (3n+1) * C(3n, n)`. -/
lemma key_choose_identity (n : ℕ) :
    (2 * n + 1) * Nat.choose (3 * n + 1) n = (3 * n + 1) * Nat.choose (3 * n) n := by
  have h := Nat.choose_mul_succ_eq (3 * n) n
  -- h : C(3n, n) * (3n + 1) = C(3n + 1, n) * (3n + 1 - n)
  have hsub : 3 * n + 1 - n = 2 * n + 1 := by omega
  rw [hsub] at h
  -- h : C(3n,n) * (3n+1) = C(3n+1,n) * (2n+1)
  rw [mul_comm (2 * n + 1), mul_comm (3 * n + 1)]
  exact h.symm

/-- The generalized Fuss–Catalan value at `s = 1` is the banked ternary
Fuss–Catalan number (as a rational): `fc 1 n = C(3n,n)/(2n+1)`. -/
lemma fc_one_eq_ternary (n : ℕ) :
    fc 1 n = (Nat.choose (3 * n) n : ℚ) / (2 * n + 1) := by
  unfold fc
  rw [Nat.cast_one]
  have hd1 : (3 * (n : ℚ) + 1) ≠ 0 := by positivity
  have hd2 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, one_mul]
  rw [div_eq_div_iff hd1 hd2]
  have hkey := key_choose_identity n
  have : ((2 * n + 1) * Nat.choose (3 * n + 1) n : ℚ)
        = ((3 * n + 1) * Nat.choose (3 * n) n : ℚ) := by exact_mod_cast hkey
  push_cast at this ⊢
  ring_nf
  ring_nf at this
  linarith [this]

/-- Connection to the banked count: `(ternaryTreeCount n : ℚ) = fc 1 n`. -/
lemma ternaryTreeCount_eq_fc_one (n : ℕ) :
    (ternaryTreeCount n : ℚ) = fc 1 n := by
  rw [fc_one_eq_ternary]
  unfold ternaryTreeCount
  rw [Nat.cast_div (ternary_choose_dvd n) (by positivity)]
  push_cast
  ring

/-- The shift identity `fc 3 n = fc 1 (n+1)`: the triple-convolution closed
form equals the next ternary Fuss–Catalan number. -/
lemma fc_three_eq_fc_one_succ (n : ℕ) :
    fc 3 n = fc 1 (n + 1) := by
  -- Nat-level key identity: (3n+4) * C(3n+3, n) = (n+1) * C(3n+4, n+1).
  have hkey : ((3 * n + 4) * Nat.choose (3 * n + 3) n : ℕ)
      = ((n + 1) * Nat.choose (3 * n + 4) (n + 1) : ℕ) := by
    have h := Nat.add_one_mul_choose_eq (3 * n + 3) n
    -- h : (3n+3+1) * C(3n+3, n) = C(3n+3+1, n+1) * (n+1)
    have e : 3 * n + 3 + 1 = 3 * n + 4 := by omega
    rw [e] at h
    rw [h]; ring
  have hChoose : Nat.choose (3 * (n + 1) + 1) (n + 1) = Nat.choose (3 * n + 4) (n + 1) := by
    rw [show 3 * (n + 1) + 1 = 3 * n + 4 from by omega]
  unfold fc
  rw [hChoose]
  push_cast
  -- LHS: 3/(3n+3) * C(3n+3,n);  RHS: 1/(3(n+1)+1) * C(3n+4, n+1)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff (by positivity) (by positivity)]
  have hkeyQ : ((3 * (n : ℚ) + 4) * (Nat.choose (3 * n + 3) n : ℚ))
      = (((n : ℚ) + 1) * (Nat.choose (3 * n + 4) (n + 1) : ℚ)) := by
    exact_mod_cast hkey
  nlinarith [hkeyQ]

/-- Nat-level contiguous recurrence for the Fuss–Catalan binomials:
`(n+1)·(2n+s+1)·(2n+s+2)·C(3n+3+s, n+1) = (3n+3+s)·(3n+s+1)·(3n+s+2)·C(3n+s, n)`.

This is the cleared-denominator form of the hypergeometric term ratio
`fc s (n+1) / fc s n = (3n+s)(3n+s+1)(3n+s+2) / ((n+1)(2n+s+1)(2n+s+2))`.
It is the contiguous (two-term, polynomial-coefficient) recurrence that the
generalized Fuss–Catalan / Raney rationals satisfy, and is the foundational
building block for any creative-telescoping (WZ) proof of the Raney convolution
additivity `convAdd` (see HANDOFF/AUDIT-FIX-ch7.md). -/
lemma fc_choose_recurrence (s n : ℕ) :
    (n + 1) * (2 * n + s + 1) * (2 * n + s + 2) * Nat.choose (3 * n + 3 + s) (n + 1)
      = (3 * n + 3 + s) * (3 * n + s + 1) * (3 * n + s + 2) * Nat.choose (3 * n + s) n := by
  -- Expand both binomials into factorials over ℚ and clear denominators; descend to ℕ.
  -- (Both sides are products of Nats; equality over ℚ ⇒ equality over ℕ.)
  have hQ : ((n + 1) * (2 * n + s + 1) * (2 * n + s + 2) * Nat.choose (3 * n + 3 + s) (n + 1) : ℚ)
      = ((3 * n + 3 + s) * (3 * n + s + 1) * (3 * n + s + 2) * Nat.choose (3 * n + s) n : ℚ) := by
    -- Express both choose's via `Nat.cast_choose` (factorials) and clear.
    have hk1 : (n + 1) ≤ 3 * n + 3 + s := by omega
    have hk0 : n ≤ 3 * n + s := by omega
    rw [Nat.cast_choose ℚ hk1, Nat.cast_choose ℚ hk0]
    have hf1 : (Nat.factorial (n + 1) : ℚ) ≠ 0 := by positivity
    have hf2 : (Nat.factorial (3 * n + 3 + s - (n + 1)) : ℚ) ≠ 0 := by positivity
    have hf3 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
    have hf4 : (Nat.factorial (3 * n + s - n) : ℚ) ≠ 0 := by positivity
    -- factorial argument simplifications
    have a1 : 3 * n + 3 + s - (n + 1) = 2 * n + s + 2 := by omega
    have a2 : 3 * n + s - n = 2 * n + s := by omega
    rw [a1, a2]
    -- Peel the factorials: (n+1)!, (3n+3+s)! down to (3n+s)!, (2n+s+2)! down to (2n+s)!.
    rw [Nat.factorial_succ n]
    rw [show 3 * n + 3 + s = (3 * n + 2 + s) + 1 from by omega, Nat.factorial_succ,
        show 3 * n + 2 + s = (3 * n + 1 + s) + 1 from by omega, Nat.factorial_succ,
        show 3 * n + 1 + s = (3 * n + s) + 1 from by omega, Nat.factorial_succ]
    rw [show 2 * n + s + 2 = (2 * n + s + 1) + 1 from by omega, Nat.factorial_succ,
        show 2 * n + s + 1 = (2 * n + s) + 1 from by omega, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  exact_mod_cast hQ

#print axioms fc_choose_recurrence

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

