/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §5: General tree families.

  This file records the Fuss-Catalan count for full `t`-ary trees, counted by
  internal nodes.  The closed form is stated in multiplied-out form, avoiding
  division in the theorem statement.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.Catalan
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch2.LabelledTrees

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries CombinatorialClass

/-! ## Full `t`-ary trees -/

/--
The number of full `t`-ary trees with `n` internal nodes.

The Fuss-Catalan formula is

`1 / (t * n + 1) * Nat.choose (t * n + 1) n`.

Since this is a natural-number count, the definition uses natural division and
the theorem `taryTreeCount_formula` below records the exact multiplied-out
form.
-/
def taryTreeCount (t n : ℕ) : ℕ :=
  (t * n + 1).choose n / (t * n + 1)

/-- The divisor in the Fuss-Catalan formula divides the binomial coefficient. -/
theorem taryTreeCount_dvd_choose (t n : ℕ) :
    t * n + 1 ∣ (t * n + 1).choose n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      set N : ℕ := t * (n + 1) + 1
      have hNpos : 0 < N := by
        dsimp [N]
        omega
      have hcop : N.Coprime (n + 1) := by
        dsimp [N]
        rw [Nat.mul_comm t (n + 1)]
        simp [Nat.add_comm, Nat.coprime_add_mul_left_left]
      have hidentity :
          N * (N - 1).choose n = N.choose (n + 1) * (n + 1) := by
        simpa [Nat.sub_add_cancel hNpos] using Nat.add_one_mul_choose_eq (N - 1) n
      have hdvd_mul : N ∣ N.choose (n + 1) * (n + 1) := by
        rw [← hidentity]
        exact dvd_mul_right N ((N - 1).choose n)
      have hdvd : N ∣ N.choose (n + 1) :=
        (hcop.dvd_mul_right).mp hdvd_mul
      simpa [N] using hdvd

/--
Fuss-Catalan formula for full `t`-ary trees, stated without division:

`(t * n + 1) * Tₙ = binom(t * n + 1, n)`.
-/
theorem taryTreeCount_formula (t n : ℕ) :
    (t * n + 1) * taryTreeCount t n = (t * n + 1).choose n := by
  rw [taryTreeCount]
  exact Nat.mul_div_cancel' (taryTreeCount_dvd_choose t n)

/-! ## Binary case: Catalan numbers -/

private theorem catalan_mul_two_mul_add_one (n : ℕ) :
    (2 * n + 1) * _root_.catalan n = (2 * n + 1).choose n := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)
  calc
    ((2 * n + 1) * _root_.catalan n) * (n + 1)
        = (2 * n + 1) * ((n + 1) * _root_.catalan n) := by ring
    _ = (2 * n + 1) * Nat.centralBinom n := by
        rw [_root_.succ_mul_catalan_eq_centralBinom]
    _ = (2 * n + 1) * (2 * n).choose n := by
        rw [Nat.centralBinom_eq_two_mul_choose]
    _ = (2 * n + 1).choose n * (n + 1) := by
        have h := Nat.add_one_mul_choose_eq (2 * n) n
        have hsymm : (2 * n + 1).choose (n + 1) = (2 * n + 1).choose n := by
          exact Nat.choose_symm_of_eq_add (by omega)
        rwa [hsymm] at h

/-- The binary specialization is Mathlib's Catalan number. -/
theorem taryTreeCount_two_eq_catalan (n : ℕ) :
    taryTreeCount 2 n = _root_.catalan n := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (2 * n))
  rw [taryTreeCount_formula]
  simpa [Nat.succ_eq_add_one] using (catalan_mul_two_mul_add_one n).symm

/-- The binary specialization matches the Chapter I binary-tree class. -/
theorem taryTreeCount_two_eq_binaryTreeClass_count (n : ℕ) :
    taryTreeCount 2 n = binaryTreeClass.count n := by
  rw [taryTreeCount_two_eq_catalan]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [binaryTree_count_zero, _root_.catalan_zero]
      | succ n =>
          rw [binaryTree_count_recursion n, _root_.catalan_succ']
          apply Finset.sum_congr rfl
          intro p hp
          have hp1 : p.1 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          have hp2 : p.2 < n + 1 := by
            have hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
            omega
          rw [ih p.1 hp1, ih p.2 hp2]

/-! ## Sanity checks -/

example : taryTreeCount 2 0 = 1 := by native_decide
example : taryTreeCount 2 1 = 1 := by native_decide
example : taryTreeCount 2 2 = 2 := by native_decide
example : taryTreeCount 2 3 = 5 := by native_decide
example : taryTreeCount 2 4 = 14 := by native_decide

example : taryTreeCount 3 0 = 1 := by native_decide
example : taryTreeCount 3 1 = 1 := by native_decide
example : taryTreeCount 3 2 = 3 := by native_decide
example : taryTreeCount 3 3 = 12 := by native_decide
example : taryTreeCount 3 4 = 55 := by native_decide
example : taryTreeCount 3 5 = 273 := by native_decide

example : (2 * 4 + 1) * taryTreeCount 2 4 = (2 * 4 + 1).choose 4 := by
  native_decide

example : (3 * 4 + 1) * taryTreeCount 3 4 = (3 * 4 + 1).choose 4 := by
  native_decide

/-! ## Cayley trees -/

/-- Chapter I alias for unordered labelled Cayley trees from Chapter II. -/
def cayleyTreeCount (n : ℕ) : ℕ :=
  cayleyUnrooted n

/--
Cross-reference to the Chapter II labelled-tree file: unordered labelled
Cayley trees are already formalized there as `cayleyUnrooted`.
-/
theorem cayley_matches_labelled (n : ℕ) :
    cayleyTreeCount n = cayleyUnrooted n := rfl

/-- Cayley's unrooted labelled-tree formula, re-exported for this section. -/
theorem cayleyTreeCount_formula (n : ℕ) (hn : 2 ≤ n) :
    cayleyTreeCount n = n ^ (n - 2) := by
  rw [cayley_matches_labelled]
  exact cayley_unrooted_formula n hn
