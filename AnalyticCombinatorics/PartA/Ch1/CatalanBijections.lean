/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §3: finite checks for the Catalan family.

  These statements deliberately avoid proving the full bijections.  They record
  the initial common Catalan sequence by executable checks on the already
  formalized finite classes.
-/
import AnalyticCombinatorics.PartA.Ch1.Trees
import AnalyticCombinatorics.PartA.Ch1.LatticePaths

set_option linter.style.show false
set_option linter.style.nativeDecide false

/-- Short name for the Dyck-path semilength counting sequence. -/
def dyckCount (n : ℕ) : ℕ := Nat.centralBinom n / (n + 1)

/-- Triangulations of an `(n + 3)`-gon, counted as `C_{n+1}`. -/
def triangCount (n : ℕ) : ℕ := Nat.centralBinom (n + 1) / (n + 2)

/--
The classical ballot-count expression for paths from `(0,0)` to `(n,n)` that
stay on the permitted side of the diagonal.
-/
def ballotCount (n : ℕ) : ℕ := (2 * n).choose n - (2 * n).choose (n + 1)

private theorem nat_le_six_cases (n : ℕ) (hn : n ≤ 6) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by
  omega

private theorem nat_le_eight_cases (n : ℕ) (hn : n ≤ 8) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by
  omega

/-! ## Binary trees and Dyck paths -/

/-- Binary-tree counts agree with the central-binomial Catalan formula for `n ≤ 8`. -/
theorem binaryTree_catalan (n : ℕ) (hn : n ≤ 8) :
    binaryTreeClass.count n = Nat.centralBinom n / (n + 1) := by
  rcases nat_le_eight_cases n hn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [binaryTreeClass_count_eq_card]
    native_decide

/-- Dyck-path counts agree with the central-binomial Catalan formula for `n ≤ 8`. -/
theorem dyck_catalan (n : ℕ) (hn : n ≤ 8) :
    dyckCount n = Nat.centralBinom n / (n + 1) := by
  rcases nat_le_eight_cases n hn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold dyckCount
    native_decide

/-- Binary-tree and Dyck-path counts give the same initial Catalan sequence. -/
theorem catalan_family_equal (n : ℕ) (hn : n ≤ 8) :
    binaryTreeClass.count n = dyckCount n := by
  rw [binaryTree_catalan n hn, dyck_catalan n hn]

/-! ## Triangulations -/

/-- The first triangulation numbers are the shifted Catalan numbers `C_{n+1}`. -/
theorem triangCount_binaryTree_shifted (n : ℕ) (hn : n ≤ 6) :
    triangCount n = binaryTreeClass.count (n + 1) := by
  rw [binaryTree_catalan (n + 1) (by omega)]
  rcases nat_le_six_cases n hn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold triangCount
    native_decide

/-- Explicit finite check of the triangulation sequence through `n = 6`. -/
theorem triangCount_initial_values :
    triangCount 0 = 1 ∧ triangCount 1 = 2 ∧ triangCount 2 = 5 ∧
      triangCount 3 = 14 ∧ triangCount 4 = 42 ∧ triangCount 5 = 132 ∧
      triangCount 6 = 429 := by
  native_decide

/-! ## Ballot numbers -/

/-- The ballot-count expression gives the Catalan number for `n ≤ 8`. -/
theorem ballotCount_catalan (n : ℕ) (hn : n ≤ 8) :
    ballotCount n = Nat.centralBinom n / (n + 1) := by
  rcases nat_le_eight_cases n hn with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold ballotCount
    native_decide

/-- The ballot-count expression agrees with binary-tree counts for `n ≤ 8`. -/
theorem ballotCount_binaryTree (n : ℕ) (hn : n ≤ 8) :
    ballotCount n = binaryTreeClass.count n := by
  rw [binaryTree_catalan n hn]
  exact ballotCount_catalan n hn
