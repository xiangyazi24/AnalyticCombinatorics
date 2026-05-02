/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter I §5: Functional equations and counting sequences.

  This file formalizes the core functional equations arising in tree enumeration:
  - Binary trees: T = 1 + z·T² (Catalan numbers)
  - Motzkin numbers (unary-binary trees)
  - Ternary trees: T = 1 + z·T³ (Fuss-Catalan numbers)
  - Ordered trees = Catalan numbers

  All verifications use finite checks via native_decide.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace FunctionalEquations

/-! ## Binary tree counting via T = 1 + z·T² -/

/-- The Catalan recursion: T(0) = 1, T(n+1) = Σ_{k=0}^{n} T(k)·T(n-k).
    This is the coefficient recursion for the functional equation T(z) = 1 + z·T(z)². -/
def treeRecursion : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), treeRecursion k.val * treeRecursion (n - k.val)
termination_by n => n
decreasing_by all_goals omega

/-- The closed-form Catalan number: C(n) = C(2n,n)/(n+1). -/
def catalanFormula (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

-- Verify treeRecursion gives Catalan numbers for n = 0..8
example : treeRecursion 0 = 1 := by native_decide
example : treeRecursion 1 = 1 := by native_decide
example : treeRecursion 2 = 2 := by native_decide
example : treeRecursion 3 = 5 := by native_decide
example : treeRecursion 4 = 14 := by native_decide
example : treeRecursion 5 = 42 := by native_decide
example : treeRecursion 6 = 132 := by native_decide
example : treeRecursion 7 = 429 := by native_decide
example : treeRecursion 8 = 1430 := by native_decide

-- Verify treeRecursion matches the Catalan formula C(2n,n)/(n+1) for n = 0..8
example : treeRecursion 0 = catalanFormula 0 := by native_decide
example : treeRecursion 1 = catalanFormula 1 := by native_decide
example : treeRecursion 2 = catalanFormula 2 := by native_decide
example : treeRecursion 3 = catalanFormula 3 := by native_decide
example : treeRecursion 4 = catalanFormula 4 := by native_decide
example : treeRecursion 5 = catalanFormula 5 := by native_decide
example : treeRecursion 6 = catalanFormula 6 := by native_decide
example : treeRecursion 7 = catalanFormula 7 := by native_decide
example : treeRecursion 8 = catalanFormula 8 := by native_decide

/-! ## Motzkin numbers (unary-binary trees) -/

/-- Motzkin numbers as a lookup table: M(0)=1, M(1)=1, M(2)=2, M(3)=4,
    M(4)=9, M(5)=21, M(6)=51, M(7)=127, M(8)=323.
    These count unary-binary trees satisfying M = 1 + z·M + z·M². -/
def motzkinTable : Fin 9 → ℕ := ![1, 1, 2, 4, 9, 21, 51, 127, 323]

-- Verify specific Motzkin values
example : motzkinTable 0 = 1 := by native_decide
example : motzkinTable 1 = 1 := by native_decide
example : motzkinTable 2 = 2 := by native_decide
example : motzkinTable 3 = 4 := by native_decide
example : motzkinTable 4 = 9 := by native_decide
example : motzkinTable 5 = 21 := by native_decide
example : motzkinTable 6 = 51 := by native_decide
example : motzkinTable 7 = 127 := by native_decide
example : motzkinTable 8 = 323 := by native_decide

/-- Motzkin recursion: (n+2)·M(n) = (2n+4)·M(n+1) - 3n·M(n) ... simplified to
    the convolution (n+2)M(n+2) = (2n+3)M(n+1) + 3∑_{k=0}^{n} M(k)M(n-k).
    We verify the recursion holds for specific values via the three-term relation:
    (n+3)M(n+2) = (2n+5)M(n+1) + 3M(n) which doesn't quite hold in general,
    but the actual Motzkin recurrence is:
    M(n+1) = M(n) + Σ_{k=0}^{n-1} M(k)·M(n-1-k)  (from M = 1 + z·M + z²·M²). -/
def motzkinRecursion : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => motzkinRecursion (n + 1) +
      ∑ k : Fin (n + 1), motzkinRecursion k.val * motzkinRecursion (n - k.val)
termination_by n => n
decreasing_by all_goals omega

-- Verify the recursion matches the table
example : motzkinRecursion 0 = motzkinTable 0 := by native_decide
example : motzkinRecursion 1 = motzkinTable 1 := by native_decide
example : motzkinRecursion 2 = motzkinTable 2 := by native_decide
example : motzkinRecursion 3 = motzkinTable 3 := by native_decide
example : motzkinRecursion 4 = motzkinTable 4 := by native_decide
example : motzkinRecursion 5 = motzkinTable 5 := by native_decide
example : motzkinRecursion 6 = motzkinTable 6 := by native_decide
example : motzkinRecursion 7 = motzkinTable 7 := by native_decide
example : motzkinRecursion 8 = motzkinTable 8 := by native_decide

/-! ## Ternary trees: T = 1 + z·T³ -/

/-- Ternary tree counting sequence from T = 1 + z·T³.
    Values: 1, 1, 3, 12, 55, 273. -/
def ternaryTreeTable : Fin 6 → ℕ := ![1, 1, 3, 12, 55, 273]

-- Verify specific ternary tree values
example : ternaryTreeTable 0 = 1 := by native_decide
example : ternaryTreeTable 1 = 1 := by native_decide
example : ternaryTreeTable 2 = 3 := by native_decide
example : ternaryTreeTable 3 = 12 := by native_decide
example : ternaryTreeTable 4 = 55 := by native_decide
example : ternaryTreeTable 5 = 273 := by native_decide

/-- Fuss-Catalan number: C_m(n) = C(m·n, n) / ((m-1)·n + 1).
    For ternary trees m = 3: C_3(n) = C(3n, n) / (2n + 1). -/
def fussCatalan3 (n : ℕ) : ℕ := Nat.choose (3 * n) n / (2 * n + 1)

-- Verify ternary tree table matches Fuss-Catalan C_3(n)
example : ternaryTreeTable 0 = fussCatalan3 0 := by native_decide
example : ternaryTreeTable 1 = fussCatalan3 1 := by native_decide
example : ternaryTreeTable 2 = fussCatalan3 2 := by native_decide
example : ternaryTreeTable 3 = fussCatalan3 3 := by native_decide
example : ternaryTreeTable 4 = fussCatalan3 4 := by native_decide
example : ternaryTreeTable 5 = fussCatalan3 5 := by native_decide

/-! ## Ordered trees = Catalan -/

/-- The number of ordered trees with n edges equals the n-th Catalan number.
    This follows from the bijection between ordered trees and binary trees. -/
example : catalanFormula 0 = 1 := by native_decide
example : catalanFormula 1 = 1 := by native_decide
example : catalanFormula 2 = 2 := by native_decide
example : catalanFormula 3 = 5 := by native_decide
example : catalanFormula 4 = 14 := by native_decide
example : catalanFormula 5 = 42 := by native_decide

/-- C_5 = 42: the number of ordered trees with 5 edges. -/
example : Nat.choose 10 5 / 6 = 42 := by native_decide

/-- C_6 = 132: the number of ordered trees with 6 edges. -/
example : Nat.choose 12 6 / 7 = 132 := by native_decide

/-! ## Cross-verification: Catalan formula properties -/

/-- Catalan numbers satisfy C(n) = C(2n,n)/(n+1) for several values. -/
theorem catalan_initial_segment :
    catalanFormula 0 = 1 ∧ catalanFormula 1 = 1 ∧ catalanFormula 2 = 2 ∧
    catalanFormula 3 = 5 ∧ catalanFormula 4 = 14 ∧ catalanFormula 5 = 42 ∧
    catalanFormula 6 = 132 ∧ catalanFormula 7 = 429 ∧ catalanFormula 8 = 1430 := by
  native_decide

/-- The functional equation T = 1 + z·T² is the defining equation for binary trees.
    Its solution has coefficients given by Catalan numbers. We verify the recursion
    relation: C(n+1) = Σ_{k=0}^{n} C(k)·C(n-k). -/
theorem catalan_convolution_check :
    treeRecursion 1 = treeRecursion 0 * treeRecursion 0 ∧
    treeRecursion 2 = treeRecursion 0 * treeRecursion 1 +
                      treeRecursion 1 * treeRecursion 0 ∧
    treeRecursion 3 = treeRecursion 0 * treeRecursion 2 +
                      treeRecursion 1 * treeRecursion 1 +
                      treeRecursion 2 * treeRecursion 0 := by
  native_decide

/-- Fuss-Catalan generalizes Catalan: C_2(n) = C(2n,n)/(n+1) = catalanFormula(n). -/
def fussCatalan2 (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

example : fussCatalan2 0 = catalanFormula 0 := by native_decide
example : fussCatalan2 1 = catalanFormula 1 := by native_decide
example : fussCatalan2 2 = catalanFormula 2 := by native_decide
example : fussCatalan2 3 = catalanFormula 3 := by native_decide
example : fussCatalan2 4 = catalanFormula 4 := by native_decide
example : fussCatalan2 5 = catalanFormula 5 := by native_decide
example : fussCatalan2 6 = catalanFormula 6 := by native_decide
example : fussCatalan2 7 = catalanFormula 7 := by native_decide
example : fussCatalan2 8 = catalanFormula 8 := by native_decide

end FunctionalEquations
