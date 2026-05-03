import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticInversionApplications

open scoped BigOperators

/-!
# Applications of analytic inversion to tree enumeration

Chapter VII uses analytic inversion to extract coefficients from tree
specifications.  The Lagrange inversion schema is:

`[z^n] T(z)^k / k = (k/n) * [z^{n-k}] phi(z)^n`, where
`T = z * phi(T)`.

The computational checks below record the standard integer consequences for
tree families.  For labelled Cayley trees, `T = z * exp T`, so the exponential
generating coefficient is `n^(n-1) / n!`, and multiplying by `n!` gives the
rooted labelled tree count `n^(n-1)`.
-/

def lagrangeRightCoefficient (n k phiPowerCoeff : ℕ) : ℚ :=
  (k : ℚ) / (n : ℚ) * (phiPowerCoeff : ℚ)

def lagrangeDividedCoefficient (n phiPowerCoeff : ℕ) : ℚ :=
  (phiPowerCoeff : ℚ) / (n : ℚ)

def catalanNumber (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def cayleyRootedTreeCount (n : ℕ) : ℕ :=
  n ^ (n - 1)

def cayleyEgfCoefficientTimesFactorial (n : ℕ) : ℚ :=
  ((cayleyRootedTreeCount n : ℚ) / (Nat.factorial n : ℚ)) * (Nat.factorial n : ℚ)

def cayleyRootedTreeTable : Fin 8 → ℕ :=
  ![1, 2, 9, 64, 625, 7776, 117649, 2097152]

theorem cayleyRootedTree_table :
    ∀ i : Fin 8, cayleyRootedTreeTable i = cayleyRootedTreeCount (i.val + 1) := by native_decide

theorem cayleyEgf_clears_factorial :
    ∀ i : Fin 8,
      cayleyEgfCoefficientTimesFactorial (i.val + 1)
        = (cayleyRootedTreeCount (i.val + 1) : ℚ) := by native_decide

theorem cayleyRootedTree_1 : cayleyRootedTreeCount 1 = 1 := by native_decide
theorem cayleyRootedTree_2 : cayleyRootedTreeCount 2 = 2 := by native_decide
theorem cayleyRootedTree_3 : cayleyRootedTreeCount 3 = 9 := by native_decide
theorem cayleyRootedTree_4 : cayleyRootedTreeCount 4 = 64 := by native_decide
theorem cayleyRootedTree_5 : cayleyRootedTreeCount 5 = 625 := by native_decide
theorem cayleyRootedTree_6 : cayleyRootedTreeCount 6 = 7776 := by native_decide
theorem cayleyRootedTree_7 : cayleyRootedTreeCount 7 = 117649 := by native_decide
theorem cayleyRootedTree_8 : cayleyRootedTreeCount 8 = 2097152 := by native_decide

/- Ordered plane trees satisfy `T = z / (1 - T)`.
Their coefficient sequence by number of nodes is the shifted Catalan sequence.
-/
def orderedPlaneTreeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => catalanNumber n

def orderedPlaneTreeTable : Fin 8 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429]

theorem orderedPlaneTree_table :
    ∀ i : Fin 8, orderedPlaneTreeTable i = orderedPlaneTreeCount (i.val + 1) := by native_decide

theorem orderedPlaneTree_catalan_shift :
    ∀ i : Fin 8, orderedPlaneTreeCount (i.val + 1) = catalanNumber i.val := by native_decide

/- Unary-binary trees satisfy `T = z + z*T + z*T^2`.
Their coefficient sequence by number of nodes is the shifted Motzkin sequence.
-/
def motzkinNumber (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalanNumber k

def unaryBinaryTreeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => motzkinNumber n

def unaryBinaryTreeTable : Fin 8 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127]

def motzkinTable : Fin 8 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127]

theorem unaryBinaryTree_table :
    ∀ i : Fin 8, unaryBinaryTreeTable i = unaryBinaryTreeCount (i.val + 1) := by native_decide

theorem motzkin_table :
    ∀ i : Fin 8, motzkinTable i = motzkinNumber i.val := by native_decide

theorem motzkin_from_unaryBinary :
    ∀ i : Fin 8, unaryBinaryTreeCount (i.val + 1) = motzkinNumber i.val := by native_decide

theorem unaryBinaryTree_is_motzkin_table :
    ∀ i : Fin 8, unaryBinaryTreeTable i = motzkinTable i := by native_decide

/- `m`-ary trees satisfy `T = z * (1 + T)^m`.
Lagrange inversion gives the Fuss-Catalan count
`1 / (m*n + 1) * choose (m*n + 1) n`.
-/
def fussCatalan (m n : ℕ) : ℕ :=
  Nat.choose (m * n + 1) n / (m * n + 1)

def fussCatalanAlt (m n : ℕ) : ℕ :=
  Nat.choose (m * n) n / ((m - 1) * n + 1)

def fussCatalan3Table : Fin 7 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428]

theorem fussCatalan3_table :
    ∀ i : Fin 7, fussCatalan3Table i = fussCatalan 3 i.val := by native_decide

theorem fussCatalan3_alt_formula :
    ∀ i : Fin 7, fussCatalan 3 i.val = Nat.choose (3 * i.val) i.val / (2 * i.val + 1) := by native_decide

theorem fussCatalan3_alt_table :
    ∀ i : Fin 7, fussCatalan3Table i = fussCatalanAlt 3 i.val := by native_decide

def ternaryTreeCount (n : ℕ) : ℕ :=
  fussCatalan 3 n

def ternaryTreeTable : Fin 7 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428]

theorem ternaryTree_table :
    ∀ i : Fin 7, ternaryTreeTable i = ternaryTreeCount i.val := by native_decide

theorem ternaryTree_is_fussCatalan3 :
    ∀ i : Fin 7, ternaryTreeCount i.val = fussCatalan 3 i.val := by native_decide

def binaryTreeCount (n : ℕ) : ℕ :=
  catalanNumber n

def totalNodesInAllBinaryTrees (n : ℕ) : ℕ :=
  (2 * n + 1) * binaryTreeCount n

def totalBinaryTreeNodesTable : Fin 6 → ℕ :=
  ![3, 10, 35, 126, 462, 1716]

theorem totalBinaryTreeNodes_table :
    ∀ i : Fin 6, totalBinaryTreeNodesTable i = totalNodesInAllBinaryTrees (i.val + 1) := by native_decide

theorem totalBinaryTreeNodes_formula :
    ∀ i : Fin 6,
      totalNodesInAllBinaryTrees (i.val + 1)
        = (2 * (i.val + 1) + 1) * catalanNumber (i.val + 1) := by native_decide

theorem totalBinaryTreeNodes_1 : totalNodesInAllBinaryTrees 1 = 3 := by native_decide
theorem totalBinaryTreeNodes_2 : totalNodesInAllBinaryTrees 2 = 10 := by native_decide
theorem totalBinaryTreeNodes_3 : totalNodesInAllBinaryTrees 3 = 35 := by native_decide
theorem totalBinaryTreeNodes_4 : totalNodesInAllBinaryTrees 4 = 126 := by native_decide
theorem totalBinaryTreeNodes_5 : totalNodesInAllBinaryTrees 5 = 462 := by native_decide
theorem totalBinaryTreeNodes_6 : totalNodesInAllBinaryTrees 6 = 1716 := by native_decide

end AnalyticInversionApplications
