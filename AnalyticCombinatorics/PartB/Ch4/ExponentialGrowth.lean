import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ExponentialGrowth

/-! ## 1. Powers of 2 -/

def powers2Table : Fin 11 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

example : powers2Table 0 = 1 := by native_decide
example : powers2Table 1 = 2 := by native_decide
example : powers2Table 2 = 4 := by native_decide
example : powers2Table 3 = 8 := by native_decide
example : powers2Table 4 = 16 := by native_decide
example : powers2Table 5 = 32 := by native_decide
example : powers2Table 6 = 64 := by native_decide
example : powers2Table 7 = 128 := by native_decide
example : powers2Table 8 = 256 := by native_decide
example : powers2Table 9 = 512 := by native_decide
example : powers2Table 10 = 1024 := by native_decide

example : powers2Table 1 = 2 * powers2Table 0 := by native_decide
example : powers2Table 2 = 2 * powers2Table 1 := by native_decide
example : powers2Table 3 = 2 * powers2Table 2 := by native_decide
example : powers2Table 4 = 2 * powers2Table 3 := by native_decide
example : powers2Table 5 = 2 * powers2Table 4 := by native_decide
example : powers2Table 6 = 2 * powers2Table 5 := by native_decide
example : powers2Table 7 = 2 * powers2Table 6 := by native_decide
example : powers2Table 8 = 2 * powers2Table 7 := by native_decide
example : powers2Table 9 = 2 * powers2Table 8 := by native_decide
example : powers2Table 10 = 2 * powers2Table 9 := by native_decide

/-! ## 2. Powers of 3 -/

def powers3Table : Fin 9 → ℕ :=
  ![1, 3, 9, 27, 81, 243, 729, 2187, 6561]

example : powers3Table 0 = 1 := by native_decide
example : powers3Table 1 = 3 := by native_decide
example : powers3Table 2 = 9 := by native_decide
example : powers3Table 3 = 27 := by native_decide
example : powers3Table 4 = 81 := by native_decide
example : powers3Table 5 = 243 := by native_decide
example : powers3Table 6 = 729 := by native_decide
example : powers3Table 7 = 2187 := by native_decide
example : powers3Table 8 = 6561 := by native_decide

example : powers3Table 1 > powers2Table 1 := by native_decide
example : powers3Table 2 > powers2Table 2 := by native_decide
example : powers3Table 3 > powers2Table 3 := by native_decide
example : powers3Table 4 > powers2Table 4 := by native_decide
example : powers3Table 5 > powers2Table 5 := by native_decide
example : powers3Table 6 > powers2Table 6 := by native_decide
example : powers3Table 7 > powers2Table 7 := by native_decide
example : powers3Table 8 > powers2Table 8 := by native_decide

/-! ## 3. Fibonacci numbers -/

def fibonacciTable : Fin 21 → ℕ :=
  ![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597,
    2584, 4181, 6765]

example : fibonacciTable 0 = 0 := by native_decide
example : fibonacciTable 1 = 1 := by native_decide
example : fibonacciTable 2 = 1 := by native_decide
example : fibonacciTable 3 = 2 := by native_decide
example : fibonacciTable 4 = 3 := by native_decide
example : fibonacciTable 5 = 5 := by native_decide
example : fibonacciTable 6 = 8 := by native_decide
example : fibonacciTable 7 = 13 := by native_decide
example : fibonacciTable 8 = 21 := by native_decide
example : fibonacciTable 9 = 34 := by native_decide
example : fibonacciTable 10 = 55 := by native_decide
example : fibonacciTable 11 = 89 := by native_decide
example : fibonacciTable 12 = 144 := by native_decide
example : fibonacciTable 13 = 233 := by native_decide
example : fibonacciTable 14 = 377 := by native_decide
example : fibonacciTable 15 = 610 := by native_decide
example : fibonacciTable 16 = 987 := by native_decide
example : fibonacciTable 17 = 1597 := by native_decide
example : fibonacciTable 18 = 2584 := by native_decide
example : fibonacciTable 19 = 4181 := by native_decide
example : fibonacciTable 20 = 6765 := by native_decide

example : fibonacciTable 0 < 2 ^ 0 := by native_decide
example : fibonacciTable 1 < 2 ^ 1 := by native_decide
example : fibonacciTable 2 < 2 ^ 2 := by native_decide
example : fibonacciTable 3 < 2 ^ 3 := by native_decide
example : fibonacciTable 4 < 2 ^ 4 := by native_decide
example : fibonacciTable 5 < 2 ^ 5 := by native_decide
example : fibonacciTable 6 < 2 ^ 6 := by native_decide
example : fibonacciTable 7 < 2 ^ 7 := by native_decide
example : fibonacciTable 8 < 2 ^ 8 := by native_decide
example : fibonacciTable 9 < 2 ^ 9 := by native_decide
example : fibonacciTable 10 < 2 ^ 10 := by native_decide
example : fibonacciTable 11 < 2 ^ 11 := by native_decide
example : fibonacciTable 12 < 2 ^ 12 := by native_decide
example : fibonacciTable 13 < 2 ^ 13 := by native_decide
example : fibonacciTable 14 < 2 ^ 14 := by native_decide
example : fibonacciTable 15 < 2 ^ 15 := by native_decide
example : fibonacciTable 16 < 2 ^ 16 := by native_decide
example : fibonacciTable 17 < 2 ^ 17 := by native_decide
example : fibonacciTable 18 < 2 ^ 18 := by native_decide
example : fibonacciTable 19 < 2 ^ 19 := by native_decide
example : fibonacciTable 20 < 2 ^ 20 := by native_decide

example : fibonacciTable 2 ^ 2 + 1 = fibonacciTable 1 * fibonacciTable 3 := by native_decide
example : fibonacciTable 2 * fibonacciTable 4 + 1 = fibonacciTable 3 ^ 2 := by native_decide
example : fibonacciTable 4 ^ 2 + 1 = fibonacciTable 3 * fibonacciTable 5 := by native_decide
example : fibonacciTable 4 * fibonacciTable 6 + 1 = fibonacciTable 5 ^ 2 := by native_decide
example : fibonacciTable 6 ^ 2 + 1 = fibonacciTable 5 * fibonacciTable 7 := by native_decide
example : fibonacciTable 6 * fibonacciTable 8 + 1 = fibonacciTable 7 ^ 2 := by native_decide
example : fibonacciTable 8 ^ 2 + 1 = fibonacciTable 7 * fibonacciTable 9 := by native_decide

/-! ## 4. Catalan numbers -/

def catalanTable : Fin 12 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786]

example : catalanTable 0 = 1 := by native_decide
example : catalanTable 1 = 1 := by native_decide
example : catalanTable 2 = 2 := by native_decide
example : catalanTable 3 = 5 := by native_decide
example : catalanTable 4 = 14 := by native_decide
example : catalanTable 5 = 42 := by native_decide
example : catalanTable 6 = 132 := by native_decide
example : catalanTable 7 = 429 := by native_decide
example : catalanTable 8 = 1430 := by native_decide
example : catalanTable 9 = 4862 := by native_decide
example : catalanTable 10 = 16796 := by native_decide
example : catalanTable 11 = 58786 := by native_decide

example : catalanTable 1 < 4 ^ 1 := by native_decide
example : catalanTable 2 < 4 ^ 2 := by native_decide
example : catalanTable 3 < 4 ^ 3 := by native_decide
example : catalanTable 4 < 4 ^ 4 := by native_decide
example : catalanTable 5 < 4 ^ 5 := by native_decide
example : catalanTable 6 < 4 ^ 6 := by native_decide
example : catalanTable 7 < 4 ^ 7 := by native_decide
example : catalanTable 8 < 4 ^ 8 := by native_decide
example : catalanTable 9 < 4 ^ 9 := by native_decide
example : catalanTable 10 < 4 ^ 10 := by native_decide
example : catalanTable 11 < 4 ^ 11 := by native_decide

example : catalanTable 2 < 4 * catalanTable 1 := by native_decide
example : catalanTable 3 < 4 * catalanTable 2 := by native_decide
example : catalanTable 4 < 4 * catalanTable 3 := by native_decide
example : catalanTable 5 < 4 * catalanTable 4 := by native_decide
example : catalanTable 6 < 4 * catalanTable 5 := by native_decide
example : catalanTable 7 < 4 * catalanTable 6 := by native_decide
example : catalanTable 8 < 4 * catalanTable 7 := by native_decide
example : catalanTable 9 < 4 * catalanTable 8 := by native_decide
example : catalanTable 10 < 4 * catalanTable 9 := by native_decide
example : catalanTable 11 < 4 * catalanTable 10 := by native_decide

/-! ## 5. Partial fractions -/

def geom2PartialTable : Fin 9 → ℕ :=
  ![1, 3, 7, 15, 31, 63, 127, 255, 511]

example : geom2PartialTable 0 = 2 ^ (0 + 1) - 1 := by native_decide
example : geom2PartialTable 1 = 2 ^ (1 + 1) - 1 := by native_decide
example : geom2PartialTable 2 = 2 ^ (2 + 1) - 1 := by native_decide
example : geom2PartialTable 3 = 2 ^ (3 + 1) - 1 := by native_decide
example : geom2PartialTable 4 = 2 ^ (4 + 1) - 1 := by native_decide
example : geom2PartialTable 5 = 2 ^ (5 + 1) - 1 := by native_decide
example : geom2PartialTable 6 = 2 ^ (6 + 1) - 1 := by native_decide
example : geom2PartialTable 7 = 2 ^ (7 + 1) - 1 := by native_decide
example : geom2PartialTable 8 = 2 ^ (8 + 1) - 1 := by native_decide

def geom23DiffTable : Fin 6 → ℕ :=
  ![1, 5, 19, 65, 211, 665]

example : geom23DiffTable 0 = 3 ^ (0 + 1) - 2 ^ (0 + 1) := by native_decide
example : geom23DiffTable 1 = 3 ^ (1 + 1) - 2 ^ (1 + 1) := by native_decide
example : geom23DiffTable 2 = 3 ^ (2 + 1) - 2 ^ (2 + 1) := by native_decide
example : geom23DiffTable 3 = 3 ^ (3 + 1) - 2 ^ (3 + 1) := by native_decide
example : geom23DiffTable 4 = 3 ^ (4 + 1) - 2 ^ (4 + 1) := by native_decide
example : geom23DiffTable 5 = 3 ^ (5 + 1) - 2 ^ (5 + 1) := by native_decide

/-! ## 6. Growth hierarchy -/

example : Nat.factorial 9 > 4 ^ 9 := by native_decide
example : Nat.factorial 10 > 4 ^ 10 := by native_decide
example : Nat.factorial 11 > 4 ^ 11 := by native_decide
example : Nat.factorial 12 > 4 ^ 12 := by native_decide

example : Nat.factorial 7 > 3 ^ 7 := by native_decide
example : Nat.factorial 8 > 3 ^ 8 := by native_decide
example : Nat.factorial 9 > 3 ^ 9 := by native_decide
example : Nat.factorial 10 > 3 ^ 10 := by native_decide

example : 4 ^ 1 > 3 ^ 1 ∧ 3 ^ 1 > 2 ^ 1 := by native_decide
example : 4 ^ 2 > 3 ^ 2 ∧ 3 ^ 2 > 2 ^ 2 := by native_decide
example : 4 ^ 3 > 3 ^ 3 ∧ 3 ^ 3 > 2 ^ 3 := by native_decide
example : 4 ^ 4 > 3 ^ 4 ∧ 3 ^ 4 > 2 ^ 4 := by native_decide
example : 4 ^ 5 > 3 ^ 5 ∧ 3 ^ 5 > 2 ^ 5 := by native_decide
example : 4 ^ 6 > 3 ^ 6 ∧ 3 ^ 6 > 2 ^ 6 := by native_decide
example : 4 ^ 7 > 3 ^ 7 ∧ 3 ^ 7 > 2 ^ 7 := by native_decide
example : 4 ^ 8 > 3 ^ 8 ∧ 3 ^ 8 > 2 ^ 8 := by native_decide
example : 4 ^ 9 > 3 ^ 9 ∧ 3 ^ 9 > 2 ^ 9 := by native_decide
example : 4 ^ 10 > 3 ^ 10 ∧ 3 ^ 10 > 2 ^ 10 := by native_decide

end ExponentialGrowth
