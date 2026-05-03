/-
  Analytic Combinatorics — Part B: Complex Asymptotics
  Chapter VII — Implicit functions and algebraic enumerations.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace ImplicitFunctions

/-! ## 1. Catalan numbers -/

/-- Catalan numbers `C(n)` for `n = 0, ..., 9`. -/
def catalanTable : Fin 10 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]

/-- The Catalan closed-form identity `(n+1) C(n) = binom(2n,n)` for `n = 0, ..., 9`. -/
theorem catalan_formula_table :
    ∀ n : Fin 10, (n.val + 1) * catalanTable n = Nat.choose (2 * n.val) n.val := by
  decide

/-! ## 2. Motzkin numbers -/

/-- Motzkin numbers `M(n)` for `n = 0, ..., 9`. -/
def motzkinTable : Fin 10 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835]

/-- Motzkin numbers satisfy `M(n) < 3^n` for `n = 1, ..., 9`. -/
theorem motzkin_lt_three_pow :
    ∀ i : Fin 9, motzkinTable ⟨i.val + 1, by omega⟩ < 3 ^ (i.val + 1) := by
  decide

/-! ## 3. Ternary trees -/

/-- Ternary tree numbers `T(n) = binom(3n,n)/(2n+1)` for `n = 0, ..., 6`. -/
def ternaryTable : Fin 7 → ℕ :=
  ![1, 1, 3, 12, 55, 273, 1428]

/-- The ternary tree closed-form identity `(2n+1) T(n) = binom(3n,n)` for `n = 0, ..., 6`. -/
theorem ternary_formula_table :
    ∀ n : Fin 7, (2 * n.val + 1) * ternaryTable n = Nat.choose (3 * n.val) n.val := by
  decide

/-! ## 4. 4-ary trees -/

/-- 4-ary tree numbers `binom(4n,n)/(3n+1)` for `n = 0, ..., 4`. -/
def quaternaryTable : Fin 5 → ℕ :=
  ![1, 1, 4, 22, 140]

/-- The 4-ary tree closed-form identity `(3n+1) val(n) = binom(4n,n)` for `n = 0, ..., 4`. -/
theorem quaternary_formula_table :
    ∀ n : Fin 5, (3 * n.val + 1) * quaternaryTable n = Nat.choose (4 * n.val) n.val := by
  decide

/-! ## 5. Catalan numbers dominate Motzkin numbers from `n = 3` to `n = 9`. -/

/-- `C(n) > M(n)` for `n = 3, ..., 9`. -/
theorem catalan_gt_motzkin :
    ∀ i : Fin 7,
      motzkinTable ⟨i.val + 3, by omega⟩ < catalanTable ⟨i.val + 3, by omega⟩ := by
  decide

/-! ## 6. Catalan numbers are below `4^n` for `n = 1` to `n = 9`. -/

/-- `C(n) < 4^n` for `n = 1, ..., 9`. -/
theorem catalan_lt_four_pow :
    ∀ i : Fin 9, catalanTable ⟨i.val + 1, by omega⟩ < 4 ^ (i.val + 1) := by
  decide

end ImplicitFunctions
