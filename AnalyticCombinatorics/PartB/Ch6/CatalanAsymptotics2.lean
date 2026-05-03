import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace CatalanAsymptotics2

def catalan : Fin 13 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012]

theorem catalan_values :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧
    catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 ∧
    catalan 6 = 132 ∧ catalan 7 = 429 ∧ catalan 8 = 1430 ∧
    catalan 9 = 4862 ∧ catalan 10 = 16796 ∧ catalan 11 = 58786 ∧
    catalan 12 = 208012 := by
  native_decide

def centralBinomial : Fin 11 → ℕ :=
  ![1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756]

theorem central_binomial_values :
    centralBinomial 0 = 1 ∧ centralBinomial 1 = 2 ∧ centralBinomial 2 = 6 ∧
    centralBinomial 3 = 20 ∧ centralBinomial 4 = 70 ∧
    centralBinomial 5 = 252 ∧ centralBinomial 6 = 924 ∧
    centralBinomial 7 = 3432 ∧ centralBinomial 8 = 12870 ∧
    centralBinomial 9 = 48620 ∧ centralBinomial 10 = 184756 := by
  native_decide

theorem central_binomial_catalan_relation :
    ∀ n : Fin 11,
      (n.val + 1) * catalan ⟨n.val, by omega⟩ = centralBinomial n := by
  native_decide

theorem catalan_ratio :
    ∀ n : Fin 11,
      (n.val + 2) * catalan ⟨n.val + 1, by omega⟩ =
        2 * (2 * n.val + 1) * catalan ⟨n.val, by omega⟩ := by
  native_decide

def fine : Fin 11 → ℕ :=
  ![1, 0, 1, 2, 6, 18, 57, 186, 622, 2120, 7338]

theorem fine_values :
    fine 0 = 1 ∧ fine 1 = 0 ∧ fine 2 = 1 ∧ fine 3 = 2 ∧
    fine 4 = 6 ∧ fine 5 = 18 ∧ fine 6 = 57 ∧ fine 7 = 186 ∧
    fine 8 = 622 ∧ fine 9 = 2120 ∧ fine 10 = 7338 := by
  native_decide

theorem catalan_fine_relation :
    ∀ n : Fin 9,
      catalan ⟨n.val + 1, by omega⟩ =
        2 * fine ⟨n.val + 1, by omega⟩ + fine ⟨n.val, by omega⟩ := by
  native_decide

def largeSchroeder : Fin 8 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558]

theorem large_schroeder_values :
    largeSchroeder 0 = 1 ∧ largeSchroeder 1 = 2 ∧ largeSchroeder 2 = 6 ∧
    largeSchroeder 3 = 22 ∧ largeSchroeder 4 = 90 ∧
    largeSchroeder 5 = 394 ∧ largeSchroeder 6 = 1806 ∧
    largeSchroeder 7 = 8558 := by
  native_decide

theorem large_schroeder_gt_twice_catalan :
    ∀ n : Fin 6,
      largeSchroeder ⟨n.val + 2, by omega⟩ >
        2 * catalan ⟨n.val + 2, by omega⟩ := by
  native_decide

def shiftedUpperBinomial : Fin 9 → ℕ :=
  ![1, 4, 15, 56, 210, 792, 3003, 11440, 43758]

theorem shifted_upper_binomial_values :
    shiftedUpperBinomial 0 = 1 ∧ shiftedUpperBinomial 1 = 4 ∧
    shiftedUpperBinomial 2 = 15 ∧ shiftedUpperBinomial 3 = 56 ∧
    shiftedUpperBinomial 4 = 210 ∧ shiftedUpperBinomial 5 = 792 ∧
    shiftedUpperBinomial 6 = 3003 ∧ shiftedUpperBinomial 7 = 11440 ∧
    shiftedUpperBinomial 8 = 43758 := by
  native_decide

theorem ballot_relation :
    ∀ n : Fin 9,
      shiftedUpperBinomial n + catalan ⟨n.val + 1, by omega⟩ =
        centralBinomial ⟨n.val + 1, by omega⟩ := by
  native_decide

end CatalanAsymptotics2
