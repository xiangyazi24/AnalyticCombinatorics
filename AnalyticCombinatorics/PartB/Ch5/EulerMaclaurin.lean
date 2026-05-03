import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace EulerMaclaurin

/-!
Finite numerical tables related to Euler-Maclaurin summation and the
asymptotic constants that occur around Bernoulli, Euler, tangent, and
secant numbers.
-/

def bernoulliNumerators : Fin 13 → ℤ :=
  ![1, -1, 1, 0, -1, 0, 1, 0, -1, 0, 5, 0, -691]

def bernoulliDenominators : Fin 13 → ℕ :=
  ![1, 2, 6, 1, 30, 1, 42, 1, 30, 1, 66, 1, 2730]

def eulerNumbers : Fin 11 → ℤ :=
  ![1, 0, -1, 0, 5, 0, -61, 0, 1385, 0, -50521]

def tangentNumbers : Fin 7 → ℕ :=
  ![1, 2, 16, 272, 7936, 353792, 22368256]

def secantNumbers : Fin 6 → ℕ :=
  ![1, 1, 5, 61, 1385, 50521]

def reciprocalSquareSumNumerators : Fin 10 → ℕ :=
  ![1, 5, 49, 205, 5269, 5369, 266681, 1077749, 9778141, 1968329]

def reciprocalSquareSumDenominators : Fin 10 → ℕ :=
  ![1, 4, 36, 144, 3600, 3600, 176400, 705600, 6350400, 1270080]

def gregoryLeibnizNumerators : Fin 10 → ℤ :=
  ![1, 2, 13, 76, 263, 2578, 36979, 33976, 622637, 11064338]

def gregoryLeibnizDenominators : Fin 10 → ℕ :=
  ![1, 3, 15, 105, 315, 3465, 45045, 45045, 765765, 14549535]

theorem bernoulli_denominators_positive :
    ∀ i : Fin 13, bernoulliDenominators i > 0 := by
  native_decide

theorem bernoulli_odd_numerators_vanish_after_one :
    bernoulliNumerators 3 = 0 ∧
      bernoulliNumerators 5 = 0 ∧
      bernoulliNumerators 7 = 0 ∧
      bernoulliNumerators 9 = 0 ∧
      bernoulliNumerators 11 = 0 := by
  native_decide

theorem bernoulli_twelve_irregular_numerator :
    bernoulliNumerators 12 = -691 ∧ bernoulliDenominators 12 = 2730 := by
  native_decide

theorem euler_odd_entries_vanish :
    eulerNumbers 1 = 0 ∧
      eulerNumbers 3 = 0 ∧
      eulerNumbers 5 = 0 ∧
      eulerNumbers 7 = 0 ∧
      eulerNumbers 9 = 0 := by
  native_decide

theorem secant_numbers_match_abs_even_euler_numbers :
    ∀ i : Fin 6, secantNumbers i = Int.natAbs (eulerNumbers ⟨2 * i.val, by omega⟩) := by
  native_decide

theorem tangent_numbers_strictly_increase :
    ∀ i : Fin 6,
      tangentNumbers ⟨i.val, by omega⟩ < tangentNumbers ⟨i.val + 1, by omega⟩ := by
  native_decide

theorem reciprocal_square_denominators_positive :
    ∀ i : Fin 10, reciprocalSquareSumDenominators i > 0 := by
  native_decide

theorem reciprocal_square_partial_sums_increase_by_cross_product :
    ∀ i : Fin 9,
      reciprocalSquareSumNumerators ⟨i.val, by omega⟩ *
          reciprocalSquareSumDenominators ⟨i.val + 1, by omega⟩ <
        reciprocalSquareSumNumerators ⟨i.val + 1, by omega⟩ *
          reciprocalSquareSumDenominators ⟨i.val, by omega⟩ := by
  native_decide

theorem gregory_leibniz_denominators_positive :
    ∀ i : Fin 10, gregoryLeibnizDenominators i > 0 := by
  native_decide

theorem gregory_leibniz_partial_sums_alternate :
    gregoryLeibnizNumerators 1 * gregoryLeibnizDenominators 0 <
        gregoryLeibnizNumerators 0 * gregoryLeibnizDenominators 1 ∧
      gregoryLeibnizNumerators 1 * gregoryLeibnizDenominators 2 <
        gregoryLeibnizNumerators 2 * gregoryLeibnizDenominators 1 ∧
      gregoryLeibnizNumerators 3 * gregoryLeibnizDenominators 2 <
        gregoryLeibnizNumerators 2 * gregoryLeibnizDenominators 3 := by
  native_decide

end EulerMaclaurin
