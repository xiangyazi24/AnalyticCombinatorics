import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace UniformAsymptotics

/-!
Uniform asymptotic expansions and singularity perturbation, with finite
coefficient checks for standard sequences from Chapter VI.
-/

def C (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n / (n + 1)

def catalanTable : Fin 14 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900]

theorem catalan_growth_0_12 :
    ∀ i : Fin 13, catalanTable ⟨i.val, by omega⟩ = C i.val := by
  native_decide

theorem catalan_ratio_integer_identity_0_12 :
    ∀ i : Fin 13,
      let n := i.val
      (n + 2) * C (n + 1) = 2 * (2 * n + 1) * C n := by
  native_decide

def centralBinom (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

theorem central_binomial_dominates_two_pow_0_15 :
    ∀ i : Fin 16, 2 ^ i.val ≤ centralBinom i.val := by
  native_decide

theorem central_binomial_dominates_four_pow_over_2n_plus_1_1_10 :
    ∀ i : Fin 10,
      let n := i.val + 1
      4 ^ n ≤ (2 * n + 1) * centralBinom n := by
  native_decide

def motzkinTable : Fin 11 → ℕ :=
  ![1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188]

theorem motzkin_growth_bounded_by_three_pow_0_10 :
    ∀ i : Fin 11, motzkinTable i ≤ 3 ^ i.val := by
  native_decide

def schroederLargeTable : Fin 8 → ℕ :=
  ![1, 2, 6, 22, 90, 394, 1806, 8558]

def S (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 22
  | 4 => 90
  | 5 => 394
  | 6 => 1806
  | 7 => 8558
  | _ => 0

theorem schroeder_large_table_0_7 :
    ∀ i : Fin 8, schroederLargeTable i = S i.val := by
  native_decide

theorem schroeder_large_recurrence_2_7 :
    ∀ i : Fin 6,
      let n := i.val + 2
      (n + 1) * S n =
        3 * (2 * n - 1) * S (n - 1) - (n - 2) * S (n - 2) := by
  native_decide

def fineTable : Fin 7 → ℕ :=
  ![1, 0, 1, 2, 6, 18, 57]

def F (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 6
  | 5 => 18
  | 6 => 57
  | _ => 0

def fineCatalanRelationTable : Fin 6 → ℕ :=
  ![1, 2, 5, 14, 42, 132]

theorem fine_values_0_6 :
    ∀ i : Fin 7, fineTable i = F i.val := by
  native_decide

theorem fine_catalan_recurrence_1_6 :
    ∀ i : Fin 6,
      let n := i.val + 1
      2 * F n + F (n - 1) = C n := by
  native_decide

theorem fine_relation_table_1_6 :
    ∀ i : Fin 6,
      let n := i.val + 1
      2 * F n + F (n - 1) = fineCatalanRelationTable i := by
  native_decide

def coeffMul (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + a k * b (n - k)) 0

def seriesPow (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => coeffMul (seriesPow a k) a n

def coeffComp (g h : ℕ → ℕ) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun total k => total + g k * seriesPow h k n) 0

def riordanD (d h g _f : ℕ → ℕ) (n : ℕ) : ℕ :=
  coeffMul d (coeffComp g h) n

def riordanH (_d h _g f : ℕ → ℕ) (n : ℕ) : ℕ :=
  coeffComp f h n

def deltaSeries (n : ℕ) : ℕ :=
  if n = 0 then 1 else 0

def zSeries (n : ℕ) : ℕ :=
  if n = 1 then 1 else 0

def pascalD (_n : ℕ) : ℕ :=
  1

def pascalH (n : ℕ) : ℕ :=
  if n = 0 then 0 else 1

def pascalSquareD (n : ℕ) : ℕ :=
  2 ^ n

def pascalSquareH (n : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - 1)

theorem riordan_left_identity_pascal_0_8 :
    (∀ i : Fin 9, riordanD deltaSeries zSeries pascalD pascalH i.val = pascalD i.val) ∧
    (∀ i : Fin 9, riordanH deltaSeries zSeries pascalD pascalH i.val = pascalH i.val) := by
  native_decide

theorem riordan_right_identity_pascal_0_8 :
    (∀ i : Fin 9, riordanD pascalD pascalH deltaSeries zSeries i.val = pascalD i.val) ∧
    (∀ i : Fin 9, riordanH pascalD pascalH deltaSeries zSeries i.val = pascalH i.val) := by
  native_decide

theorem riordan_pascal_square_product_rule_0_8 :
    (∀ i : Fin 9, riordanD pascalD pascalH pascalD pascalH i.val = pascalSquareD i.val) ∧
    (∀ i : Fin 9, riordanH pascalD pascalH pascalD pascalH i.val = pascalSquareH i.val) := by
  native_decide

end UniformAsymptotics
