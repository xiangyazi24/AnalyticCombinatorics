import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace SuccessionRules

/-!
  # Succession Rules (ECO Method)

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.

  A succession rule Ω = (axiom, production) defines a generating tree where the root
  carries the axiom label and each node with label k produces children whose labels
  are determined by the production function. The number of nodes at each level
  enumerates a combinatorial family.
-/

/-! ## Succession rule framework -/

/-- A succession rule defines a generating tree via an axiom label and a production. -/
structure SuccessionRule where
  axiomLabel : ℕ
  production : ℕ → List ℕ

/-- Labels of all nodes at level n of the generating tree. -/
def levelLabels (rule : SuccessionRule) : ℕ → List ℕ
  | 0 => [rule.axiomLabel]
  | n + 1 => (levelLabels rule n).flatMap rule.production

/-- Number of nodes at level n. -/
def levelWidth (rule : SuccessionRule) (n : ℕ) : ℕ :=
  (levelLabels rule n).length

/-- Sum of all labels at level n. -/
def labelSum (rule : SuccessionRule) (n : ℕ) : ℕ :=
  (levelLabels rule n).foldl (fun acc x => acc + x) 0

/-- Maximum label at level n. -/
def maxLabel (rule : SuccessionRule) (n : ℕ) : ℕ :=
  (levelLabels rule n).foldl max 0

/-! ## Binary tree succession rule -/

/-- Ω = { (2); (k) → (2)(3)···(k+1) }. Generates Catalan numbers. -/
def binaryTreeRule : SuccessionRule where
  axiomLabel := 2
  production k := (List.range k).map (· + 2)

example : binaryTreeRule.production 2 = [2, 3] := by native_decide
example : binaryTreeRule.production 3 = [2, 3, 4] := by native_decide
example : binaryTreeRule.production 4 = [2, 3, 4, 5] := by native_decide

theorem bt_production_length :
    ∀ k : Fin 10, (binaryTreeRule.production k.val).length = k.val := by
  native_decide

/-! ## Level structure of binary tree generating tree -/

theorem bt_level_0 : levelLabels binaryTreeRule 0 = [2] := by native_decide
theorem bt_level_1 : levelLabels binaryTreeRule 1 = [2, 3] := by native_decide
theorem bt_level_2 :
    levelLabels binaryTreeRule 2 = [2, 3, 2, 3, 4] := by native_decide

/-! ## Catalan numbers -/

def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

theorem catalan_values :
    [catalan 0, catalan 1, catalan 2, catalan 3, catalan 4,
     catalan 5, catalan 6, catalan 7] =
    [1, 1, 2, 5, 14, 42, 132, 429] := by native_decide

/-! ## Level widths equal Catalan numbers -/

theorem bt_widths :
    [levelWidth binaryTreeRule 0, levelWidth binaryTreeRule 1,
     levelWidth binaryTreeRule 2, levelWidth binaryTreeRule 3,
     levelWidth binaryTreeRule 4, levelWidth binaryTreeRule 5] =
    [1, 2, 5, 14, 42, 132] := by native_decide

theorem bt_width_eq_catalan :
    ∀ n : Fin 6, levelWidth binaryTreeRule n.val = catalan (n.val + 1) := by
  native_decide

/-! ## Label sums predict next level width -/

theorem bt_label_sums :
    [labelSum binaryTreeRule 0, labelSum binaryTreeRule 1,
     labelSum binaryTreeRule 2, labelSum binaryTreeRule 3,
     labelSum binaryTreeRule 4] =
    [2, 5, 14, 42, 132] := by native_decide

theorem bt_label_sum_eq_next_width :
    ∀ n : Fin 5, labelSum binaryTreeRule n.val =
      levelWidth binaryTreeRule (n.val + 1) := by
  native_decide

/-! ## Maximum label growth -/

theorem bt_max_labels :
    [maxLabel binaryTreeRule 0, maxLabel binaryTreeRule 1,
     maxLabel binaryTreeRule 2, maxLabel binaryTreeRule 3,
     maxLabel binaryTreeRule 4, maxLabel binaryTreeRule 5] =
    [2, 3, 4, 5, 6, 7] := by native_decide

theorem bt_max_label_eq :
    ∀ n : Fin 6, maxLabel binaryTreeRule n.val = n.val + 2 := by
  native_decide

/-! ## Fibonacci succession rule -/

/-- Ω = { (1); (1) → (2), (2) → (1)(2) }. Generates Fibonacci numbers. -/
def fibRule : SuccessionRule where
  axiomLabel := 1
  production
    | 1 => [2]
    | 2 => [1, 2]
    | _ => []

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem fib_values :
    [fib 0, fib 1, fib 2, fib 3, fib 4, fib 5, fib 6, fib 7, fib 8, fib 9] =
    [0, 1, 1, 2, 3, 5, 8, 13, 21, 34] := by native_decide

theorem fib_widths :
    [levelWidth fibRule 0, levelWidth fibRule 1, levelWidth fibRule 2,
     levelWidth fibRule 3, levelWidth fibRule 4, levelWidth fibRule 5,
     levelWidth fibRule 6, levelWidth fibRule 7] =
    [1, 1, 2, 3, 5, 8, 13, 21] := by native_decide

theorem fib_width_eq :
    ∀ n : Fin 8, levelWidth fibRule n.val = fib (n.val + 1) := by
  native_decide

/-! ## Doubling rule (powers of 2) -/

/-- Ω = { (2); (k) → (2)^k }. Width doubles each level. -/
def doublingRule : SuccessionRule where
  axiomLabel := 2
  production k := List.replicate k 2

theorem doubling_widths :
    ∀ n : Fin 8, levelWidth doublingRule n.val = 2 ^ n.val := by
  native_decide

theorem doubling_labels_uniform :
    ∀ n : Fin 6, (levelLabels doublingRule n.val).all (· == 2) = true := by
  native_decide

/-! ## Catalan convolution recurrence -/

def catalanConv (n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc k => acc + catalan k * catalan (n - 1 - k)) 0

theorem catalan_recurrence :
    ∀ n : Fin 8, catalan (n.val + 1) = catalanConv (n.val + 1) := by
  native_decide

/-! ## General structural theorems -/

theorem bt_generates_catalan (n : ℕ) :
    levelWidth binaryTreeRule n = catalan (n + 1) := by
  sorry

theorem bt_max_label_general (n : ℕ) :
    maxLabel binaryTreeRule n = n + 2 := by
  sorry

theorem label_sum_predicts_width (rule : SuccessionRule)
    (h : ∀ k, (rule.production k).length = k) (n : ℕ) :
    labelSum rule n = levelWidth rule (n + 1) := by
  sorry

end SuccessionRules
