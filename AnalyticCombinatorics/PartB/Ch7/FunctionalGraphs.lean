import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace FunctionalGraphs

open Finset

/-!
Functional graphs, also called endofunction digraphs, are directed graphs
obtained from maps `[n] -> [n]`: every vertex has outdegree one.  This file
records small exact tables and finite checks from Chapter VII of Analytic
Combinatorics.
-/

/-! ## Total endofunctions -/

/-- Number of total functions `[n] -> [n]`. -/
def totalFunctions (n : ℕ) : ℕ :=
  n ^ n

/-- Values of `n^n` for `n = 1, ..., 8`. -/
def totalFunctionTable : Fin 8 → ℕ :=
  ![1, 4, 27, 256, 3125, 46656, 823543, 16777216]

theorem totalFunctions_table :
    ∀ i : Fin 8, totalFunctionTable i = totalFunctions (i.val + 1) := by
  native_decide

theorem totalFunctions_1 : totalFunctions 1 = 1 := by native_decide
theorem totalFunctions_2 : totalFunctions 2 = 4 := by native_decide
theorem totalFunctions_3 : totalFunctions 3 = 27 := by native_decide
theorem totalFunctions_4 : totalFunctions 4 = 256 := by native_decide
theorem totalFunctions_5 : totalFunctions 5 = 3125 := by native_decide
theorem totalFunctions_6 : totalFunctions 6 = 46656 := by native_decide
theorem totalFunctions_7 : totalFunctions 7 = 823543 := by native_decide
theorem totalFunctions_8 : totalFunctions 8 = 16777216 := by native_decide

/-! ## Connected functional graphs -/

/--
Number of connected functional graphs on `[n]` (OEIS A001865).
The standard formula is
`(n - 1)! * sum_{j=0}^{n-1} n^j / j!`, written with integer divisions.
-/
def connectedFunctionalGraphs (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ∑ j ∈ range n, (Nat.factorial (n - 1) / Nat.factorial j) * n ^ j

/-- OEIS A001865 for `n = 1, ..., 8`. -/
def connectedFunctionalGraphTable : Fin 8 → ℕ :=
  ![1, 3, 17, 142, 1569, 21576, 355081, 6805296]

theorem connectedFunctionalGraphs_table :
    ∀ i : Fin 8,
      connectedFunctionalGraphTable i = connectedFunctionalGraphs (i.val + 1) := by
  native_decide

theorem connectedFunctionalGraphs_1 : connectedFunctionalGraphs 1 = 1 := by native_decide
theorem connectedFunctionalGraphs_2 : connectedFunctionalGraphs 2 = 3 := by native_decide
theorem connectedFunctionalGraphs_3 : connectedFunctionalGraphs 3 = 17 := by native_decide
theorem connectedFunctionalGraphs_4 : connectedFunctionalGraphs 4 = 142 := by native_decide
theorem connectedFunctionalGraphs_5 : connectedFunctionalGraphs 5 = 1569 := by native_decide
theorem connectedFunctionalGraphs_6 : connectedFunctionalGraphs 6 = 21576 := by native_decide
theorem connectedFunctionalGraphs_7 : connectedFunctionalGraphs 7 = 355081 := by native_decide
theorem connectedFunctionalGraphs_8 : connectedFunctionalGraphs 8 = 6805296 := by native_decide

/-! ## Bijections among endofunctions -/

/-- Number of permutations of `[n]`, i.e. bijective endofunctions. -/
def permutations (n : ℕ) : ℕ :=
  Nat.factorial n

/-- Values of `n!` for `n = 1, ..., 8`. -/
def permutationTable : Fin 8 → ℕ :=
  ![1, 2, 6, 24, 120, 720, 5040, 40320]

theorem permutations_table :
    ∀ i : Fin 8, permutationTable i = permutations (i.val + 1) := by
  native_decide

/-- Cross-multiplied comparison for `n! / n^n`. -/
def bijectionRatioStrictlyDropsAt (n : ℕ) : Bool :=
  permutations (n + 1) * totalFunctions n < permutations n * totalFunctions (n + 1)

theorem bijectionRatio_decreases_1_to_8 :
    ∀ i : Fin 7, bijectionRatioStrictlyDropsAt (i.val + 1) = true := by
  native_decide

theorem bijectionRatio_drop_1 : bijectionRatioStrictlyDropsAt 1 = true := by native_decide
theorem bijectionRatio_drop_2 : bijectionRatioStrictlyDropsAt 2 = true := by native_decide
theorem bijectionRatio_drop_3 : bijectionRatioStrictlyDropsAt 3 = true := by native_decide
theorem bijectionRatio_drop_4 : bijectionRatioStrictlyDropsAt 4 = true := by native_decide
theorem bijectionRatio_drop_5 : bijectionRatioStrictlyDropsAt 5 = true := by native_decide
theorem bijectionRatio_drop_6 : bijectionRatioStrictlyDropsAt 6 = true := by native_decide
theorem bijectionRatio_drop_7 : bijectionRatioStrictlyDropsAt 7 = true := by native_decide

/-! ## Idempotent functions -/

/--
Number of idempotent functions `f : [n] -> [n]` with `f ∘ f = f`.
Choose the image, whose elements are exactly the fixed points, then map every
remaining element into that image.
-/
def idempotentFunctions (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), Nat.choose n k * k ^ (n - k)

/-- Idempotent endofunction counts for `n = 1, ..., 5`. -/
def idempotentFunctionTable : Fin 5 → ℕ :=
  ![1, 3, 10, 41, 196]

theorem idempotentFunctions_table :
    ∀ i : Fin 5, idempotentFunctionTable i = idempotentFunctions (i.val + 1) := by
  native_decide

theorem idempotentFunctions_0 : idempotentFunctions 0 = 1 := by native_decide
theorem idempotentFunctions_1 : idempotentFunctions 1 = 1 := by native_decide
theorem idempotentFunctions_2 : idempotentFunctions 2 = 3 := by native_decide
theorem idempotentFunctions_3 : idempotentFunctions 3 = 10 := by native_decide
theorem idempotentFunctions_4 : idempotentFunctions 4 = 41 := by native_decide
theorem idempotentFunctions_5 : idempotentFunctions 5 = 196 := by native_decide

/-- Correct recurrence rhs for idempotent functions, with `a(0) = 1`. -/
def idempotentRecurrenceRhs : ℕ → ℕ
  | 0 => 1
  | m + 1 =>
      ∑ j ∈ range (m + 1),
        Nat.choose m j * (j + 1) * idempotentFunctions (m - j)

theorem idempotentRecurrence_0 : idempotentRecurrenceRhs 0 = idempotentFunctions 0 := by
  native_decide

theorem idempotentRecurrence_1 : idempotentRecurrenceRhs 1 = idempotentFunctions 1 := by
  native_decide

theorem idempotentRecurrence_2 : idempotentRecurrenceRhs 2 = idempotentFunctions 2 := by
  native_decide

theorem idempotentRecurrence_3 : idempotentRecurrenceRhs 3 = idempotentFunctions 3 := by
  native_decide

theorem idempotentRecurrence_4 : idempotentRecurrenceRhs 4 = idempotentFunctions 4 := by
  native_decide

theorem idempotentRecurrence_5 : idempotentRecurrenceRhs 5 = idempotentFunctions 5 := by
  native_decide

/--
The often-seen Abel recurrence shape
`a(n) = sum_{k=1}^n C(n,k) k^(k-1) a(n-k)`.
-/
def abelRecurrenceRhs (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, Nat.choose n k * k ^ (k - 1) * a (n - k)

/--
With `a(n) = n^n`, Abel's identity verifies the recurrence for total
endofunctions, not for idempotent endofunctions.
-/
theorem abelRecurrence_totalFunctions_1_to_8 :
    ∀ i : Fin 8,
      abelRecurrenceRhs totalFunctions (i.val + 1) = totalFunctions (i.val + 1) := by
  native_decide

theorem abelRecurrence_idempotent_countercheck_2 :
    abelRecurrenceRhs idempotentFunctions 2 = 4 := by
  native_decide

theorem abelRecurrence_not_idempotent_2 :
    abelRecurrenceRhs idempotentFunctions 2 ≠ idempotentFunctions 2 := by
  native_decide

/-! ## Rho length and the birthday problem -/

/--
Floor of `1000 * sqrt(pi * n / 2)`, using `1570796 / 1000000` for `pi / 2`.
This is the classical scale for the expected rho length, tail plus cycle, of
a random functional graph component reached from a random start vertex.
-/
def rhoLengthApproxMilli (n : ℕ) : ℕ :=
  Nat.sqrt (1570796 * n)

/-- The same asymptotic scale appears as the birthday collision time. -/
def birthdayCollisionApproxMilli (n : ℕ) : ℕ :=
  rhoLengthApproxMilli n

def rhoLengthApproxMilliTable : Fin 8 → ℕ :=
  ![1253, 1772, 2170, 2506, 2802, 3069, 3315, 3544]

theorem rhoLengthApproxMilli_table :
    ∀ i : Fin 8, rhoLengthApproxMilliTable i = rhoLengthApproxMilli (i.val + 1) := by
  native_decide

theorem birthdayCollision_same_scale :
    ∀ i : Fin 8,
      birthdayCollisionApproxMilli (i.val + 1) = rhoLengthApproxMilli (i.val + 1) := by
  native_decide

/-! ## Trees as functional graphs -/

/-- Rooted labelled trees on `[n]`, counted by Cayley's `n^(n-1)`. -/
def rootedLabelledTrees (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

/-- Unrooted labelled trees on `[n]`, with the one-vertex case normalized. -/
def unrootedLabelledTrees (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else n ^ (n - 2)

/-- Summing unrooted labelled trees over all choices of the root. -/
def sumTreesOverRoots (n : ℕ) : ℕ :=
  n * unrootedLabelledTrees n

def rootedLabelledTreeTable : Fin 6 → ℕ :=
  ![1, 2, 9, 64, 625, 7776]

theorem rootedLabelledTrees_table :
    ∀ i : Fin 6, rootedLabelledTreeTable i = rootedLabelledTrees (i.val + 1) := by
  native_decide

theorem sumTreesOverRoots_1 : sumTreesOverRoots 1 = 1 ^ (1 - 1) := by native_decide
theorem sumTreesOverRoots_2 : sumTreesOverRoots 2 = 2 ^ (2 - 1) := by native_decide
theorem sumTreesOverRoots_3 : sumTreesOverRoots 3 = 3 ^ (3 - 1) := by native_decide
theorem sumTreesOverRoots_4 : sumTreesOverRoots 4 = 4 ^ (4 - 1) := by native_decide
theorem sumTreesOverRoots_5 : sumTreesOverRoots 5 = 5 ^ (5 - 1) := by native_decide
theorem sumTreesOverRoots_6 : sumTreesOverRoots 6 = 6 ^ (6 - 1) := by native_decide

theorem sumTreesOverRoots_cayley_1_to_6 :
    ∀ i : Fin 6,
      sumTreesOverRoots (i.val + 1) = rootedLabelledTrees (i.val + 1) := by
  native_decide

end FunctionalGraphs
