import AnalyticCombinatorics.PartA.Ch3.MultivariateGF
import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-! # Ch III — Permutation Runs and Fixed Points

Runs in a permutation are maximal ascending consecutive subsequences, so the
number of runs is the number of descents plus one.  This file records small
computable companions to the Eulerian descent table from `MultivariateGF`,
and focuses on derangements and the fixed-point distribution.
-/

namespace PermutationRuns

/-! ## Ascents, descents, runs, and excedances -/

/-- Eulerian number `A(n,k)`, viewed as the number of permutations of `[n]`
with exactly `k` descents. -/
abbrev descentCount (n k : ℕ) : ℕ :=
  MultivariateGF.eulerianNumber n k

/-- The number of permutations of `[n]` with exactly `k` ascents. -/
def ascentCount (n k : ℕ) : ℕ :=
  descentCount n (n - 1 - k)

/-- Runs are descents plus one, so `r` runs corresponds to `r - 1` descents. -/
def runCount (n r : ℕ) : ℕ :=
  if r = 0 then 0 else descentCount n (r - 1)

/-- Boolean finite check for the Eulerian symmetry behind ascent/descent
equidistribution. -/
def ascentDescentSymmetryCheck (n : ℕ) : Bool :=
  (List.range n).all fun k => descentCount n k == ascentCount n k

/-- Total number of excedances over all permutations of `[n]`. -/
def totalExcedances (n : ℕ) : ℕ :=
  n.factorial * (n - 1) / 2

example : ascentCount 4 0 = 1 := by native_decide
example : ascentCount 4 1 = 11 := by native_decide
example : ascentCount 4 2 = 11 := by native_decide
example : ascentCount 4 3 = 1 := by native_decide

example : runCount 4 1 = 1 := by native_decide
example : runCount 4 2 = 11 := by native_decide
example : runCount 4 3 = 11 := by native_decide
example : runCount 4 4 = 1 := by native_decide

example : ascentDescentSymmetryCheck 1 = true := by native_decide
example : ascentDescentSymmetryCheck 2 = true := by native_decide
example : ascentDescentSymmetryCheck 3 = true := by native_decide
example : ascentDescentSymmetryCheck 4 = true := by native_decide
example : ascentDescentSymmetryCheck 5 = true := by native_decide
example : ascentDescentSymmetryCheck 6 = true := by native_decide

example : totalExcedances 2 = 1 := by native_decide
example : totalExcedances 3 = 6 := by native_decide
example : totalExcedances 4 = 36 := by native_decide

/-! ## Derangements and fixed points -/

/-- The subfactorial `!n`, i.e. the number of derangements of `[n]`. -/
def subfactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (subfactorial (n + 1) + subfactorial n)

/-- Number of permutations of `[n]` with exactly `k` fixed points:
choose the fixed points and derange the remaining labels. -/
def fixedPointPerms (n k : ℕ) : ℕ :=
  Nat.choose n k * subfactorial (n - k)

/-- Row sum of the fixed-point distribution. -/
def fixedPointPermsRowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), fixedPointPerms n k

/-- First moment numerator of the fixed-point distribution. -/
def fixedPointPermsWeightedSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k * fixedPointPerms n k

/-- Total fixed points over all permutations of `[n]`. -/
def totalFixedPoints (n : ℕ) : ℕ :=
  n.factorial

@[simp]
theorem fixedPointPerms_zero (n : ℕ) :
    fixedPointPerms n 0 = subfactorial n := by
  simp [fixedPointPerms]

example : subfactorial 0 = 1 := by native_decide
example : subfactorial 1 = 0 := by native_decide
example : subfactorial 2 = 1 := by native_decide
example : subfactorial 3 = 2 := by native_decide
example : subfactorial 4 = 9 := by native_decide
example : subfactorial 5 = 44 := by native_decide
example : subfactorial 6 = 265 := by native_decide

example : fixedPointPerms 0 0 = subfactorial 0 := by native_decide
example : fixedPointPerms 1 0 = subfactorial 1 := by native_decide
example : fixedPointPerms 2 0 = subfactorial 2 := by native_decide
example : fixedPointPerms 3 0 = subfactorial 3 := by native_decide
example : fixedPointPerms 4 0 = subfactorial 4 := by native_decide
example : fixedPointPerms 5 0 = subfactorial 5 := by native_decide
example : fixedPointPerms 6 0 = subfactorial 6 := by native_decide

example : fixedPointPermsRowSum 0 = Nat.factorial 0 := by native_decide
example : fixedPointPermsRowSum 1 = Nat.factorial 1 := by native_decide
example : fixedPointPermsRowSum 2 = Nat.factorial 2 := by native_decide
example : fixedPointPermsRowSum 3 = Nat.factorial 3 := by native_decide
example : fixedPointPermsRowSum 4 = Nat.factorial 4 := by native_decide
example : fixedPointPermsRowSum 5 = Nat.factorial 5 := by native_decide
example : fixedPointPermsRowSum 6 = Nat.factorial 6 := by native_decide

example : fixedPointPermsWeightedSum 1 = totalFixedPoints 1 := by native_decide
example : fixedPointPermsWeightedSum 2 = totalFixedPoints 2 := by native_decide
example : fixedPointPermsWeightedSum 3 = totalFixedPoints 3 := by native_decide
example : fixedPointPermsWeightedSum 4 = totalFixedPoints 4 := by native_decide
example : fixedPointPermsWeightedSum 5 = totalFixedPoints 5 := by native_decide
example : fixedPointPermsWeightedSum 6 = totalFixedPoints 6 := by native_decide

end PermutationRuns
