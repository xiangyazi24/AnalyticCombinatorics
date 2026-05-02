/-
  Analytic Combinatorics — Part A: Symbolic Method
  Chapter II: Labelled rooted and unrooted trees.

  This file records the Cayley counts used in the Chapter II labelled-tree
  showcase.  The full Lagrange inversion argument for the tree function
      T(z) = z exp(T(z))
  is not developed here; instead we formalize the resulting coefficient and
  counting identities directly.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Basic
import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass

set_option linter.style.show false
set_option linter.style.nativeDecide false

open PowerSeries

/-- Number of labelled rooted trees on `n` vertices.

The empty size has no tree; for positive `n`, Cayley's rooted count is
`n^(n-1)`. -/
def cayleyCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else n ^ (n - 1)

/-- Number of labelled unrooted trees on `n` vertices.

For `n ≥ 2`, Cayley's unrooted count is `n^(n-2)`.  The small exceptional
sizes are set to zero for a total function on `ℕ`. -/
def cayleyUnrooted (n : ℕ) : ℕ :=
  if n < 2 then 0 else n ^ (n - 2)

/-- The exponential generating function of labelled rooted trees, with
coefficients given by Cayley's formula. -/
noncomputable def labelledRootedTreeEgf : PowerSeries ℚ :=
  PowerSeries.mk fun n => (cayleyCount n : ℚ) / n.factorial

theorem cayleyCount_zero : cayleyCount 0 = 0 := by
  simp [cayleyCount]

theorem cayleyCount_eq_pow (n : ℕ) (hn : 0 < n) :
    cayleyCount n = n ^ (n - 1) := by
  simp [cayleyCount, hn.ne']

theorem cayleyCount_one : cayleyCount 1 = 1 := by
  native_decide

theorem cayleyCount_two : cayleyCount 2 = 2 := by
  native_decide

theorem cayleyCount_three : cayleyCount 3 = 9 := by
  native_decide

theorem cayleyCount_four : cayleyCount 4 = 64 := by
  native_decide

theorem cayleyCount_five : cayleyCount 5 = 625 := by
  native_decide

/-- EGF coefficient form of the rooted Cayley count. -/
theorem labelledRootedTreeEgf_coeff (n : ℕ) :
    coeff n labelledRootedTreeEgf = (cayleyCount n : ℚ) / n.factorial := by
  rw [labelledRootedTreeEgf, PowerSeries.coeff_mk]

/-- Lagrange-inversion coefficient consequence for labelled rooted trees,
recorded directly from Cayley's formula. -/
theorem cayley_egf_coeff (n : ℕ) (hn : 0 < n) :
    (cayleyCount n : ℚ) / n.factorial = (n : ℚ) ^ (n - 1) / n.factorial := by
  rw [cayleyCount_eq_pow n hn]
  norm_num

/-- The same coefficient identity stated as a power-series coefficient. -/
theorem labelledRootedTreeEgf_coeff_eq_pow (n : ℕ) (hn : 0 < n) :
    coeff n labelledRootedTreeEgf = (n : ℚ) ^ (n - 1) / n.factorial := by
  rw [labelledRootedTreeEgf_coeff, cayley_egf_coeff n hn]

theorem cayleyUnrooted_zero : cayleyUnrooted 0 = 0 := by
  simp [cayleyUnrooted]

theorem cayleyUnrooted_one : cayleyUnrooted 1 = 0 := by
  simp [cayleyUnrooted]

theorem cayleyUnrooted_eq_pow (n : ℕ) (hn : 2 ≤ n) :
    cayleyUnrooted n = n ^ (n - 2) := by
  simp [cayleyUnrooted, Nat.not_lt.mpr hn]

/-- Cayley's formula proper: labelled unrooted trees on `n ≥ 2` vertices. -/
theorem cayley_unrooted_formula (n : ℕ) (hn : 2 ≤ n) :
    cayleyUnrooted n = n ^ (n - 2) :=
  cayleyUnrooted_eq_pow n hn

/-- Rooting an unrooted labelled tree at one of its `n` vertices gives the
rooted count. -/
theorem cayleyCount_eq_mul_cayleyUnrooted (n : ℕ) (hn : 2 ≤ n) :
    cayleyCount n = n * cayleyUnrooted n := by
  rw [cayleyCount_eq_pow n (by omega), cayleyUnrooted_eq_pow n hn]
  have hsub : n - 1 = n - 2 + 1 := by omega
  rw [hsub, pow_succ, mul_comm]

/-- Prüfer-sequence count: length-`n-2` words over an `n`-letter alphabet. -/
theorem pruferSequence_count (n : ℕ) :
    Fintype.card (Fin (n - 2) → Fin n) = n ^ (n - 2) := by
  simp

/-- For `n ≥ 2`, the unrooted Cayley count equals the Prüfer-sequence count. -/
theorem cayleyUnrooted_eq_pruferSequence_count (n : ℕ) (hn : 2 ≤ n) :
    cayleyUnrooted n = Fintype.card (Fin (n - 2) → Fin n) := by
  rw [cayleyUnrooted_eq_pow n hn, pruferSequence_count n]

