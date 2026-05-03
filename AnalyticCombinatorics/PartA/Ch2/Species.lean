import Mathlib.Tactic
import AnalyticCombinatorics.PartA.Ch2.CycleIndex
import AnalyticCombinatorics.PartA.Ch2.BellNumbers

open Finset

set_option linter.style.nativeDecide false

/-! Chapter II appendix: species, at the level of labelled counting sequences.

We avoid the categorical definition of species and record only the coefficient
data needed for labelled enumeration.  A species is represented here by its
counting sequence `ℕ → ℕ`, where the value at `n` is the number of structures
on an `n`-element label set.
-/

namespace Species

/-- Counting sequence of a species. -/
def speciesCount (species : ℕ → ℕ) (n : ℕ) : ℕ :=
  species n

/-- The atomic species: one structure on a singleton label set. -/
def atomSpeciesCount (n : ℕ) : ℕ :=
  if n = 1 then 1 else 0

/-- The set species: one structure on every finite label set. -/
def setSpeciesCount (_n : ℕ) : ℕ :=
  1

/-- The cycle species: `(n - 1)!` structures on a nonempty `n`-label set. -/
def cycleSpeciesCount (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n - 1).factorial

/-- The species of linear orders: `n!` structures on an `n`-label set. -/
def linearOrderSpeciesCount (n : ℕ) : ℕ :=
  n.factorial

/-- The species of set partitions: Bell numbers. -/
def partitionSpeciesCount (n : ℕ) : ℕ :=
  BellNumbers.bell n

/-- Sum of species counting sequences. -/
def speciesSum (F G : ℕ → ℕ) (n : ℕ) : ℕ :=
  F n + G n

/-- Labelled product of species counting sequences. -/
def speciesProduct (F G : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * F k * G (n - k)

theorem speciesCount_apply (F : ℕ → ℕ) (n : ℕ) :
    speciesCount F n = F n := by
  rfl

theorem atomSpeciesCount_zero : atomSpeciesCount 0 = 0 := by
  native_decide

theorem atomSpeciesCount_one : atomSpeciesCount 1 = 1 := by
  native_decide

theorem atomSpeciesCount_ne_one {n : ℕ} (hn : n ≠ 1) :
    atomSpeciesCount n = 0 := by
  simp [atomSpeciesCount, hn]

theorem setSpeciesCount_eq_one (n : ℕ) :
    setSpeciesCount n = 1 := by
  rfl

theorem cycleSpeciesCount_zero : cycleSpeciesCount 0 = 0 := by
  native_decide

theorem cycleSpeciesCount_succ (n : ℕ) :
    cycleSpeciesCount (n + 1) = n.factorial := by
  simp [cycleSpeciesCount]

theorem linearOrderSpeciesCount_eq_factorial (n : ℕ) :
    linearOrderSpeciesCount n = n.factorial := by
  rfl

theorem partitionSpeciesCount_eq_BellNumbers.bell (n : ℕ) :
    partitionSpeciesCount n = BellNumbers.bell n := by
  rfl

theorem speciesSum_apply (F G : ℕ → ℕ) (n : ℕ) :
    speciesSum F G n = F n + G n := by
  rfl

theorem speciesProduct_apply (F G : ℕ → ℕ) (n : ℕ) :
    speciesProduct F G n =
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k * F k * G (n - k) := by
  rfl

/-! ## Linear orders and the labelled sequence species -/

/-- The EGF coefficient attached to a counting sequence. -/
def speciesEgfCoeff (F : ℕ → ℕ) (n : ℕ) : ℚ :=
  (F n : ℚ) / n.factorial

/-- At the EGF level, labelled linear orders have every coefficient equal to `1`. -/
theorem linearOrderSpecies_egfCoeff_eq_one (n : ℕ) :
    speciesEgfCoeff linearOrderSpeciesCount n = 1 := by
  unfold speciesEgfCoeff linearOrderSpeciesCount
  field_simp [Nat.cast_ne_zero.mpr n.factorial_pos.ne']

/-- A counting-sequence name for the labelled sequence species. -/
def seqSpeciesCount (n : ℕ) : ℕ :=
  n.factorial

theorem linearOrderSpeciesCount_eq_seqSpeciesCount (n : ℕ) :
    linearOrderSpeciesCount n = seqSpeciesCount n := by
  rfl

/-! ## `PERM = SET(CYC)`, checked by cycle decomposition -/

/-- Count of permutations obtained as a set of cycles, grouped by number of cycles. -/
def permViaSetCycleSpeciesCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), cycleTypeCount n k

theorem permViaSetCycleSpeciesCount_eq_factorial (n : ℕ) :
    permViaSetCycleSpeciesCount n = n.factorial := by
  exact stirling1_row_sum n

theorem permViaSetCycleSpeciesCount_eq_linearOrderSpeciesCount (n : ℕ) :
    permViaSetCycleSpeciesCount n = linearOrderSpeciesCount n := by
  rw [permViaSetCycleSpeciesCount_eq_factorial, linearOrderSpeciesCount_eq_factorial]

theorem permViaSetCycleSpeciesCount_zero :
    permViaSetCycleSpeciesCount 0 = 1 := by
  native_decide

theorem permViaSetCycleSpeciesCount_one :
    permViaSetCycleSpeciesCount 1 = 1 := by
  native_decide

theorem permViaSetCycleSpeciesCount_two :
    permViaSetCycleSpeciesCount 2 = 2 := by
  native_decide

theorem permViaSetCycleSpeciesCount_three :
    permViaSetCycleSpeciesCount 3 = 6 := by
  native_decide

theorem permViaSetCycleSpeciesCount_four :
    permViaSetCycleSpeciesCount 4 = 24 := by
  native_decide

theorem permViaSetCycleSpeciesCount_five :
    permViaSetCycleSpeciesCount 5 = 120 := by
  native_decide

theorem permViaSetCycleSpeciesCount_six :
    permViaSetCycleSpeciesCount 6 = 720 := by
  native_decide

/-- Checked instances, for `n = 0, ..., 6`, of `PERM = SET(CYC)`. -/
theorem permViaSetCycleSpeciesCount_checked (n : ℕ) (hn : n ≤ 6) :
    permViaSetCycleSpeciesCount n = linearOrderSpeciesCount n := by
  interval_cases n <;> native_decide

/-! ## Small concrete values -/

theorem partitionSpeciesCount_zero : partitionSpeciesCount 0 = 1 := by
  native_decide

theorem partitionSpeciesCount_one : partitionSpeciesCount 1 = 1 := by
  native_decide

theorem partitionSpeciesCount_two : partitionSpeciesCount 2 = 2 := by
  native_decide

theorem partitionSpeciesCount_three : partitionSpeciesCount 3 = 5 := by
  native_decide

theorem partitionSpeciesCount_four : partitionSpeciesCount 4 = 15 := by
  native_decide

theorem partitionSpeciesCount_five : partitionSpeciesCount 5 = 52 := by
  native_decide

theorem partitionSpeciesCount_six : partitionSpeciesCount 6 = 203 := by
  native_decide


end Species