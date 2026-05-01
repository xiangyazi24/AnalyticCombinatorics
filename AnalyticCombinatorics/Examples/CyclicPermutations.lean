import AnalyticCombinatorics.PartA.Ch1.CombinatorialClass
import AnalyticCombinatorics.PartA.Ch2.LabelledClass
import Mathlib.GroupTheory.Perm.Cycle.Basic

open CombinatorialClass

/-- A cyclic permutation of `Fin n` is a permutation with a single orbit under
    repeated application. This convention includes the empty permutation on
    `Fin 0` and the identity permutation on `Fin 1`. -/
def IsCyclicPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x y : Fin n, σ.SameCycle x y

/-- The type of cyclic permutations on `Fin n`. -/
def CyclicPermutation (n : ℕ) : Type :=
  { σ : Equiv.Perm (Fin n) // IsCyclicPermutation σ }

/-- The usual count of cyclic permutations of size `n`, with zero objects at
    size zero and `(n - 1)!` objects at positive size. -/
def cyclicPermutationCount (n : ℕ) : ℚ :=
  if n = 0 then 0 else ((n - 1).factorial : ℚ)

@[simp]
theorem cyclicPermutationCount_zero : cyclicPermutationCount 0 = 0 := by
  simp [cyclicPermutationCount]

@[simp]
theorem cyclicPermutationCount_succ (n : ℕ) :
    cyclicPermutationCount (n + 1) = (n.factorial : ℚ) := by
  simp [cyclicPermutationCount]

/-- The empty permutation on `Fin 0` satisfies the one-orbit convention
    vacuously. -/
example (σ : Equiv.Perm (Fin 0)) : IsCyclicPermutation σ := by
  intro x
  exact Fin.elim0 x

/-- The unique permutation on `Fin 1` is the unique 1-cycle. -/
example (σ : Equiv.Perm (Fin 1)) : IsCyclicPermutation σ := by
  intro x y
  exact (Subsingleton.elim x y).sameCycle σ

/-- Cardinality bridge: `labelCycCount Atom (n+1) = ((n+1)-1)!`. -/
example (n : ℕ) : labelCycCount Atom (n + 1) = (n.factorial : ℚ) :=
  labelCycCount_Atom_succ n

/-- Labelled cycle count agrees with the cyclic permutation count at positive
    sizes. -/
theorem labelCycCount_Atom_eq_cyclicPermutationCount_succ (n : ℕ) :
    labelCycCount Atom (n + 1) = cyclicPermutationCount (n + 1) := by
  rw [labelCycCount_Atom_succ, cyclicPermutationCount_succ]

/-- Sanity: 1-cycles, 2-cycles, 3-cycles, 4-cycles, 5-cycles. -/
example : labelCycCount Atom 0 = 0 := by
  simp [CombinatorialClass.labelCycCount]

example : labelCycCount Atom 1 = 1 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 2 = 1 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 3 = 2 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 4 = 6 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 5 = 24 := by
  rw [labelCycCount_Atom_succ]
  rfl

example : labelCycCount Atom 6 = 120 := labelCycCount_Atom_succ 5  -- 5! = 120
example : labelCycCount Atom 7 = 720 := labelCycCount_Atom_succ 6  -- 6! = 720
example : labelCycCount Atom 8 = 5040 := labelCycCount_Atom_succ 7  -- 7! = 5040
example : labelCycCount Atom 9 = 40320 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 10 = 362880 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 11 = 3628800 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 12 = 39916800 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 13 = 479001600 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 14 = 6227020800 := by
  rw [labelCycCount_Atom_succ]
  decide
example : labelCycCount Atom 15 = 87178291200 := by
  rw [labelCycCount_Atom_succ]
  decide

/-- The Atom labelled SET equals 1, the Atom labelled CYC at `n` equals
    `(n - 1)!`, and these connect via the standard `exp(log(...))` relation;
    we do not formalize that composition here.

    A simpler concrete identity: the EGF of permutation cycles equals
    `log(1/(1-z))`. The EGF coefficient at `n` is `1/n`: that is,
    `labelCycCount Atom n / n! = (n-1)! / n! = 1/n`. -/
example (n : ℕ) (hn : 1 ≤ n) :
    labelCycCount Atom n / (n.factorial : ℚ) = 1 / (n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [labelCycCount_Atom_succ]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The EGF coefficient of labelled Atom-cycles at size zero is zero. -/
theorem labelCycCount_Atom_egf_coeff_zero :
    PowerSeries.coeff 0
        (PowerSeries.mk fun n => (labelCycCount Atom n : ℚ) / n.factorial) = 0 := by
  simp [CombinatorialClass.labelCycCount]

/-- The EGF coefficient of labelled Atom-cycles at every positive size is `1 / n`. -/
theorem labelCycCount_Atom_egf_coeff_pos (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n
        (PowerSeries.mk fun n => (labelCycCount Atom n : ℚ) / n.factorial) =
      1 / (n : ℚ) := by
  rw [PowerSeries.coeff_mk]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [labelCycCount_Atom_succ]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Coefficient form of the EGF for labelled Atom-cycles.  This is the formal
    series whose analytic notation is `∑_{n ≥ 1} X^n / n`. -/
theorem labelCycCount_Atom_egf_coeff (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.mk fun n => (labelCycCount Atom n : ℚ) / n.factorial) =
      if n = 0 then 0 else 1 / (n : ℚ) := by
  by_cases hn : n = 0
  · simpa [hn] using labelCycCount_Atom_egf_coeff_zero
  · simp [hn, labelCycCount_Atom_egf_coeff_pos n (Nat.pos_iff_ne_zero.mpr hn)]

/-- The labelled Atom-cycle EGF as an explicit formal power series.  Mathlib in
    this checkout does not provide `PowerSeries.log`, so the logarithmic
    identification `-log (1 - X)` is left as an API-level TODO. -/
theorem labelCycCount_Atom_egf_coeffs :
    (PowerSeries.mk fun n => (labelCycCount Atom n : ℚ) / n.factorial) =
      PowerSeries.mk fun n => if n = 0 then 0 else 1 / (n : ℚ) := by
  ext n
  rw [labelCycCount_Atom_egf_coeff, PowerSeries.coeff_mk]
