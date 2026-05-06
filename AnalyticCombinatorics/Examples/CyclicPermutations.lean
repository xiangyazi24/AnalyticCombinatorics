import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cyclic permutation examples.

This file keeps the labelled cycle examples self-contained: a positive cycle
count is represented by `(n - 1)!`, while the zero-size count is `0`.
-/

namespace AnalyticCombinatorics.Examples.CyclicPermutations

/-- A cyclic permutation of `Fin n` is a permutation with one cycle. -/
def IsCyclicPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x y : Fin n, σ.SameCycle x y

/-- The subtype of cyclic permutations on `Fin n`. -/
def CyclicPermutation (n : ℕ) : Type :=
  { σ : Equiv.Perm (Fin n) // IsCyclicPermutation σ }

/-- Labelled cycle count for an atom class: zero at size `0`,
and `(n - 1)!` at positive size. -/
def labelledCycleCount : ℕ → ℚ
  | 0 => 0
  | n + 1 => (n.factorial : ℚ)

@[simp]
theorem labelledCycleCount_zero : labelledCycleCount 0 = 0 := rfl

@[simp]
theorem labelledCycleCount_succ (n : ℕ) :
    labelledCycleCount (n + 1) = (n.factorial : ℚ) := rfl

/-- The empty permutation on `Fin 0` satisfies the one-cycle convention by
eliminating the impossible point. -/
example (σ : Equiv.Perm (Fin 0)) : IsCyclicPermutation σ := by
  intro x
  exact Fin.elim0 x

/-- The unique permutation on `Fin 1` is a one-cycle. -/
example (σ : Equiv.Perm (Fin 1)) : IsCyclicPermutation σ := by
  intro x y
  exact (Subsingleton.elim x y).sameCycle σ

example : labelledCycleCount 1 = 1 := by native_decide
example : labelledCycleCount 2 = 1 := by native_decide
example : labelledCycleCount 3 = 2 := by native_decide
example : labelledCycleCount 4 = 6 := by native_decide
example : labelledCycleCount 5 = 24 := by native_decide
example : labelledCycleCount 6 = 120 := by native_decide
example : labelledCycleCount 7 = 720 := by native_decide
example : labelledCycleCount 8 = 5040 := by native_decide
example : labelledCycleCount 9 = 40320 := by native_decide
example : labelledCycleCount 10 = 362880 := by native_decide

/-- Positive labelled cycle EGF coefficients are `1 / n`. -/
theorem labelledCycleEgfCoeff_pos (n : ℕ) :
    labelledCycleCount (n + 1) / ((n + 1).factorial : ℚ) =
      1 / ((n + 1 : ℕ) : ℚ) := by
  rw [labelledCycleCount_succ, Nat.factorial_succ]
  norm_num
  field_simp

/-- Coefficient stream form of the labelled cycle EGF. -/
def labelledCycleEgfCoeff (n : ℕ) : ℚ :=
  labelledCycleCount n / (n.factorial : ℚ)

example : labelledCycleEgfCoeff 0 = 0 := by native_decide
example : labelledCycleEgfCoeff 1 = 1 := by native_decide
example : labelledCycleEgfCoeff 2 = 1 / 2 := by native_decide
example : labelledCycleEgfCoeff 3 = 1 / 3 := by native_decide
example : labelledCycleEgfCoeff 4 = 1 / 4 := by native_decide
example : labelledCycleEgfCoeff 5 = 1 / 5 := by native_decide

structure CyclicPermutationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CyclicPermutationsBudgetCertificate.controlled
    (c : CyclicPermutationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CyclicPermutationsBudgetCertificate.budgetControlled
    (c : CyclicPermutationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CyclicPermutationsBudgetCertificate.Ready
    (c : CyclicPermutationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CyclicPermutationsBudgetCertificate.size
    (c : CyclicPermutationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem cyclicPermutations_budgetCertificate_le_size
    (c : CyclicPermutationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCyclicPermutationsBudgetCertificate :
    CyclicPermutationsBudgetCertificate :=
  { primaryWindow := 4
    secondaryWindow := 5
    certificateBudgetWindow := 10
    slack := 1 }

example : sampleCyclicPermutationsBudgetCertificate.Ready := by
  constructor
  · norm_num [CyclicPermutationsBudgetCertificate.controlled,
      sampleCyclicPermutationsBudgetCertificate]
  · norm_num [CyclicPermutationsBudgetCertificate.budgetControlled,
      sampleCyclicPermutationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCyclicPermutationsBudgetCertificate.Ready := by
  constructor
  · norm_num [CyclicPermutationsBudgetCertificate.controlled,
      sampleCyclicPermutationsBudgetCertificate]
  · norm_num [CyclicPermutationsBudgetCertificate.budgetControlled,
      sampleCyclicPermutationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCyclicPermutationsBudgetCertificate.certificateBudgetWindow ≤
      sampleCyclicPermutationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CyclicPermutationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCyclicPermutationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCyclicPermutationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.Examples.CyclicPermutations
