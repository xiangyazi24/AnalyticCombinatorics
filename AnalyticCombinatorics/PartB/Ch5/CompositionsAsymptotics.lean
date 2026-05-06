/-
  Analytic Combinatorics — Part B
  Chapter V — Applications of Rational Generating Functions

  Executable coefficient checks for integer compositions.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch5.CompositionsAsymptotics

open Finset

/-! ## Ordinary compositions -/

/-- Number of compositions of `n` into positive parts, with the empty
composition counted at `n = 0`. -/
def compositionCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ n

theorem compositionCount_zero : compositionCount 0 = 1 := rfl

theorem compositionCount_succ (n : ℕ) : compositionCount (n + 1) = 2 ^ n := rfl

/-- Executable check of the first values `1, 1, 2, 4, ..., 512`. -/
theorem compositionCount_values_0_to_10 :
    [compositionCount 0, compositionCount 1, compositionCount 2,
      compositionCount 3, compositionCount 4, compositionCount 5,
      compositionCount 6, compositionCount 7, compositionCount 8,
      compositionCount 9, compositionCount 10]
      = [1, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512] := by
  native_decide

/-! ## Restricted parts -/

/-- Number of compositions of `n` whose positive parts all lie in `S`. -/
def restrictedCompCount (S : Finset ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ p ∈ S, if hp : 1 ≤ p ∧ p ≤ n + 1 then
        restrictedCompCount S (n + 1 - p)
      else
        0
termination_by n => n
decreasing_by omega

private abbrev oneTwo : Finset ℕ := {1, 2}

theorem restrictedCompCount_oneTwo_values_0_to_10 :
    [restrictedCompCount oneTwo 0, restrictedCompCount oneTwo 1,
      restrictedCompCount oneTwo 2, restrictedCompCount oneTwo 3,
      restrictedCompCount oneTwo 4, restrictedCompCount oneTwo 5,
      restrictedCompCount oneTwo 6, restrictedCompCount oneTwo 7,
      restrictedCompCount oneTwo 8, restrictedCompCount oneTwo 9,
      restrictedCompCount oneTwo 10]
      = [Nat.fib 1, Nat.fib 2, Nat.fib 3, Nat.fib 4, Nat.fib 5,
        Nat.fib 6, Nat.fib 7, Nat.fib 8, Nat.fib 9, Nat.fib 10,
        Nat.fib 11] := by
  native_decide

theorem restrictedCompCount_oneTwo_eq_fib_upto_10 :
    (List.range 11).all (fun n => restrictedCompCount oneTwo n == Nat.fib (n + 1))
      = true := by
  native_decide

/-! ## Number of parts -/

/-- Total number of parts over all compositions of `n`.

For `n ≥ 1`, the separator model gives
`totalParts n = 2^(n-1) + (n-1) * 2^(n-2) = (n+1) * 2^(n-2)`.
-/
def totalParts : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 3) * 2 ^ n

theorem totalParts_values_0_to_8 :
    [totalParts 0, totalParts 1, totalParts 2, totalParts 3, totalParts 4,
      totalParts 5, totalParts 6, totalParts 7, totalParts 8]
      = [0, 1, 3, 8, 20, 48, 112, 256, 576] := by
  native_decide

/-- Multiplied integer form of the average number of parts:
`total / count = (n+1)/2`, for `n = 1, ..., 8`. -/
theorem totalParts_twice_eq_average_formula_1_to_8 :
    (List.range 8).all
      (fun k =>
        let n := k + 1
        totalParts n * 2 == (n + 1) * 2 ^ (n - 1))
      = true := by
  native_decide

/-- The exponent `2^n` sometimes written in this identity is off by one:
it already fails at `n = 1`. -/
theorem totalParts_requested_formula_fails_at_one :
    ¬ totalParts 1 * 2 = (1 + 1) * 2 ^ 1 := by
  native_decide

/-! ## Growth rate -/

theorem compositionCount_pos (n : ℕ) : 0 < compositionCount n := by
  cases n with
  | zero => native_decide
  | succ n =>
      rw [compositionCount_succ]
      exact pow_pos (by decide : 0 < (2 : ℕ)) n

theorem compositionCount_lt_pow_two (n : ℕ) (hn : 1 ≤ n) :
    compositionCount n < 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [compositionCount_succ, pow_succ]
  have hpos : 0 < 2 ^ k := pow_pos (by decide : 0 < (2 : ℕ)) k
  calc
    2 ^ k < 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right hpos
    _ = 2 ^ k * 2 := by rw [Nat.mul_two]

theorem compositionCount_growth_values_1_to_10 :
    (List.range 10).all
      (fun k =>
        let n := k + 1
        compositionCount n < 2 ^ n)
      = true := by
  native_decide

theorem compositionCount_positive_values_0_to_10 :
    (List.range 11).all (fun n => 0 < compositionCount n) = true := by
  native_decide


structure CompositionsAsymptoticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CompositionsAsymptoticsBudgetCertificate.controlled
    (c : CompositionsAsymptoticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def CompositionsAsymptoticsBudgetCertificate.budgetControlled
    (c : CompositionsAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def CompositionsAsymptoticsBudgetCertificate.Ready
    (c : CompositionsAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CompositionsAsymptoticsBudgetCertificate.size
    (c : CompositionsAsymptoticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem compositionsAsymptotics_budgetCertificate_le_size
    (c : CompositionsAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCompositionsAsymptoticsBudgetCertificate :
    CompositionsAsymptoticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleCompositionsAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsAsymptoticsBudgetCertificate.controlled,
      sampleCompositionsAsymptoticsBudgetCertificate]
  · norm_num [CompositionsAsymptoticsBudgetCertificate.budgetControlled,
      sampleCompositionsAsymptoticsBudgetCertificate]

example :
    sampleCompositionsAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositionsAsymptoticsBudgetCertificate.size := by
  apply compositionsAsymptotics_budgetCertificate_le_size
  constructor
  · norm_num [CompositionsAsymptoticsBudgetCertificate.controlled,
      sampleCompositionsAsymptoticsBudgetCertificate]
  · norm_num [CompositionsAsymptoticsBudgetCertificate.budgetControlled,
      sampleCompositionsAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCompositionsAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [CompositionsAsymptoticsBudgetCertificate.controlled,
      sampleCompositionsAsymptoticsBudgetCertificate]
  · norm_num [CompositionsAsymptoticsBudgetCertificate.budgetControlled,
      sampleCompositionsAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCompositionsAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      sampleCompositionsAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List CompositionsAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCompositionsAsymptoticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleCompositionsAsymptoticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.CompositionsAsymptotics
