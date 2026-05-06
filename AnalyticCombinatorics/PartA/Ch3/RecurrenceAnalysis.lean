import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch3.RecurrenceAnalysis


open Finset Nat

/-!
# Recurrence relation analysis

Finite, executable checks for standard recurrences from the analysis of
algorithms.  The statements are intentionally bounded, so that every proof is
closed by `native_decide`.
-/

/-! ## 1. Divide-and-conquer: `T(n) = 2*T(n/2) + n` -/

/-- Values of `T(2^k)` for `T(1) = 0` and `T(n) = 2*T(n/2) + n`. -/
def divideConquerTable : Fin 8 -> Nat :=
  ![0, 2, 8, 24, 64, 160, 384, 896]

/-- At powers of two, this table satisfies `T(2^k) = 2^k * k`. -/
theorem divideConquer_closed_form :
    forall k : Fin 8, divideConquerTable k = 2 ^ k.val * k.val := by
  native_decide

/-- The recurrence step `T(2^(k+1)) = 2*T(2^k) + 2^(k+1)`. -/
theorem divideConquer_recurrence :
    divideConquerTable 1 = 2 * divideConquerTable 0 + 2 ^ 1
      ∧ divideConquerTable 2 = 2 * divideConquerTable 1 + 2 ^ 2
      ∧ divideConquerTable 3 = 2 * divideConquerTable 2 + 2 ^ 3
      ∧ divideConquerTable 4 = 2 * divideConquerTable 3 + 2 ^ 4
      ∧ divideConquerTable 5 = 2 * divideConquerTable 4 + 2 ^ 5
      ∧ divideConquerTable 6 = 2 * divideConquerTable 5 + 2 ^ 6
      ∧ divideConquerTable 7 = 2 * divideConquerTable 6 + 2 ^ 7 := by
  native_decide

/-! ## 2. Master theorem cases at powers of two -/

/-- Case `a < b^d`: `T(n) = T(n/2) + n`, with `T(1) = 1`. -/
def masterCaseSmallTable : Fin 6 -> Nat :=
  ![1, 3, 7, 15, 31, 63]

/-- Closed form `T(2^k) = 2^(k+1) - 1`. -/
theorem masterCaseSmall_closed_form :
    forall k : Fin 6, masterCaseSmallTable k = 2 ^ (k.val + 1) - 1 := by
  native_decide

/-- Recurrence check for `T(n) = T(n/2) + n`. -/
theorem masterCaseSmall_recurrence :
    masterCaseSmallTable 1 = masterCaseSmallTable 0 + 2 ^ 1
      ∧ masterCaseSmallTable 2 = masterCaseSmallTable 1 + 2 ^ 2
      ∧ masterCaseSmallTable 3 = masterCaseSmallTable 2 + 2 ^ 3
      ∧ masterCaseSmallTable 4 = masterCaseSmallTable 3 + 2 ^ 4
      ∧ masterCaseSmallTable 5 = masterCaseSmallTable 4 + 2 ^ 5 := by
  native_decide

/-- Balanced case `a = b^d`: `T(n) = 2*T(n/2) + n`, with `T(1) = 1`. -/
def masterCaseBalancedTable : Fin 6 -> Nat :=
  ![1, 4, 12, 32, 80, 192]

/-- Closed form `T(2^k) = (k+1)*2^k`. -/
theorem masterCaseBalanced_closed_form :
    forall k : Fin 6, masterCaseBalancedTable k = (k.val + 1) * 2 ^ k.val := by
  native_decide

/-- Recurrence check for `T(n) = 2*T(n/2) + n`. -/
theorem masterCaseBalanced_recurrence :
    masterCaseBalancedTable 1 = 2 * masterCaseBalancedTable 0 + 2 ^ 1
      ∧ masterCaseBalancedTable 2 = 2 * masterCaseBalancedTable 1 + 2 ^ 2
      ∧ masterCaseBalancedTable 3 = 2 * masterCaseBalancedTable 2 + 2 ^ 3
      ∧ masterCaseBalancedTable 4 = 2 * masterCaseBalancedTable 3 + 2 ^ 4
      ∧ masterCaseBalancedTable 5 = 2 * masterCaseBalancedTable 4 + 2 ^ 5 := by
  native_decide

/-- Case `a > b^d`: `T(n) = 4*T(n/2) + n`, with `T(1) = 1`. -/
def masterCaseLargeTable : Fin 6 -> Nat :=
  ![1, 6, 28, 120, 496, 2016]

/-- Closed form `T(2^k) = 2*4^k - 2^k`. -/
theorem masterCaseLarge_closed_form :
    forall k : Fin 6, masterCaseLargeTable k = 2 * 4 ^ k.val - 2 ^ k.val := by
  native_decide

/-- Recurrence check for `T(n) = 4*T(n/2) + n`. -/
theorem masterCaseLarge_recurrence :
    masterCaseLargeTable 1 = 4 * masterCaseLargeTable 0 + 2 ^ 1
      ∧ masterCaseLargeTable 2 = 4 * masterCaseLargeTable 1 + 2 ^ 2
      ∧ masterCaseLargeTable 3 = 4 * masterCaseLargeTable 2 + 2 ^ 3
      ∧ masterCaseLargeTable 4 = 4 * masterCaseLargeTable 3 + 2 ^ 4
      ∧ masterCaseLargeTable 5 = 4 * masterCaseLargeTable 4 + 2 ^ 5 := by
  native_decide

/-! ## 3. Akra-Bazzi style recurrence: `T(n) = a*T(n/b) + f(n)` -/

/-- Values of `T(3^k)` for `T(1)=1` and `T(n) = 2*T(n/3) + n`. -/
def akraBazziTable : Fin 6 -> Nat :=
  ![1, 5, 19, 65, 211, 665]

/-- Closed form for the checked instance: `T(3^k) = 3^(k+1) - 2^(k+1)`. -/
theorem akraBazzi_closed_form :
    forall k : Fin 6, akraBazziTable k = 3 ^ (k.val + 1) - 2 ^ (k.val + 1) := by
  native_decide

/-- Recurrence check for `T(n) = 2*T(n/3) + n` on powers of three. -/
theorem akraBazzi_recurrence :
    akraBazziTable 1 = 2 * akraBazziTable 0 + 3 ^ 1
      ∧ akraBazziTable 2 = 2 * akraBazziTable 1 + 3 ^ 2
      ∧ akraBazziTable 3 = 2 * akraBazziTable 2 + 3 ^ 3
      ∧ akraBazziTable 4 = 2 * akraBazziTable 3 + 3 ^ 4
      ∧ akraBazziTable 5 = 2 * akraBazziTable 4 + 3 ^ 5 := by
  native_decide

/-! ## 4. Full-history recurrence -/

/-- `T(0)=1`, and for `n >= 1`, `T(n)=2^(n-1)`. -/
def fullHistory (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | m + 1 => 2 ^ m

/-- For `1 <= n <= 8`, `T(n) = 2^(n-1)`. -/
theorem fullHistory_closed_form :
    forall n : Fin 8, fullHistory (n.val + 1) = 2 ^ n.val := by
  native_decide

/-- For `1 <= n <= 8`, `T(n) = sum_{k<n} T(k)`. -/
theorem fullHistory_recurrence :
    forall n : Fin 8,
      fullHistory (n.val + 1) = (range (n.val + 1)).sum fullHistory := by
  native_decide

/-! ## 5. Quicksort recurrence structure -/

/-- `n! * H_n`, represented with natural arithmetic as `sum_{k=1}^n n!/k`. -/
def harmonicScaled (n : Nat) : Nat :=
  (range n).sum fun k => factorial n / (k + 1)

/-- `n!` times the expected quicksort comparison count. -/
def quicksortScaledFormula (n : Nat) : Nat :=
  2 * (n + 1) * harmonicScaled n - 4 * n * factorial n

/-- Values of `n! * (2*(n+1)*H_n - 4*n)` for `n = 0..7`. -/
def quicksortScaledTable : Fin 8 -> Nat :=
  ![0, 0, 2, 16, 116, 888, 7416, 67968]

/-- Small-`n` verification of `C(n) = 2*(n+1)*H_n - 4*n`, scaled by `n!`. -/
theorem quicksort_closed_form_small :
    forall n : Fin 8, quicksortScaledTable n = quicksortScaledFormula n.val := by
  native_decide

/-- The scaled table starts with the standard expected comparison values. -/
theorem quicksort_initial_values :
    quicksortScaledTable 0 = 0
      ∧ quicksortScaledTable 1 = 0
      ∧ quicksortScaledTable 2 = 2
      ∧ quicksortScaledTable 3 = 16
      ∧ quicksortScaledTable 4 = 116 := by
  native_decide

/-! ## 6. Towers of Hanoi -/

/-- Closed form for the number of moves in the Towers of Hanoi puzzle. -/
def hanoi (n : Nat) : Nat :=
  2 ^ n - 1

/-- `T(n) = 2^n - 1` for the checked range. -/
theorem hanoi_closed_form :
    forall n : Fin 10, hanoi n.val = 2 ^ n.val - 1 := by
  native_decide

/-- Recurrence `T(n+1) = 2*T(n) + 1`. -/
theorem hanoi_recurrence :
    forall n : Fin 9, hanoi (n.val + 1) = 2 * hanoi n.val + 1 := by
  native_decide



structure RecurrenceAnalysisBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RecurrenceAnalysisBudgetCertificate.controlled
    (c : RecurrenceAnalysisBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RecurrenceAnalysisBudgetCertificate.budgetControlled
    (c : RecurrenceAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RecurrenceAnalysisBudgetCertificate.Ready
    (c : RecurrenceAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RecurrenceAnalysisBudgetCertificate.size
    (c : RecurrenceAnalysisBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem recurrenceAnalysis_budgetCertificate_le_size
    (c : RecurrenceAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRecurrenceAnalysisBudgetCertificate :
    RecurrenceAnalysisBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRecurrenceAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [RecurrenceAnalysisBudgetCertificate.controlled,
      sampleRecurrenceAnalysisBudgetCertificate]
  · norm_num [RecurrenceAnalysisBudgetCertificate.budgetControlled,
      sampleRecurrenceAnalysisBudgetCertificate]

example :
    sampleRecurrenceAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleRecurrenceAnalysisBudgetCertificate.size := by
  apply recurrenceAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [RecurrenceAnalysisBudgetCertificate.controlled,
      sampleRecurrenceAnalysisBudgetCertificate]
  · norm_num [RecurrenceAnalysisBudgetCertificate.budgetControlled,
      sampleRecurrenceAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRecurrenceAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [RecurrenceAnalysisBudgetCertificate.controlled,
      sampleRecurrenceAnalysisBudgetCertificate]
  · norm_num [RecurrenceAnalysisBudgetCertificate.budgetControlled,
      sampleRecurrenceAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRecurrenceAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleRecurrenceAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RecurrenceAnalysisBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRecurrenceAnalysisBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRecurrenceAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.RecurrenceAnalysis
