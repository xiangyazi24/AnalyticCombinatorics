import Mathlib.Tactic
set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch4.RationalGFApplications


/-!
Bounded executable tables for applications of rational generating functions
from Chapter IV of Flajolet--Sedgewick.
-/

def lookup12 (a : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  if h : n < 12 then a ⟨n, h⟩ else 0

def lookup15 (a : Fin 15 → ℕ) (n : ℕ) : ℕ :=
  if h : n < 15 then a ⟨n, h⟩ else 0

def orderTwoRecurrenceCheck (a : Fin 15 → ℕ) (c : Fin 2 → ℕ) : Bool :=
  (List.range 13).all fun n =>
    lookup15 a (n + 2) == c 0 * lookup15 a (n + 1) + c 1 * lookup15 a n

abbrev orderTwoRecurrenceHolds (a : Fin 15 → ℕ) (c : Fin 2 → ℕ) : Prop :=
  orderTwoRecurrenceCheck a c = true

def orderThreeRecurrenceCheck (a : Fin 15 → ℕ) (c : Fin 3 → ℕ) : Bool :=
  (List.range 12).all fun n =>
    lookup15 a (n + 3) ==
      c 0 * lookup15 a (n + 2) +
      c 1 * lookup15 a (n + 1) +
      c 2 * lookup15 a n

abbrev orderThreeRecurrenceHolds (a : Fin 15 → ℕ) (c : Fin 3 → ℕ) : Prop :=
  orderThreeRecurrenceCheck a c = true

/-! ## Positive compositions -/

/-- Counts of compositions of `n + 1`, namely `2^n`, for `0 <= n < 12`. -/
def positiveCompositionTable : Fin 12 → ℕ :=
  ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

theorem positiveCompositionTable_formula :
    ∀ n ∈ List.range 12, lookup12 positiveCompositionTable n = 2 ^ n := by
  native_decide

/-! ## Restricted compositions -/

/-- Compositions of `n` with parts in `{1, 2}` for `0 <= n < 15`. -/
def restrictedComposition12Table : Fin 15 → ℕ :=
  ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]

/-- Compositions of `n` with parts in `{1, 2, 3}` for `0 <= n < 15`. -/
def restrictedComposition123Table : Fin 15 → ℕ :=
  ![1, 1, 2, 4, 7, 13, 24, 44, 81, 149, 274, 504, 927, 1705, 3136]

def fibonacciCoefficients : Fin 2 → ℕ :=
  ![1, 1]

def tribonacciCoefficients : Fin 3 → ℕ :=
  ![1, 1, 1]

theorem restrictedComposition12_fibonacci_recurrence :
    orderTwoRecurrenceHolds restrictedComposition12Table fibonacciCoefficients := by
  native_decide

theorem restrictedComposition123_tribonacci_recurrence :
    orderThreeRecurrenceHolds restrictedComposition123Table tribonacciCoefficients := by
  native_decide

/-! ## Domino tilings of a `2 x n` rectangle -/

/-- Domino tilings of the `2 x n` rectangle, equal to `F_{n+1}`. -/
def dominoTilingTable : Fin 15 → ℕ :=
  ![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610]

theorem dominoTilingTable_fibonacci_shift :
    ∀ n ∈ List.range 15, lookup15 dominoTilingTable n = Nat.fib (n + 1) := by
  native_decide

theorem dominoTilingTable_order_two_recurrence :
    orderTwoRecurrenceHolds dominoTilingTable fibonacciCoefficients := by
  native_decide

/-! ## Binary words avoiding a forbidden pattern -/

/-- Binary words of length `n` with no adjacent `1`s. -/
def noAdjacentOnesWordTable : Fin 15 → ℕ :=
  ![1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987]

theorem noAdjacentOnesWordTable_recurrence :
    orderTwoRecurrenceHolds noAdjacentOnesWordTable fibonacciCoefficients := by
  native_decide

theorem noAdjacentOnesWordTable_tiling_shift :
    ∀ n ∈ List.range 14,
      lookup15 noAdjacentOnesWordTable n = lookup15 dominoTilingTable (n + 1) := by
  native_decide

/-! ## Transfer-matrix traces -/

/--
Traces of powers of the Fibonacci transfer matrix
`[[1, 1], [1, 0]]`, i.e. Lucas numbers `L_n`.
-/
def fibonacciTransferTraceTable : Fin 15 → ℕ :=
  ![2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, 199, 322, 521, 843]

theorem fibonacciTransferTraceTable_characteristic_recurrence :
    orderTwoRecurrenceHolds fibonacciTransferTraceTable fibonacciCoefficients := by
  native_decide

theorem fibonacciTransferTraceTable_fibonacci_consequence :
    ∀ n ∈ List.range 13,
      lookup15 fibonacciTransferTraceTable (n + 2) =
        lookup15 dominoTilingTable (n + 2) + lookup15 dominoTilingTable n := by
  native_decide



structure RationalGFApplicationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RationalGFApplicationsBudgetCertificate.controlled
    (c : RationalGFApplicationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RationalGFApplicationsBudgetCertificate.budgetControlled
    (c : RationalGFApplicationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RationalGFApplicationsBudgetCertificate.Ready
    (c : RationalGFApplicationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RationalGFApplicationsBudgetCertificate.size
    (c : RationalGFApplicationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem rationalGFApplications_budgetCertificate_le_size
    (c : RationalGFApplicationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRationalGFApplicationsBudgetCertificate :
    RationalGFApplicationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRationalGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalGFApplicationsBudgetCertificate.controlled,
      sampleRationalGFApplicationsBudgetCertificate]
  · norm_num [RationalGFApplicationsBudgetCertificate.budgetControlled,
      sampleRationalGFApplicationsBudgetCertificate]

example :
    sampleRationalGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRationalGFApplicationsBudgetCertificate.size := by
  apply rationalGFApplications_budgetCertificate_le_size
  constructor
  · norm_num [RationalGFApplicationsBudgetCertificate.controlled,
      sampleRationalGFApplicationsBudgetCertificate]
  · norm_num [RationalGFApplicationsBudgetCertificate.budgetControlled,
      sampleRationalGFApplicationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRationalGFApplicationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalGFApplicationsBudgetCertificate.controlled,
      sampleRationalGFApplicationsBudgetCertificate]
  · norm_num [RationalGFApplicationsBudgetCertificate.budgetControlled,
      sampleRationalGFApplicationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRationalGFApplicationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRationalGFApplicationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RationalGFApplicationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRationalGFApplicationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRationalGFApplicationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.RationalGFApplications
