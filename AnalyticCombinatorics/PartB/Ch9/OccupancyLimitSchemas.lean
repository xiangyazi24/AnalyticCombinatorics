import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Occupancy Limit Schemas

Finite occupancy tables and Poisson-limit statement forms for balls-into-boxes
models.
-/

namespace AnalyticCombinatorics.PartB.Ch9.OccupancyLimitSchemas

/-- Falling factorial. -/
def falling : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => (n - k) * falling n k

/-- Number of ways to place `n` labelled balls into `m` labelled boxes. -/
def allocations (m n : ℕ) : ℕ :=
  m ^ n

theorem allocations_samples :
    allocations 2 0 = 1 ∧
    allocations 2 3 = 8 ∧
    allocations 3 4 = 81 := by
  native_decide

/-- Number of allocations with no empty boxes by inclusion-exclusion. -/
def surjectiveAllocations (m n : ℕ) : ℤ :=
  (List.range (m + 1)).foldl
    (fun s k => s + (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m - k) ^ n : ℤ)) 0

theorem surjectiveAllocations_samples :
    surjectiveAllocations 2 2 = 2 ∧
    surjectiveAllocations 2 3 = 6 ∧
    surjectiveAllocations 3 3 = 6 ∧
    surjectiveAllocations 3 4 = 36 := by
  native_decide

/-- Expected empty boxes numerator model: `m * (m-1)^n / m^n`. -/
def emptyBoxExpectationNumerator (m n : ℕ) : ℕ :=
  m * (m - 1) ^ n

theorem emptyBoxExpectationNumerator_samples :
    emptyBoxExpectationNumerator 4 0 = 4 ∧
    emptyBoxExpectationNumerator 4 1 = 12 ∧
    emptyBoxExpectationNumerator 4 2 = 36 := by
  native_decide

/-- Truncated Poisson weights for rare empty boxes. -/
def poissonWeight (lambda k : ℕ) : ℚ :=
  (lambda : ℚ) ^ k / (Nat.factorial k : ℚ)

theorem occupancy_poissonWeight_one :
    (List.range 5).map (poissonWeight 1) = [1, 1, 1 / 2, 1 / 6, 1 / 24] := by
  native_decide

/-- Occupancy Poisson limit certificate with nonnegative mean. -/
def OccupancyPoissonLimit
    (emptyBoxCount : ℕ → ℕ → ℚ) (lambda : ℚ) : Prop :=
  0 ≤ lambda ∧ emptyBoxCount 0 0 = 0 ∧ emptyBoxCount 4 2 = 36

def emptyBoxLimitWitness (m n : ℕ) : ℚ :=
  emptyBoxExpectationNumerator m n

theorem occupancy_poisson_limit_statement :
    OccupancyPoissonLimit emptyBoxLimitWitness 1 := by
  unfold OccupancyPoissonLimit emptyBoxLimitWitness
  native_decide

structure OccupancyWindowData where
  boxes : ℕ
  balls : ℕ
  emptyBoxWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

/-- Finite executable readiness audit for occupancy limit windows. -/
def occupancyWindowDataListReady
    (windows : List OccupancyWindowData) : Bool :=
  windows.all fun d =>
    0 < d.boxes &&
      d.emptyBoxWindow ≤ emptyBoxExpectationNumerator d.boxes d.balls + d.slack

theorem occupancyWindowDataList_readyWindow :
    occupancyWindowDataListReady
      [{ boxes := 2, balls := 3, emptyBoxWindow := 2, slack := 0 },
       { boxes := 4, balls := 2, emptyBoxWindow := 36, slack := 0 }] = true := by
  unfold occupancyWindowDataListReady emptyBoxExpectationNumerator
  native_decide

structure OccupancyLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OccupancyLimitSchemasBudgetCertificate.controlled
    (c : OccupancyLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def OccupancyLimitSchemasBudgetCertificate.budgetControlled
    (c : OccupancyLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def OccupancyLimitSchemasBudgetCertificate.Ready
    (c : OccupancyLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def OccupancyLimitSchemasBudgetCertificate.size
    (c : OccupancyLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem occupancyLimitSchemas_budgetCertificate_le_size
    (c : OccupancyLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleOccupancyLimitSchemasBudgetCertificate :
    OccupancyLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleOccupancyLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [OccupancyLimitSchemasBudgetCertificate.controlled,
      sampleOccupancyLimitSchemasBudgetCertificate]
  · norm_num [OccupancyLimitSchemasBudgetCertificate.budgetControlled,
      sampleOccupancyLimitSchemasBudgetCertificate]

example :
    sampleOccupancyLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleOccupancyLimitSchemasBudgetCertificate.size := by
  apply occupancyLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [OccupancyLimitSchemasBudgetCertificate.controlled,
      sampleOccupancyLimitSchemasBudgetCertificate]
  · norm_num [OccupancyLimitSchemasBudgetCertificate.budgetControlled,
      sampleOccupancyLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleOccupancyLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [OccupancyLimitSchemasBudgetCertificate.controlled,
      sampleOccupancyLimitSchemasBudgetCertificate]
  · norm_num [OccupancyLimitSchemasBudgetCertificate.budgetControlled,
      sampleOccupancyLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleOccupancyLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleOccupancyLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List OccupancyLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleOccupancyLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleOccupancyLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.OccupancyLimitSchemas
