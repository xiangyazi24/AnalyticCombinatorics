import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.SurjectionsStirling


/-! ## Total functions -/

/-- Number of total functions `[n] → [k]`. -/
def totalFunctions (n k : ℕ) : ℕ := k ^ n

/-- Values of `k^n` for the listed total-function checks. -/
def totalFunctionTable : Fin 5 → ℕ := ![8, 27, 81, 256, 125]

theorem totalFunctions_values :
    totalFunctions 3 2 = totalFunctionTable 0 ∧
    totalFunctions 3 3 = totalFunctionTable 1 ∧
    totalFunctions 4 3 = totalFunctionTable 2 ∧
    totalFunctions 4 4 = totalFunctionTable 3 ∧
    totalFunctions 3 5 = totalFunctionTable 4 := by
  native_decide

example : 2 ^ 3 = 8 := by native_decide
example : 3 ^ 3 = 27 := by native_decide
example : 3 ^ 4 = 81 := by native_decide
example : 4 ^ 4 = 256 := by native_decide
example : 5 ^ 3 = 125 := by native_decide

/-! ## Surjections and Stirling numbers of the second kind -/

/-- Stirling numbers of the second kind. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Number of surjections `[n] → [k]`: `k! * Stirling2(n,k)`. -/
def surjectionCount (n k : ℕ) : ℕ := Nat.factorial k * stirling2 n k

/-- Values of `S(n,k)` for the listed surjection checks. -/
def surjectionTable : Fin 9 → ℕ := ![6, 6, 14, 36, 24, 30, 150, 240, 120]

theorem surjection_values :
    surjectionCount 3 2 = surjectionTable 0 ∧
    surjectionCount 3 3 = surjectionTable 1 ∧
    surjectionCount 4 2 = surjectionTable 2 ∧
    surjectionCount 4 3 = surjectionTable 3 ∧
    surjectionCount 4 4 = surjectionTable 4 ∧
    surjectionCount 5 2 = surjectionTable 5 ∧
    surjectionCount 5 3 = surjectionTable 6 ∧
    surjectionCount 5 4 = surjectionTable 7 ∧
    surjectionCount 5 5 = surjectionTable 8 := by
  native_decide

/-- Inclusion-exclusion formula for the number of surjections `[n] → [k]`. -/
def surjectionIE (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ j * (Nat.choose k j : ℤ) * (((k - j) ^ n : ℕ) : ℤ)

theorem surjection_ie_3_2 :
    surjectionIE 3 2 = (surjectionCount 3 2 : ℤ) := by
  native_decide

theorem surjection_ie_4_3 :
    surjectionIE 4 3 = (surjectionCount 4 3 : ℤ) := by
  native_decide

/-! ## Falling factorials -/

/-- Falling factorial `P(n,k) = n! / (n-k)!`. -/
def fallingFactorial (n k : ℕ) : ℕ := Nat.factorial n / Nat.factorial (n - k)

/-- Values of `P(n,k)` for the listed checks. -/
def fallingFactorialTable : Fin 5 → ℕ := ![20, 60, 120, 42, 720]

theorem fallingFactorial_values :
    fallingFactorial 5 2 = fallingFactorialTable 0 ∧
    fallingFactorial 5 3 = fallingFactorialTable 1 ∧
    fallingFactorial 6 3 = fallingFactorialTable 2 ∧
    fallingFactorial 7 2 = fallingFactorialTable 3 ∧
    fallingFactorial 10 3 = fallingFactorialTable 4 := by
  native_decide

/-! ## Factorials -/

/-- Factorials `1!` through `8!`. -/
def factorialTable : Fin 8 → ℕ := ![1, 2, 6, 24, 120, 720, 5040, 40320]

theorem factorial_values_1_to_8 :
    Nat.factorial 1 = factorialTable 0 ∧
    Nat.factorial 2 = factorialTable 1 ∧
    Nat.factorial 3 = factorialTable 2 ∧
    Nat.factorial 4 = factorialTable 3 ∧
    Nat.factorial 5 = factorialTable 4 ∧
    Nat.factorial 6 = factorialTable 5 ∧
    Nat.factorial 7 = factorialTable 6 ∧
    Nat.factorial 8 = factorialTable 7 := by
  native_decide

/-! ## Stars and bars -/

/-- Weak compositions of `n` into `k` parts: `C(n+k-1,k-1)`. -/
def starsAndBars (n k : ℕ) : ℕ := Nat.choose (n + k - 1) (k - 1)

/-- Values of `C(n+k-1,k-1)` for the listed stars-and-bars checks. -/
def starsAndBarsTable : Fin 3 → ℕ := ![10, 15, 21]

theorem starsAndBars_values :
    starsAndBars 3 3 = starsAndBarsTable 0 ∧
    starsAndBars 4 3 = starsAndBarsTable 1 ∧
    starsAndBars 5 3 = starsAndBarsTable 2 := by
  native_decide

/-! ## Compositions -/

/-- Compositions of `n` into `k` positive parts: `C(n-1,k-1)`. -/
def compositions (n k : ℕ) : ℕ := Nat.choose (n - 1) (k - 1)

/-- Values of `C(n-1,k-1)` for the listed composition checks. -/
def compositionTable : Fin 3 → ℕ := ![6, 10, 20]

theorem composition_values :
    compositions 5 3 = compositionTable 0 ∧
    compositions 6 3 = compositionTable 1 ∧
    compositions 7 4 = compositionTable 2 := by
  native_decide



structure SurjectionsStirlingBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SurjectionsStirlingBudgetCertificate.controlled
    (c : SurjectionsStirlingBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def SurjectionsStirlingBudgetCertificate.budgetControlled
    (c : SurjectionsStirlingBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SurjectionsStirlingBudgetCertificate.Ready
    (c : SurjectionsStirlingBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SurjectionsStirlingBudgetCertificate.size
    (c : SurjectionsStirlingBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem surjectionsStirling_budgetCertificate_le_size
    (c : SurjectionsStirlingBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSurjectionsStirlingBudgetCertificate :
    SurjectionsStirlingBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleSurjectionsStirlingBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsStirlingBudgetCertificate.controlled,
      sampleSurjectionsStirlingBudgetCertificate]
  · norm_num [SurjectionsStirlingBudgetCertificate.budgetControlled,
      sampleSurjectionsStirlingBudgetCertificate]

example :
    sampleSurjectionsStirlingBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsStirlingBudgetCertificate.size := by
  apply surjectionsStirling_budgetCertificate_le_size
  constructor
  · norm_num [SurjectionsStirlingBudgetCertificate.controlled,
      sampleSurjectionsStirlingBudgetCertificate]
  · norm_num [SurjectionsStirlingBudgetCertificate.budgetControlled,
      sampleSurjectionsStirlingBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSurjectionsStirlingBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsStirlingBudgetCertificate.controlled,
      sampleSurjectionsStirlingBudgetCertificate]
  · norm_num [SurjectionsStirlingBudgetCertificate.budgetControlled,
      sampleSurjectionsStirlingBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSurjectionsStirlingBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsStirlingBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SurjectionsStirlingBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSurjectionsStirlingBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleSurjectionsStirlingBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.SurjectionsStirling
