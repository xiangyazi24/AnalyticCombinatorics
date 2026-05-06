import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartB.Ch6.GrowthRateClassification


/-!
Finite numerical checks for growth-rate classes suggested by singularity type.
All ranges are encoded by `Fin` tables, with proofs by computation.
-/

/-! ## 1. Polynomial growth -/

/-- Values of `n^2` for `n = 1..10`. -/
def squareTable : Fin 10 → ℕ := ![1, 4, 9, 16, 25, 36, 49, 64, 81, 100]

/-- Values of `n^3` for `n = 1..8`. -/
def cubeTable : Fin 8 → ℕ := ![1, 8, 27, 64, 125, 216, 343, 512]

example : ∀ n : Fin 10, ((n : ℕ) + 1) ^ 2 = squareTable n := by
  native_decide

example : ∀ n : Fin 8, ((n : ℕ) + 1) ^ 3 = cubeTable n := by
  native_decide

/-! ## 2. Exponential growth -/

/-- Values of `2^n` for `n = 0..10`. -/
def powTwoTable : Fin 11 → ℕ := ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

example : ∀ n : Fin 11, 2 ^ (n : ℕ) = powTwoTable n := by
  native_decide

/-! ## 3. Super-exponential growth -/

/-- Values of `n!` for `n = 0..10`. -/
def factorialTable : Fin 11 → ℕ :=
  ![1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800]

example : ∀ n : Fin 11, Nat.factorial (n : ℕ) = factorialTable n := by
  native_decide

example : ∀ n : Fin 7,
    factorialTable ⟨(n : ℕ) + 4, by omega⟩ > 2 ^ ((n : ℕ) + 4) := by
  native_decide

/-! ## 4. Sub-exponential growth -/

/-- Partition numbers `p(n)` for `n = 0..15`. -/
def partitionTable : Fin 16 → ℕ :=
  ![1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176]

example : partitionTable ⟨0, by omega⟩ = 1 := by native_decide
example : partitionTable ⟨1, by omega⟩ = 1 := by native_decide
example : partitionTable ⟨2, by omega⟩ = 2 := by native_decide
example : partitionTable ⟨3, by omega⟩ = 3 := by native_decide
example : partitionTable ⟨4, by omega⟩ = 5 := by native_decide
example : partitionTable ⟨5, by omega⟩ = 7 := by native_decide
example : partitionTable ⟨6, by omega⟩ = 11 := by native_decide
example : partitionTable ⟨7, by omega⟩ = 15 := by native_decide
example : partitionTable ⟨8, by omega⟩ = 22 := by native_decide
example : partitionTable ⟨9, by omega⟩ = 30 := by native_decide
example : partitionTable ⟨10, by omega⟩ = 42 := by native_decide
example : partitionTable ⟨11, by omega⟩ = 56 := by native_decide
example : partitionTable ⟨12, by omega⟩ = 77 := by native_decide
example : partitionTable ⟨13, by omega⟩ = 101 := by native_decide
example : partitionTable ⟨14, by omega⟩ = 135 := by native_decide
example : partitionTable ⟨15, by omega⟩ = 176 := by native_decide

example : ∀ n : Fin 12,
    partitionTable ⟨(n : ℕ) + 4, by omega⟩ < 2 ^ ((n : ℕ) + 4) := by
  native_decide

example : ∀ n : Fin 12,
    partitionTable ⟨(n : ℕ) + 4, by omega⟩ > (n : ℕ) + 4 := by
  native_decide

/-! ## 5. Algebraic-exponential growth -/

/-- Catalan number `C(n) = binom(2n,n)/(n+1)`. -/
def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

/-- Catalan numbers `C(n)` for `n = 0..10`. -/
def catalanTable : Fin 11 → ℕ :=
  ![1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796]

example : ∀ n : Fin 11, catalan (n : ℕ) = catalanTable n := by
  native_decide

example : ∀ n : Fin 10,
    catalanTable ⟨(n : ℕ) + 1, by omega⟩ < 4 ^ ((n : ℕ) + 1) := by
  native_decide

example : ∀ n : Fin 10,
    catalanTable ⟨(n : ℕ) + 1, by omega⟩ * ((n : ℕ) + 1) < 4 ^ ((n : ℕ) + 1) := by
  native_decide

/-! ## 6. Comparison chains -/

/-
For standard Catalan numbers the chain `p(n) < C(n) < 2^n < n!` is false
on `n = 5..8`; already `C(5) = 42 > 32 = 2^5`.
The verified hierarchy on this finite range is `p(n) < 2^n < C(n) < n!`.
-/
example : ∀ n : Fin 4,
    partitionTable ⟨(n : ℕ) + 5, by omega⟩
      < 2 ^ ((n : ℕ) + 5)
    ∧ 2 ^ ((n : ℕ) + 5)
      < catalanTable ⟨(n : ℕ) + 5, by omega⟩
    ∧ catalanTable ⟨(n : ℕ) + 5, by omega⟩
      < factorialTable ⟨(n : ℕ) + 5, by omega⟩ := by
  native_decide

example : ∀ n : Fin 4,
    ¬ (catalanTable ⟨(n : ℕ) + 5, by omega⟩ < 2 ^ ((n : ℕ) + 5)) := by
  native_decide

/-- Partition-number sample at fifteen. -/
theorem partitionTable_fifteen :
    partitionTable ⟨15, by omega⟩ = 176 := by
  native_decide

/-- Catalan-number table sample at ten. -/
theorem catalanTable_ten :
    catalanTable ⟨10, by omega⟩ = 16796 := by
  native_decide



structure GrowthRateClassificationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GrowthRateClassificationBudgetCertificate.controlled
    (c : GrowthRateClassificationBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GrowthRateClassificationBudgetCertificate.budgetControlled
    (c : GrowthRateClassificationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GrowthRateClassificationBudgetCertificate.Ready
    (c : GrowthRateClassificationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GrowthRateClassificationBudgetCertificate.size
    (c : GrowthRateClassificationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem growthRateClassification_budgetCertificate_le_size
    (c : GrowthRateClassificationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGrowthRateClassificationBudgetCertificate :
    GrowthRateClassificationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGrowthRateClassificationBudgetCertificate.Ready := by
  constructor
  · norm_num [GrowthRateClassificationBudgetCertificate.controlled,
      sampleGrowthRateClassificationBudgetCertificate]
  · norm_num [GrowthRateClassificationBudgetCertificate.budgetControlled,
      sampleGrowthRateClassificationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGrowthRateClassificationBudgetCertificate.certificateBudgetWindow ≤
      sampleGrowthRateClassificationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGrowthRateClassificationBudgetCertificate.Ready := by
  constructor
  · norm_num [GrowthRateClassificationBudgetCertificate.controlled,
      sampleGrowthRateClassificationBudgetCertificate]
  · norm_num [GrowthRateClassificationBudgetCertificate.budgetControlled,
      sampleGrowthRateClassificationBudgetCertificate]

example :
    sampleGrowthRateClassificationBudgetCertificate.certificateBudgetWindow ≤
      sampleGrowthRateClassificationBudgetCertificate.size := by
  apply growthRateClassification_budgetCertificate_le_size
  constructor
  · norm_num [GrowthRateClassificationBudgetCertificate.controlled,
      sampleGrowthRateClassificationBudgetCertificate]
  · norm_num [GrowthRateClassificationBudgetCertificate.budgetControlled,
      sampleGrowthRateClassificationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List GrowthRateClassificationBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGrowthRateClassificationBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGrowthRateClassificationBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.GrowthRateClassification
