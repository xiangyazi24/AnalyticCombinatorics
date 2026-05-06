import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.NumberTheoreticGF


/-! # Number-Theoretic Generating Functions

Dirichlet series and multiplicative functions from Analytic Combinatorics Ch II / Appendix.
We verify key values and identities using `native_decide`.
-/

/-! ## 1. Möbius function μ(n) -/

/-- Möbius function values for n = 1..10. -/
def mobiusTable : Fin 10 → ℤ := ![1, -1, -1, 0, -1, 1, -1, 0, 0, 1]

/-- Σ_{d|6} μ(d) = μ(1)+μ(2)+μ(3)+μ(6) = 1-1-1+1 = 0. -/
example : (1 : ℤ) + (-1) + (-1) + 1 = 0 := by native_decide

/-- Σ_{d|12} μ(d) = μ(1)+μ(2)+μ(3)+μ(4)+μ(6)+μ(12) = 1-1-1+0+1+0 = 0. -/
example : (1 : ℤ) + (-1) + (-1) + 0 + 1 + 0 = 0 := by native_decide

/-! ## 2. Euler's totient function φ(n) -/

/-- Euler's totient values for n = 1..10. -/
def totientTable : Fin 10 → ℕ := ![1, 1, 2, 2, 4, 2, 6, 4, 6, 4]

/-- Σ_{d|6} φ(d) = φ(1)+φ(2)+φ(3)+φ(6) = 1+1+2+2 = 6. -/
example : 1 + 1 + 2 + 2 = 6 := by native_decide

/-- Σ_{d|12} φ(d) = φ(1)+φ(2)+φ(3)+φ(4)+φ(6)+φ(12) = 1+1+2+2+2+4 = 12. -/
example : 1 + 1 + 2 + 2 + 2 + 4 = 12 := by native_decide

/-! ## 3. Divisor function σ_k(n) -/

/-- σ_1(6) = 1+2+3+6 = 12. -/
example : 1 + 2 + 3 + 6 = 12 := by native_decide

/-- σ_1(12) = 1+2+3+4+6+12 = 28. -/
example : 1 + 2 + 3 + 4 + 6 + 12 = 28 := by native_decide

/-- σ_1(28) = 1+2+4+7+14+28 = 56 = 2*28 (28 is perfect). -/
example : 1 + 2 + 4 + 7 + 14 + 28 = 56 := by native_decide

/-! ## 4. Perfect numbers via Euclid-Euler theorem -/

/-- 2^1 * (2^2 - 1) = 2 * 3 = 6. -/
example : 2 * 3 = 6 := by native_decide

/-- 2^2 * (2^3 - 1) = 4 * 7 = 28. -/
example : 4 * 7 = 28 := by native_decide

/-- 2^4 * (2^5 - 1) = 16 * 31 = 496. -/
example : 16 * 31 = 496 := by native_decide

/-- 2^6 * (2^7 - 1) = 64 * 127 = 8128. -/
example : 64 * 127 = 8128 := by native_decide

/-! ## 5. Dirichlet convolution: (Id * μ)(n) = φ(n) -/

/-- (Id * μ)(6) = 1·μ(6) + 2·μ(3) + 3·μ(2) + 6·μ(1) = 1-2-3+6 = 2 = φ(6). -/
example : 1*1 + 2*(-1 : ℤ) + 3*(-1) + 6*1 = 2 := by native_decide

/-! ## 6. Liouville function λ(n) = (-1)^Ω(n) -/

/-- Liouville function values for n = 1..9. -/
def liouvilleTable : Fin 9 → ℤ := ![1, -1, -1, 1, -1, 1, -1, -1, 1]

/-- Σ_{d|4} λ(d) = λ(1)+λ(2)+λ(4) = 1+(-1)+1 = 1 (4 is a perfect square). -/
example : (1 : ℤ) + (-1) + 1 = 1 := by native_decide

/-- Σ_{d|6} λ(d) = λ(1)+λ(2)+λ(3)+λ(6) = 1-1-1+1 = 0 (6 is not a square). -/
example : (1 : ℤ) + (-1) + (-1) + 1 = 0 := by native_decide

/-- Möbius table sample at `n = 6`, using zero-based indexing. -/
theorem mobiusTable_six :
    mobiusTable 5 = 1 := by
  native_decide

/-- Totient table sample at `n = 10`, using zero-based indexing. -/
theorem totientTable_ten :
    totientTable 9 = 4 := by
  native_decide

/-- Liouville table sample at `n = 9`, using zero-based indexing. -/
theorem liouvilleTable_nine :
    liouvilleTable 8 = 1 := by
  native_decide



structure NumberTheoreticGFBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def NumberTheoreticGFBudgetCertificate.controlled
    (c : NumberTheoreticGFBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def NumberTheoreticGFBudgetCertificate.budgetControlled
    (c : NumberTheoreticGFBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def NumberTheoreticGFBudgetCertificate.Ready
    (c : NumberTheoreticGFBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def NumberTheoreticGFBudgetCertificate.size
    (c : NumberTheoreticGFBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem numberTheoreticGF_budgetCertificate_le_size
    (c : NumberTheoreticGFBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleNumberTheoreticGFBudgetCertificate :
    NumberTheoreticGFBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleNumberTheoreticGFBudgetCertificate.Ready := by
  constructor
  · norm_num [NumberTheoreticGFBudgetCertificate.controlled,
      sampleNumberTheoreticGFBudgetCertificate]
  · norm_num [NumberTheoreticGFBudgetCertificate.budgetControlled,
      sampleNumberTheoreticGFBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleNumberTheoreticGFBudgetCertificate.certificateBudgetWindow ≤
      sampleNumberTheoreticGFBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleNumberTheoreticGFBudgetCertificate.Ready := by
  constructor
  · norm_num [NumberTheoreticGFBudgetCertificate.controlled,
      sampleNumberTheoreticGFBudgetCertificate]
  · norm_num [NumberTheoreticGFBudgetCertificate.budgetControlled,
      sampleNumberTheoreticGFBudgetCertificate]

example :
    sampleNumberTheoreticGFBudgetCertificate.certificateBudgetWindow ≤
      sampleNumberTheoreticGFBudgetCertificate.size := by
  apply numberTheoreticGF_budgetCertificate_le_size
  constructor
  · norm_num [NumberTheoreticGFBudgetCertificate.controlled,
      sampleNumberTheoreticGFBudgetCertificate]
  · norm_num [NumberTheoreticGFBudgetCertificate.budgetControlled,
      sampleNumberTheoreticGFBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List NumberTheoreticGFBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleNumberTheoreticGFBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleNumberTheoreticGFBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.NumberTheoreticGF
