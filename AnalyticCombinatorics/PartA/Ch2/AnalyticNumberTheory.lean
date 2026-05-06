import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch2.AnalyticNumberTheory


/-- The divisor function σ_k(n) = Σ_{d|n} d^k. -/
def divisorSigma (k n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, d ^ k

-- σ_0(12) = 6 (number of divisors of 12)
example : divisorSigma 0 12 = 6 := by native_decide

-- σ_1(12) = 28 (sum of divisors of 12)
example : divisorSigma 1 12 = 28 := by native_decide

-- σ_0(1) = 1
example : divisorSigma 0 1 = 1 := by native_decide

-- σ_0(p) = 2 for primes
example : divisorSigma 0 2 = 2 := by native_decide
example : divisorSigma 0 3 = 2 := by native_decide
example : divisorSigma 0 5 = 2 := by native_decide
example : divisorSigma 0 7 = 2 := by native_decide
example : divisorSigma 0 11 = 2 := by native_decide

/-! ## Euler's totient verification -/

example : Nat.totient 1 = 1 := by native_decide
example : Nat.totient 2 = 1 := by native_decide
example : Nat.totient 3 = 2 := by native_decide
example : Nat.totient 4 = 2 := by native_decide
example : Nat.totient 5 = 4 := by native_decide
example : Nat.totient 6 = 2 := by native_decide
example : Nat.totient 7 = 6 := by native_decide
example : Nat.totient 8 = 4 := by native_decide
example : Nat.totient 9 = 6 := by native_decide
example : Nat.totient 10 = 4 := by native_decide
example : Nat.totient 11 = 10 := by native_decide
example : Nat.totient 12 = 4 := by native_decide

/-! ## Totient sum identity: Σ_{d|n} φ(d) = n -/

/-- Sum of Euler's totient over divisors of n. -/
def totientDivisorSum (n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, Nat.totient d

example : totientDivisorSum 1 = 1 := by native_decide
example : totientDivisorSum 2 = 2 := by native_decide
example : totientDivisorSum 3 = 3 := by native_decide
example : totientDivisorSum 4 = 4 := by native_decide
example : totientDivisorSum 5 = 5 := by native_decide
example : totientDivisorSum 6 = 6 := by native_decide
example : totientDivisorSum 7 = 7 := by native_decide
example : totientDivisorSum 8 = 8 := by native_decide
example : totientDivisorSum 9 = 9 := by native_decide
example : totientDivisorSum 10 = 10 := by native_decide
example : totientDivisorSum 11 = 11 := by native_decide
example : totientDivisorSum 12 = 12 := by native_decide

/-! ## Squarefree counting -/

/-- A positive integer is squarefree if no perfect square > 1 divides it. -/
def isSquarefree (n : ℕ) : Bool :=
  n ≥ 1 && ((Nat.divisors n).filter (fun d => decide (d * d ∣ n) && decide (d > 1))).card == 0

/-- Count of squarefree numbers in {1, ..., n}. -/
def squarefreeCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => isSquarefree (k + 1))).card

example : squarefreeCount 10 = 7 := by native_decide
example : squarefreeCount 20 = 13 := by native_decide
example : squarefreeCount 30 = 19 := by native_decide

/-! ## Möbius function (table-based) -/

/-- Möbius function values for 0..6, stored as a lookup table.
    μ(1)=1, μ(2)=-1, μ(3)=-1, μ(4)=0, μ(5)=-1, μ(6)=1. -/
def mobiusTable : Fin 7 → ℤ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => -1
  | ⟨6, _⟩ => 1

example : mobiusTable ⟨1, by omega⟩ = 1 := by native_decide
example : mobiusTable ⟨2, by omega⟩ = -1 := by native_decide
example : mobiusTable ⟨3, by omega⟩ = -1 := by native_decide
example : mobiusTable ⟨4, by omega⟩ = 0 := by native_decide
example : mobiusTable ⟨5, by omega⟩ = -1 := by native_decide
example : mobiusTable ⟨6, by omega⟩ = 1 := by native_decide

/-- Totient divisor-sum sample. -/
theorem totientDivisorSum_twelve :
    totientDivisorSum 12 = 12 := by
  native_decide

/-- Squarefree counting sample through thirty. -/
theorem squarefreeCount_thirty :
    squarefreeCount 30 = 19 := by
  native_decide



structure AnalyticNumberTheoryBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticNumberTheoryBudgetCertificate.controlled
    (c : AnalyticNumberTheoryBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticNumberTheoryBudgetCertificate.budgetControlled
    (c : AnalyticNumberTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticNumberTheoryBudgetCertificate.Ready
    (c : AnalyticNumberTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticNumberTheoryBudgetCertificate.size
    (c : AnalyticNumberTheoryBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticNumberTheory_budgetCertificate_le_size
    (c : AnalyticNumberTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticNumberTheoryBudgetCertificate :
    AnalyticNumberTheoryBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticNumberTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNumberTheoryBudgetCertificate.controlled,
      sampleAnalyticNumberTheoryBudgetCertificate]
  · norm_num [AnalyticNumberTheoryBudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticNumberTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNumberTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticNumberTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticNumberTheoryBudgetCertificate.controlled,
      sampleAnalyticNumberTheoryBudgetCertificate]
  · norm_num [AnalyticNumberTheoryBudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheoryBudgetCertificate]

example :
    sampleAnalyticNumberTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticNumberTheoryBudgetCertificate.size := by
  apply analyticNumberTheory_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticNumberTheoryBudgetCertificate.controlled,
      sampleAnalyticNumberTheoryBudgetCertificate]
  · norm_num [AnalyticNumberTheoryBudgetCertificate.budgetControlled,
      sampleAnalyticNumberTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticNumberTheoryBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticNumberTheoryBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticNumberTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.AnalyticNumberTheory
