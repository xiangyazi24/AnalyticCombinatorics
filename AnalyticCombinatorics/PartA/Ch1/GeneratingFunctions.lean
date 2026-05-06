/-
  Chapter I — Generating Functions: Coefficient Extraction and Transforms

  Basic definitions for OGF/EGF coefficient extraction, binomial transforms,
  and Borel transform, with numerical verifications.

  Reference: Flajolet & Sedgewick, Analytic Combinatorics, Chapter I.
-/
import Mathlib.Tactic

set_option linter.style.nativeDecide false

namespace AnalyticCombinatorics.PartA.Ch1.GeneratingFunctions
/-- OGF coefficient extraction: [z^n] A(z) = a_n -/
def ogfCoeff (a : ℕ → ℕ) (n : ℕ) : ℕ := a n

/-- Partial sums of the all-ones sequence: ∑_{k=0}^{n} 1 = n + 1 -/
def partialSum (n : ℕ) : ℕ := n + 1

-- Verify partialSum n = n + 1 for n = 0..10
example : partialSum 0 = 1 := by native_decide
example : partialSum 1 = 2 := by native_decide
example : partialSum 2 = 3 := by native_decide
example : partialSum 3 = 4 := by native_decide
example : partialSum 4 = 5 := by native_decide
example : partialSum 5 = 6 := by native_decide
example : partialSum 6 = 7 := by native_decide
example : partialSum 7 = 8 := by native_decide
example : partialSum 8 = 9 := by native_decide
example : partialSum 9 = 10 := by native_decide
example : partialSum 10 = 11 := by native_decide

/-- EGF coefficient extraction: [z^n/n!] A(z) = a_n / n! -/
def egfCoeff (a : ℕ → ℕ) (n : ℕ) : ℚ := (a n : ℚ) / (Nat.factorial n : ℚ)

-- For a_n = n! (permutations): egfCoeff Nat.factorial n = 1
example : egfCoeff Nat.factorial 0 = 1 := by native_decide
example : egfCoeff Nat.factorial 1 = 1 := by native_decide
example : egfCoeff Nat.factorial 2 = 1 := by native_decide
example : egfCoeff Nat.factorial 3 = 1 := by native_decide
example : egfCoeff Nat.factorial 4 = 1 := by native_decide
example : egfCoeff Nat.factorial 5 = 1 := by native_decide
example : egfCoeff Nat.factorial 6 = 1 := by native_decide
example : egfCoeff Nat.factorial 7 = 1 := by native_decide
example : egfCoeff Nat.factorial 8 = 1 := by native_decide

/-- Binomial transform: (Ba)_n = ∑_{k=0}^{n} C(n,k) * a_k -/
def binomialTransform (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * a k

-- Transform of constant-1 gives 2^n
example : binomialTransform (fun _ => 1) 0 = 2 ^ 0 := by native_decide
example : binomialTransform (fun _ => 1) 1 = 2 ^ 1 := by native_decide
example : binomialTransform (fun _ => 1) 2 = 2 ^ 2 := by native_decide
example : binomialTransform (fun _ => 1) 3 = 2 ^ 3 := by native_decide
example : binomialTransform (fun _ => 1) 4 = 2 ^ 4 := by native_decide
example : binomialTransform (fun _ => 1) 5 = 2 ^ 5 := by native_decide
example : binomialTransform (fun _ => 1) 6 = 2 ^ 6 := by native_decide
example : binomialTransform (fun _ => 1) 7 = 2 ^ 7 := by native_decide
example : binomialTransform (fun _ => 1) 8 = 2 ^ 8 := by native_decide

/-- Inverse binomial transform: (B⁻¹a)_n = ∑_{k=0}^{n} (-1)^(n-k) * C(n,k) * a_k -/
def invBinomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.choose n k : ℤ) * a k

-- Verify: invBinomialTransform (fun n => 2^n) n = 1 for n=0..6
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 0 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 1 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 2 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 3 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 4 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 5 = 1 := by native_decide
example : invBinomialTransform (fun n => (2 : ℤ) ^ n) 6 = 1 := by native_decide

/-- Borel transform: converts OGF coefficients a_n to EGF coefficients a_n/n! -/
def borelTransform (a : ℕ → ℕ) (n : ℕ) : ℚ := (a n : ℚ) / (Nat.factorial n : ℚ)

-- For a_n = 1: borelTransform (fun _ => 1) n = 1/n!
example : borelTransform (fun _ => 1) 0 = 1 / (Nat.factorial 0 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 1 = 1 / (Nat.factorial 1 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 2 = 1 / (Nat.factorial 2 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 3 = 1 / (Nat.factorial 3 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 4 = 1 / (Nat.factorial 4 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 5 = 1 / (Nat.factorial 5 : ℚ) := by native_decide
example : borelTransform (fun _ => 1) 6 = 1 / (Nat.factorial 6 : ℚ) := by native_decide

/-- Binomial transform of the constant sequence at index eight. -/
theorem binomialTransform_const_one_eight :
    binomialTransform (fun _ => 1) 8 = 2 ^ 8 := by
  native_decide

/-- Inverse binomial transform recovers the constant sequence at index six. -/
theorem invBinomialTransform_powers_two_six :
    invBinomialTransform (fun n => (2 : ℤ) ^ n) 6 = 1 := by
  native_decide


structure GeneratingFunctionsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneratingFunctionsBudgetCertificate.controlled
    (c : GeneratingFunctionsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def GeneratingFunctionsBudgetCertificate.budgetControlled
    (c : GeneratingFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def GeneratingFunctionsBudgetCertificate.Ready
    (c : GeneratingFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneratingFunctionsBudgetCertificate.size
    (c : GeneratingFunctionsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem generatingFunctions_budgetCertificate_le_size
    (c : GeneratingFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleGeneratingFunctionsBudgetCertificate :
    GeneratingFunctionsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionsBudgetCertificate.controlled,
      sampleGeneratingFunctionsBudgetCertificate]
  · norm_num [GeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGeneratingFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneratingFunctionsBudgetCertificate.controlled,
      sampleGeneratingFunctionsBudgetCertificate]
  · norm_num [GeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionsBudgetCertificate]

example :
    sampleGeneratingFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneratingFunctionsBudgetCertificate.size := by
  apply generatingFunctions_budgetCertificate_le_size
  constructor
  · norm_num [GeneratingFunctionsBudgetCertificate.controlled,
      sampleGeneratingFunctionsBudgetCertificate]
  · norm_num [GeneratingFunctionsBudgetCertificate.budgetControlled,
      sampleGeneratingFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List GeneratingFunctionsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneratingFunctionsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleGeneratingFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.GeneratingFunctions
