import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Rational and meromorphic functions.
-/

namespace AnalyticCombinatorics.PartB.Ch4.RationalMeromorphicFunctions

/-- Coefficients of `1 / (1 - base*z)` over natural samples. -/
def rationalSimplePoleCoeff (base n : ℕ) : ℕ :=
  base ^ n

/-- First-order linear recurrence audit for rational coefficients. -/
def rationalRecurrenceCheck
    (a : ℕ → ℕ) (base N : ℕ) : Bool :=
  (List.range N).all fun n => a (n + 1) = base * a n

/-- Finite rational-meromorphic coefficient window. -/
def RationalCoefficientWindow (a : ℕ → ℕ) (base N : ℕ) : Prop :=
  a 0 = 1 ∧ rationalRecurrenceCheck a base N = true

theorem rationalSimplePoleCoeff_samples :
    rationalSimplePoleCoeff 3 0 = 1 ∧
    rationalSimplePoleCoeff 3 1 = 3 ∧
    rationalSimplePoleCoeff 3 2 = 9 ∧
    rationalSimplePoleCoeff 3 3 = 27 := by
  unfold rationalSimplePoleCoeff
  native_decide

theorem rationalSimplePoleCoeff_window :
    RationalCoefficientWindow (rationalSimplePoleCoeff 3) 3 12 := by
  unfold RationalCoefficientWindow rationalRecurrenceCheck
    rationalSimplePoleCoeff
  native_decide

/-- Prefix sum of a rational simple-pole coefficient sequence. -/
def rationalPrefixSum (a : ℕ → ℕ) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl (fun total n => total + a n) 0

def RationalPrefixWindow (a : ℕ → ℕ) (N total : ℕ) : Prop :=
  rationalPrefixSum a N = total

theorem rationalSimplePoleCoeff_prefixWindow :
    RationalPrefixWindow (rationalSimplePoleCoeff 2) 5 63 := by
  unfold RationalPrefixWindow rationalPrefixSum rationalSimplePoleCoeff
  native_decide

example : rationalSimplePoleCoeff 2 6 = 64 := by
  unfold rationalSimplePoleCoeff
  native_decide

example : rationalPrefixSum (rationalSimplePoleCoeff 3) 3 = 40 := by
  unfold rationalPrefixSum rationalSimplePoleCoeff
  native_decide

structure RationalMeromorphicFunctionsBudgetCertificate where
  rationalWindow : ℕ
  poleWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RationalMeromorphicFunctionsBudgetCertificate.controlled
    (c : RationalMeromorphicFunctionsBudgetCertificate) : Prop :=
  0 < c.rationalWindow ∧
    c.coefficientWindow ≤ c.rationalWindow + c.poleWindow + c.slack

def RationalMeromorphicFunctionsBudgetCertificate.budgetControlled
    (c : RationalMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.rationalWindow + c.poleWindow + c.coefficientWindow + c.slack

def RationalMeromorphicFunctionsBudgetCertificate.Ready
    (c : RationalMeromorphicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RationalMeromorphicFunctionsBudgetCertificate.size
    (c : RationalMeromorphicFunctionsBudgetCertificate) : ℕ :=
  c.rationalWindow + c.poleWindow + c.coefficientWindow + c.slack

theorem rationalMeromorphicFunctions_budgetCertificate_le_size
    (c : RationalMeromorphicFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRationalMeromorphicFunctionsBudgetCertificate :
    RationalMeromorphicFunctionsBudgetCertificate :=
  { rationalWindow := 5
    poleWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRationalMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalMeromorphicFunctionsBudgetCertificate.controlled,
      sampleRationalMeromorphicFunctionsBudgetCertificate]
  · norm_num [RationalMeromorphicFunctionsBudgetCertificate.budgetControlled,
      sampleRationalMeromorphicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRationalMeromorphicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleRationalMeromorphicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRationalMeromorphicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalMeromorphicFunctionsBudgetCertificate.controlled,
      sampleRationalMeromorphicFunctionsBudgetCertificate]
  · norm_num [RationalMeromorphicFunctionsBudgetCertificate.budgetControlled,
      sampleRationalMeromorphicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RationalMeromorphicFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRationalMeromorphicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRationalMeromorphicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch4.RationalMeromorphicFunctions
