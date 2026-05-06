import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Rational Approximations

Finite rational intervals and approximation certificates.
-/

namespace AnalyticCombinatorics.AppA.RationalApproximations

structure RationalInterval where
  lo : ℚ
  hi : ℚ

def contains (I : RationalInterval) (x : ℚ) : Bool :=
  I.lo ≤ x && x ≤ I.hi

theorem contains_samples :
    contains { lo := 1, hi := 2 } (3 / 2) = true ∧
    contains { lo := 1, hi := 2 } (5 / 2) = false := by
  native_decide

def intervalWidth (I : RationalInterval) : ℚ :=
  I.hi - I.lo

theorem intervalWidth_samples :
    intervalWidth { lo := 1 / 3, hi := 1 / 2 } = 1 / 6 := by
  native_decide

def sqrt2Approx : RationalInterval where
  lo := 141 / 100
  hi := 142 / 100

theorem sqrt2Approx_values :
    sqrt2Approx.lo = 141 / 100 ∧ sqrt2Approx.hi = 71 / 50 ∧
    intervalWidth sqrt2Approx = 1 / 100 := by
  native_decide

def approximationRefines (A B : RationalInterval) : Bool :=
  B.lo ≤ A.lo && A.hi ≤ B.hi

theorem approximationRefines_samples :
    approximationRefines { lo := 11 / 10, hi := 12 / 10 } { lo := 1, hi := 2 } = true ∧
    approximationRefines { lo := 0, hi := 12 / 10 } { lo := 1, hi := 2 } = false := by
  native_decide

def RationalApproximationCertificate
    (x : ℚ) (I : RationalInterval) : Prop :=
  contains I x = true

theorem rational_approximation_certificate_statement :
    RationalApproximationCertificate (1415 / 1000) sqrt2Approx := by
  unfold RationalApproximationCertificate contains sqrt2Approx
  native_decide


structure RationalApproximationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RationalApproximationsBudgetCertificate.controlled
    (c : RationalApproximationsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RationalApproximationsBudgetCertificate.budgetControlled
    (c : RationalApproximationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RationalApproximationsBudgetCertificate.Ready
    (c : RationalApproximationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RationalApproximationsBudgetCertificate.size
    (c : RationalApproximationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem rationalApproximations_budgetCertificate_le_size
    (c : RationalApproximationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRationalApproximationsBudgetCertificate :
    RationalApproximationsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRationalApproximationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalApproximationsBudgetCertificate.controlled,
      sampleRationalApproximationsBudgetCertificate]
  · norm_num [RationalApproximationsBudgetCertificate.budgetControlled,
      sampleRationalApproximationsBudgetCertificate]

example :
    sampleRationalApproximationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRationalApproximationsBudgetCertificate.size := by
  apply rationalApproximations_budgetCertificate_le_size
  constructor
  · norm_num [RationalApproximationsBudgetCertificate.controlled,
      sampleRationalApproximationsBudgetCertificate]
  · norm_num [RationalApproximationsBudgetCertificate.budgetControlled,
      sampleRationalApproximationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRationalApproximationsBudgetCertificate.Ready := by
  constructor
  · norm_num [RationalApproximationsBudgetCertificate.controlled,
      sampleRationalApproximationsBudgetCertificate]
  · norm_num [RationalApproximationsBudgetCertificate.budgetControlled,
      sampleRationalApproximationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRationalApproximationsBudgetCertificate.certificateBudgetWindow ≤
      sampleRationalApproximationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List RationalApproximationsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRationalApproximationsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRationalApproximationsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.RationalApproximations
