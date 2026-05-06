import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Polynomials

Finite polynomial arithmetic models used for coefficient extraction and
truncated generating functions.
-/

namespace AnalyticCombinatorics.AppA.FinitePolynomials

def coeff (p : List ℤ) (n : ℕ) : ℤ :=
  p.getD n 0

def add (p q : List ℤ) : List ℤ :=
  (List.range (max p.length q.length)).map fun n => coeff p n + coeff q n

def mul (p q : List ℤ) : List ℤ :=
  (List.range (p.length + q.length - 1)).map fun n =>
    (List.range (n + 1)).foldl (fun s k => s + coeff p k * coeff q (n - k)) 0

theorem add_samples :
    add [1, 2, 3] [4, 5] = [5, 7, 3] := by
  native_decide

theorem mul_samples :
    mul [1, 1] [1, 1, 1] = [1, 2, 2, 1] ∧
    mul [1, -1] [1, 1] = [1, 0, -1] := by
  native_decide

def derivative (p : List ℤ) : List ℤ :=
  (List.range (p.length - 1)).map fun n => ((n + 1 : ℕ) : ℤ) * coeff p (n + 1)

theorem derivative_samples :
    derivative [3, 2, 1] = [2, 2] ∧ derivative [0, 0, 5] = [0, 10] := by
  native_decide

def evalAt (p : List ℤ) (x : ℤ) : ℤ :=
  (List.range p.length).foldl (fun s n => s + coeff p n * x ^ n) 0

theorem evalAt_samples :
    evalAt [1, 2, 3] 2 = 17 ∧ evalAt [1, -1] 1 = 0 := by
  native_decide

def PolynomialCoefficientExtraction
    (p : List ℤ) (closedForm : ℕ → ℤ) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => coeff p n = closedForm n) = true

theorem polynomial_coefficient_extraction_statement :
    PolynomialCoefficientExtraction [1, 3, 3, 1] (fun n => [1, 3, 3, 1].getD n 0) 6 := by
  unfold PolynomialCoefficientExtraction coeff
  native_decide


structure FinitePolynomialsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePolynomialsBudgetCertificate.controlled
    (c : FinitePolynomialsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePolynomialsBudgetCertificate.budgetControlled
    (c : FinitePolynomialsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePolynomialsBudgetCertificate.Ready
    (c : FinitePolynomialsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePolynomialsBudgetCertificate.size
    (c : FinitePolynomialsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePolynomials_budgetCertificate_le_size
    (c : FinitePolynomialsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePolynomialsBudgetCertificate :
    FinitePolynomialsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFinitePolynomialsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePolynomialsBudgetCertificate.controlled,
      sampleFinitePolynomialsBudgetCertificate]
  · norm_num [FinitePolynomialsBudgetCertificate.budgetControlled,
      sampleFinitePolynomialsBudgetCertificate]

example :
    sampleFinitePolynomialsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePolynomialsBudgetCertificate.size := by
  apply finitePolynomials_budgetCertificate_le_size
  constructor
  · norm_num [FinitePolynomialsBudgetCertificate.controlled,
      sampleFinitePolynomialsBudgetCertificate]
  · norm_num [FinitePolynomialsBudgetCertificate.budgetControlled,
      sampleFinitePolynomialsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFinitePolynomialsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePolynomialsBudgetCertificate.controlled,
      sampleFinitePolynomialsBudgetCertificate]
  · norm_num [FinitePolynomialsBudgetCertificate.budgetControlled,
      sampleFinitePolynomialsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePolynomialsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePolynomialsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FinitePolynomialsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePolynomialsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePolynomialsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePolynomials
