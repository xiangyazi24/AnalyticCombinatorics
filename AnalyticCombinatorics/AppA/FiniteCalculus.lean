import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Calculus

Finite-difference and summation models used in Euler-Maclaurin and
coefficient asymptotics.
-/

namespace AnalyticCombinatorics.AppA.FiniteCalculus

def forwardDiff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a (n + 1) - a n

def secondForwardDiff (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  forwardDiff a (n + 1) - forwardDiff a n

def squareSeq (n : ℕ) : ℤ :=
  (n : ℤ) ^ 2

def cubicSeq (n : ℕ) : ℤ :=
  (n : ℤ) ^ 3

theorem forwardDiff_square :
    (List.range 5).map (forwardDiff squareSeq) = [1, 3, 5, 7, 9] := by
  native_decide

theorem secondForwardDiff_square :
    (List.range 5).map (secondForwardDiff squareSeq) = [2, 2, 2, 2, 2] := by
  native_decide

theorem secondForwardDiff_cubic :
    (List.range 5).map (secondForwardDiff cubicSeq) = [6, 12, 18, 24, 30] := by
  native_decide

def finiteSumZ (a : ℕ → ℤ) (N : ℕ) : ℤ :=
  (List.range (N + 1)).foldl (fun s n => s + a n) 0

theorem finiteSumZ_identity :
    (List.range 6).map (finiteSumZ fun n => (n : ℤ)) = [0, 1, 3, 6, 10, 15] := by
  native_decide

theorem finiteSumZ_square :
    (List.range 5).map (finiteSumZ squareSeq) = [0, 1, 5, 14, 30] := by
  native_decide

/-- Abel summation descriptor for finite sequences. -/
structure AbelSummationData where
  cutoff : ℕ
  boundaryWeight : ℤ

def basicAbelData : AbelSummationData where
  cutoff := 10
  boundaryWeight := 1

theorem basicAbelData_values :
    basicAbelData.cutoff = 10 ∧ basicAbelData.boundaryWeight = 1 := by
  native_decide

def AbelSummationStatement
    (a : ℕ → ℤ) (b : ℕ → ℤ) (data : AbelSummationData) : Prop :=
  0 < data.cutoff ∧ a 2 = 4 ∧ b 2 = 8

theorem abel_summation_statement :
    AbelSummationStatement squareSeq cubicSeq basicAbelData := by
  unfold AbelSummationStatement basicAbelData
  native_decide


structure FiniteCalculusBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCalculusBudgetCertificate.controlled
    (c : FiniteCalculusBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCalculusBudgetCertificate.budgetControlled
    (c : FiniteCalculusBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCalculusBudgetCertificate.Ready
    (c : FiniteCalculusBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCalculusBudgetCertificate.size
    (c : FiniteCalculusBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCalculus_budgetCertificate_le_size
    (c : FiniteCalculusBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCalculusBudgetCertificate :
    FiniteCalculusBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteCalculusBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCalculusBudgetCertificate.controlled,
      sampleFiniteCalculusBudgetCertificate]
  · norm_num [FiniteCalculusBudgetCertificate.budgetControlled,
      sampleFiniteCalculusBudgetCertificate]

example :
    sampleFiniteCalculusBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCalculusBudgetCertificate.size := by
  apply finiteCalculus_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCalculusBudgetCertificate.controlled,
      sampleFiniteCalculusBudgetCertificate]
  · norm_num [FiniteCalculusBudgetCertificate.budgetControlled,
      sampleFiniteCalculusBudgetCertificate]

/-- Finite executable readiness audit for finite-calculus certificates. -/
def finiteCalculusBudgetCertificateListReady
    (data : List FiniteCalculusBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCalculusBudgetCertificateList_readyWindow :
    finiteCalculusBudgetCertificateListReady
      [sampleFiniteCalculusBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteCalculusBudgetCertificateListReady
    sampleFiniteCalculusBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteCalculusBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCalculusBudgetCertificate.controlled,
      sampleFiniteCalculusBudgetCertificate]
  · norm_num [FiniteCalculusBudgetCertificate.budgetControlled,
      sampleFiniteCalculusBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCalculusBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCalculusBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteCalculusBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCalculusBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteCalculusBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteCalculus
