import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# The general analysis of algebraic functions
-/

namespace AnalyticCombinatorics.PartB.Ch7.GeneralAnalysisOfAlgebraicFunctions

/-- Finite discriminant witness for an algebraic branch point. -/
structure AlgebraicBranchWitness where
  polynomialDegree : ℕ
  discriminantMultiplicity : ℕ
  puiseuxDenominator : ℕ
deriving DecidableEq, Repr

def AlgebraicBranchWitness.valid (w : AlgebraicBranchWitness) : Prop :=
  0 < w.polynomialDegree ∧ 0 < w.puiseuxDenominator

theorem algebraicBranchWitness_sample_valid :
    ({ polynomialDegree := 2, discriminantMultiplicity := 1,
       puiseuxDenominator := 2 } : AlgebraicBranchWitness).valid := by
  norm_num [AlgebraicBranchWitness.valid]

/-- Toy Puiseux exponent numerator after clearing the denominator. -/
def puiseuxClearedExponent (numerator denominator : ℕ) : ℕ :=
  numerator * denominator

theorem puiseuxClearedExponent_sample :
    puiseuxClearedExponent 3 2 = 6 := by
  native_decide

structure AlgebraicAnalysisWindow where
  algebraicWindow : ℕ
  branchWindow : ℕ
  puiseuxWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicAnalysisWindow.ready (w : AlgebraicAnalysisWindow) : Prop :=
  0 < w.algebraicWindow ∧
    w.puiseuxWindow ≤ w.algebraicWindow + w.branchWindow + w.slack

def sampleAlgebraicAnalysisWindow : AlgebraicAnalysisWindow :=
  { algebraicWindow := 4, branchWindow := 3, puiseuxWindow := 7, slack := 0 }

example : sampleAlgebraicAnalysisWindow.ready := by
  norm_num [AlgebraicAnalysisWindow.ready, sampleAlgebraicAnalysisWindow]

structure BudgetCertificate where
  algebraicWindow : ℕ
  branchWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.algebraicWindow ∧ c.branchWindow ≤ c.algebraicWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.algebraicWindow + c.branchWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.algebraicWindow + c.branchWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { algebraicWindow := 5, branchWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.GeneralAnalysisOfAlgebraicFunctions
