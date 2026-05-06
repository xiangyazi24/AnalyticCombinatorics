import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
The general analysis of algebraic functions.

Finite bookkeeping for algebraic equation systems and Puiseux windows.
-/

namespace AnalyticCombinatorics.PartB.Ch7.GeneralAnalysisAlgebraicFunctions

/-- Algebraic equation residual `y^2 - x` over integer samples. -/
def quadraticAlgebraicResidual (x y : ℤ) : ℤ :=
  y ^ 2 - x

/-- Branch regularity condition: derivative in `y` is nonzero. -/
def quadraticDerivativeY (y : ℤ) : ℤ :=
  2 * y

/-- Finite check that sampled branches away from zero are regular. -/
def regularBranchCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    if n = 0 then true else quadraticDerivativeY n ≠ 0

def AlgebraicFunctionWindow (N : ℕ) : Prop :=
  regularBranchCheck N = true

theorem quadraticBranch_regularWindow :
    AlgebraicFunctionWindow 24 := by
  unfold AlgebraicFunctionWindow regularBranchCheck quadraticDerivativeY
  native_decide

theorem quadraticResidual_sample :
    quadraticAlgebraicResidual 9 3 = 0 := by
  norm_num [quadraticAlgebraicResidual]

structure AlgebraicAnalysisWindow where
  polynomialWindow : ℕ
  branchWindow : ℕ
  puiseuxDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def algebraicAnalysisReady (w : AlgebraicAnalysisWindow) : Prop :=
  0 < w.polynomialWindow ∧
    w.puiseuxDepth ≤ w.polynomialWindow + w.branchWindow + w.slack

def algebraicAnalysisBudget (w : AlgebraicAnalysisWindow) : ℕ :=
  w.polynomialWindow + w.branchWindow + w.puiseuxDepth + w.slack

theorem puiseuxDepth_le_algebraicAnalysisBudget
    (w : AlgebraicAnalysisWindow) :
    w.puiseuxDepth ≤ algebraicAnalysisBudget w := by
  unfold algebraicAnalysisBudget
  omega

def sampleAlgebraicAnalysisWindow : AlgebraicAnalysisWindow :=
  { polynomialWindow := 5, branchWindow := 6, puiseuxDepth := 10, slack := 1 }

example : algebraicAnalysisReady sampleAlgebraicAnalysisWindow := by
  norm_num [algebraicAnalysisReady, sampleAlgebraicAnalysisWindow]

structure GeneralAnalysisAlgebraicFunctionsBudgetCertificate where
  polynomialWindow : ℕ
  branchWindow : ℕ
  puiseuxWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GeneralAnalysisAlgebraicFunctionsBudgetCertificate.controlled
    (c : GeneralAnalysisAlgebraicFunctionsBudgetCertificate) : Prop :=
  0 < c.polynomialWindow ∧
    c.puiseuxWindow ≤ c.polynomialWindow + c.branchWindow + c.slack

def GeneralAnalysisAlgebraicFunctionsBudgetCertificate.budgetControlled
    (c : GeneralAnalysisAlgebraicFunctionsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.polynomialWindow + c.branchWindow + c.puiseuxWindow + c.slack

def GeneralAnalysisAlgebraicFunctionsBudgetCertificate.Ready
    (c : GeneralAnalysisAlgebraicFunctionsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def GeneralAnalysisAlgebraicFunctionsBudgetCertificate.size
    (c : GeneralAnalysisAlgebraicFunctionsBudgetCertificate) : ℕ :=
  c.polynomialWindow + c.branchWindow + c.puiseuxWindow + c.slack

theorem generalAnalysisAlgebraicFunctions_budgetCertificate_le_size
    (c : GeneralAnalysisAlgebraicFunctionsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate :
    GeneralAnalysisAlgebraicFunctionsBudgetCertificate :=
  { polynomialWindow := 5
    branchWindow := 6
    puiseuxWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneralAnalysisAlgebraicFunctionsBudgetCertificate.controlled,
      sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate]
  · norm_num [GeneralAnalysisAlgebraicFunctionsBudgetCertificate.budgetControlled,
      sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate.certificateBudgetWindow ≤
      sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate.Ready := by
  constructor
  · norm_num [GeneralAnalysisAlgebraicFunctionsBudgetCertificate.controlled,
      sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate]
  · norm_num
      [GeneralAnalysisAlgebraicFunctionsBudgetCertificate.budgetControlled,
        sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List GeneralAnalysisAlgebraicFunctionsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleGeneralAnalysisAlgebraicFunctionsBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.GeneralAnalysisAlgebraicFunctions
