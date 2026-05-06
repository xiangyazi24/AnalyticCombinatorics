import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: algebraic elimination.

Finite degree/resultant-window bookkeeping for elimination arguments.
-/

namespace AnalyticCombinatorics.AppB.AlgebraicElimination

/-- Residual of eliminating `y` from `y = x + 1` and `z = y + 1`. -/
def linearEliminationResidual (x z : ℤ) : ℤ :=
  z - (x + 2)

/-- Finite audit that the eliminated relation holds on sampled data. -/
def linearEliminationCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun x =>
    linearEliminationResidual x (x + 2) = 0

theorem linearElimination_window :
    linearEliminationCheck 24 = true := by
  unfold linearEliminationCheck linearEliminationResidual
  native_decide

def eliminationDegreeBudget (leftDegree rightDegree variableCount : ℕ) : ℕ :=
  leftDegree * rightDegree + variableCount

theorem eliminationDegreeBudget_samples :
    eliminationDegreeBudget 2 3 1 = 7 ∧
    eliminationDegreeBudget 4 5 2 = 22 := by
  native_decide

/-- Finite composition audit before eliminating the intermediate variable. -/
def linearCompositionCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun x =>
    let y := x + 1
    let z := y + 1
    linearEliminationResidual x z = 0

theorem linearComposition_eliminationWindow :
    linearCompositionCheck 24 = true := by
  unfold linearCompositionCheck linearEliminationResidual
  native_decide

structure AlgebraicEliminationData where
  leftDegree : ℕ
  rightDegree : ℕ
  variableCount : ℕ
  resultantWindow : ℕ
deriving DecidableEq, Repr

def algebraicEliminationReady (d : AlgebraicEliminationData) : Prop :=
  0 < d.leftDegree ∧ 0 < d.rightDegree ∧
    d.resultantWindow ≤
      eliminationDegreeBudget d.leftDegree d.rightDegree d.variableCount

def algebraicEliminationBudget (d : AlgebraicEliminationData) : ℕ :=
  d.leftDegree + d.rightDegree + d.variableCount + d.resultantWindow

theorem resultantWindow_le_budget (d : AlgebraicEliminationData) :
    d.resultantWindow ≤ algebraicEliminationBudget d := by
  unfold algebraicEliminationBudget
  omega

def sampleAlgebraicEliminationData : AlgebraicEliminationData :=
  { leftDegree := 2, rightDegree := 3, variableCount := 1, resultantWindow := 7 }

example : algebraicEliminationReady sampleAlgebraicEliminationData := by
  norm_num [algebraicEliminationReady, eliminationDegreeBudget,
    sampleAlgebraicEliminationData]

structure AlgebraicEliminationBudgetCertificate where
  degreeWindow : ℕ
  variableWindow : ℕ
  resultantWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AlgebraicEliminationBudgetCertificate.controlled
    (c : AlgebraicEliminationBudgetCertificate) : Prop :=
  0 < c.degreeWindow ∧
    c.resultantWindow ≤ c.degreeWindow * c.degreeWindow + c.variableWindow + c.slack

def AlgebraicEliminationBudgetCertificate.budgetControlled
    (c : AlgebraicEliminationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.degreeWindow + c.variableWindow + c.resultantWindow + c.slack

def AlgebraicEliminationBudgetCertificate.Ready
    (c : AlgebraicEliminationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AlgebraicEliminationBudgetCertificate.size
    (c : AlgebraicEliminationBudgetCertificate) : ℕ :=
  c.degreeWindow + c.variableWindow + c.resultantWindow + c.slack

theorem algebraicElimination_budgetCertificate_le_size
    (c : AlgebraicEliminationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleAlgebraicEliminationBudgetCertificate :
    AlgebraicEliminationBudgetCertificate :=
  { degreeWindow := 3
    variableWindow := 1
    resultantWindow := 7
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleAlgebraicEliminationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicEliminationBudgetCertificate.controlled,
      sampleAlgebraicEliminationBudgetCertificate]
  · norm_num [AlgebraicEliminationBudgetCertificate.budgetControlled,
      sampleAlgebraicEliminationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleAlgebraicEliminationBudgetCertificate.Ready := by
  constructor
  · norm_num [AlgebraicEliminationBudgetCertificate.controlled,
      sampleAlgebraicEliminationBudgetCertificate]
  · norm_num [AlgebraicEliminationBudgetCertificate.budgetControlled,
      sampleAlgebraicEliminationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAlgebraicEliminationBudgetCertificate.certificateBudgetWindow ≤
      sampleAlgebraicEliminationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List AlgebraicEliminationBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleAlgebraicEliminationBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleAlgebraicEliminationBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AlgebraicElimination
