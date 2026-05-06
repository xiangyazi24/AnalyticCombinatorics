import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix B: several complex variables.

Finite polydisc and diagonal-extraction bookkeeping.
-/

namespace AnalyticCombinatorics.AppB.SeveralComplexVariables

/-- Bivariate coefficient model for a product of two geometric series. -/
def bivariateGeometricCoeff (baseX baseY i j : ℕ) : ℕ :=
  baseX ^ i * baseY ^ j

/-- Diagonal coefficient of a bivariate coefficient table. -/
def diagonalCoeff (a : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  a n n

/-- Finite polydisc majorant check on a rectangular sample box. -/
def polydiscMajorantCheck
    (a : ℕ → ℕ → ℕ) (baseX baseY N : ℕ) : Bool :=
  (List.range (N + 1)).all fun i =>
    (List.range (N + 1)).all fun j =>
      a i j ≤ baseX ^ i * baseY ^ j

theorem bivariateGeometric_polydiscMajorant :
    polydiscMajorantCheck (bivariateGeometricCoeff 2 3) 2 3 8 = true := by
  unfold polydiscMajorantCheck bivariateGeometricCoeff
  native_decide

theorem bivariateGeometric_diagonal_sample :
    diagonalCoeff (bivariateGeometricCoeff 2 3) 4 = 1296 := by
  unfold diagonalCoeff bivariateGeometricCoeff
  native_decide

/-- Finite ratio audit for diagonal coefficients of a product geometric series. -/
def diagonalRatioCheck (baseX baseY N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    diagonalCoeff (bivariateGeometricCoeff baseX baseY) (n + 1) =
      baseX * baseY * diagonalCoeff (bivariateGeometricCoeff baseX baseY) n

theorem bivariateGeometric_diagonalRatioWindow :
    diagonalRatioCheck 2 3 8 = true := by
  unfold diagonalRatioCheck diagonalCoeff bivariateGeometricCoeff
  native_decide

structure PolydiscWindow where
  variableCount : ℕ
  radiusWindow : ℕ
  diagonalDepth : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def polydiscWindowReady (w : PolydiscWindow) : Prop :=
  0 < w.variableCount ∧ 0 < w.radiusWindow ∧
    w.diagonalDepth ≤ w.variableCount * w.radiusWindow + w.boundarySlack

def polydiscWindowBudget (w : PolydiscWindow) : ℕ :=
  w.variableCount + w.radiusWindow + w.diagonalDepth + w.boundarySlack

theorem diagonalDepth_le_budget (w : PolydiscWindow) :
    w.diagonalDepth ≤ polydiscWindowBudget w := by
  unfold polydiscWindowBudget
  omega

def samplePolydiscWindow : PolydiscWindow :=
  { variableCount := 3, radiusWindow := 4, diagonalDepth := 10, boundarySlack := 2 }

example : polydiscWindowReady samplePolydiscWindow := by
  norm_num [polydiscWindowReady, samplePolydiscWindow]

structure SeveralComplexVariablesBudgetCertificate where
  variableWindow : ℕ
  radiusWindow : ℕ
  diagonalWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SeveralComplexVariablesBudgetCertificate.controlled
    (c : SeveralComplexVariablesBudgetCertificate) : Prop :=
  0 < c.variableWindow ∧ 0 < c.radiusWindow ∧
    c.diagonalWindow ≤ c.variableWindow * c.radiusWindow + c.slack

def SeveralComplexVariablesBudgetCertificate.budgetControlled
    (c : SeveralComplexVariablesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.variableWindow + c.radiusWindow + c.diagonalWindow + c.slack

def SeveralComplexVariablesBudgetCertificate.Ready
    (c : SeveralComplexVariablesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SeveralComplexVariablesBudgetCertificate.size
    (c : SeveralComplexVariablesBudgetCertificate) : ℕ :=
  c.variableWindow + c.radiusWindow + c.diagonalWindow + c.slack

theorem severalComplexVariables_budgetCertificate_le_size
    (c : SeveralComplexVariablesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSeveralComplexVariablesBudgetCertificate :
    SeveralComplexVariablesBudgetCertificate :=
  { variableWindow := 3
    radiusWindow := 4
    diagonalWindow := 10
    certificateBudgetWindow := 18
    slack := 1 }

example : sampleSeveralComplexVariablesBudgetCertificate.Ready := by
  constructor
  · norm_num [SeveralComplexVariablesBudgetCertificate.controlled,
      sampleSeveralComplexVariablesBudgetCertificate]
  · norm_num [SeveralComplexVariablesBudgetCertificate.budgetControlled,
      sampleSeveralComplexVariablesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSeveralComplexVariablesBudgetCertificate.Ready := by
  constructor
  · norm_num [SeveralComplexVariablesBudgetCertificate.controlled,
      sampleSeveralComplexVariablesBudgetCertificate]
  · norm_num [SeveralComplexVariablesBudgetCertificate.budgetControlled,
      sampleSeveralComplexVariablesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSeveralComplexVariablesBudgetCertificate.certificateBudgetWindow ≤
      sampleSeveralComplexVariablesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List SeveralComplexVariablesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSeveralComplexVariablesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSeveralComplexVariablesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.SeveralComplexVariables
