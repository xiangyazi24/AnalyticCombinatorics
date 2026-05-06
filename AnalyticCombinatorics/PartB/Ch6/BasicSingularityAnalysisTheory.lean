import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Basic singularity analysis theory.

Finite window bookkeeping for local singular expansions and coefficient
transfer depth.
-/

namespace AnalyticCombinatorics.PartB.Ch6.BasicSingularityAnalysisTheory

/-- Coefficient model for a simple algebraic singular expansion. -/
def singularScaleCoeff (alpha n : ℕ) : ℕ :=
  (n + 1) ^ alpha

/-- Finite transfer envelope from local singular scale to coefficient scale. -/
def singularTransferCheck
    (coeff : ℕ → ℕ) (alpha N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => coeff n ≤ singularScaleCoeff alpha n

def BasicSingularityTransferWindow (coeff : ℕ → ℕ) (alpha N : ℕ) : Prop :=
  singularTransferCheck coeff alpha N = true

theorem polynomial_singularityTransferWindow :
    BasicSingularityTransferWindow (fun n => (n + 1) ^ 2) 2 24 := by
  unfold BasicSingularityTransferWindow singularTransferCheck singularScaleCoeff
  native_decide

/-- Finite monotonicity audit for singular coefficient scales. -/
def singularScaleMonotoneCheck (alpha N : ℕ) : Bool :=
  (List.range N).all fun n =>
    singularScaleCoeff alpha n ≤ singularScaleCoeff alpha (n + 1)

theorem singularScale_monotoneWindow :
    singularScaleMonotoneCheck 3 16 = true := by
  unfold singularScaleMonotoneCheck singularScaleCoeff
  native_decide

structure BasicSingularityWindow where
  expansionDepth : ℕ
  coefficientDepth : ℕ
  errorWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def basicSingularityReady (w : BasicSingularityWindow) : Prop :=
  0 < w.expansionDepth ∧
    w.coefficientDepth ≤ w.expansionDepth + w.errorWindow + w.slack

def basicSingularityBudget (w : BasicSingularityWindow) : ℕ :=
  w.expansionDepth + w.coefficientDepth + w.errorWindow + w.slack

theorem coefficientDepth_le_basicSingularityBudget
    (w : BasicSingularityWindow) :
    w.coefficientDepth ≤ basicSingularityBudget w := by
  unfold basicSingularityBudget
  omega

def sampleBasicSingularityWindow : BasicSingularityWindow :=
  { expansionDepth := 5, coefficientDepth := 7, errorWindow := 3, slack := 1 }

example : basicSingularityReady sampleBasicSingularityWindow := by
  norm_num [basicSingularityReady, sampleBasicSingularityWindow]

structure BasicSingularityAnalysisTheoryBudgetCertificate where
  expansionWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BasicSingularityAnalysisTheoryBudgetCertificate.controlled
    (c : BasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  0 < c.expansionWindow ∧
    c.coefficientWindow ≤ c.expansionWindow + c.slack

def BasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled
    (c : BasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.expansionWindow + c.coefficientWindow + c.slack

def BasicSingularityAnalysisTheoryBudgetCertificate.Ready
    (c : BasicSingularityAnalysisTheoryBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BasicSingularityAnalysisTheoryBudgetCertificate.size
    (c : BasicSingularityAnalysisTheoryBudgetCertificate) : ℕ :=
  c.expansionWindow + c.coefficientWindow + c.slack

theorem basicSingularityAnalysisTheory_budgetCertificate_le_size
    (c : BasicSingularityAnalysisTheoryBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBasicSingularityAnalysisTheoryBudgetCertificate :
    BasicSingularityAnalysisTheoryBudgetCertificate :=
  { expansionWindow := 5
    coefficientWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBasicSingularityAnalysisTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicSingularityAnalysisTheoryBudgetCertificate.controlled,
      sampleBasicSingularityAnalysisTheoryBudgetCertificate]
  · norm_num [BasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled,
      sampleBasicSingularityAnalysisTheoryBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBasicSingularityAnalysisTheoryBudgetCertificate.certificateBudgetWindow ≤
      sampleBasicSingularityAnalysisTheoryBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBasicSingularityAnalysisTheoryBudgetCertificate.Ready := by
  constructor
  · norm_num [BasicSingularityAnalysisTheoryBudgetCertificate.controlled,
      sampleBasicSingularityAnalysisTheoryBudgetCertificate]
  · norm_num [BasicSingularityAnalysisTheoryBudgetCertificate.budgetControlled,
      sampleBasicSingularityAnalysisTheoryBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BasicSingularityAnalysisTheoryBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBasicSingularityAnalysisTheoryBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBasicSingularityAnalysisTheoryBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.BasicSingularityAnalysisTheory
