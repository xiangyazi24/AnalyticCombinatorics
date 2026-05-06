import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Runge-approximation bookkeeping.

The analytic approximation statement is represented by a finite compact
family, an approximation degree, and an error budget.
-/

namespace AnalyticCombinatorics.AppB.RungeApproximationModels

structure RungeDatum where
  compactComponents : ℕ
  approximationDegree : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def nonemptyCompactFamily (d : RungeDatum) : Prop :=
  0 < d.compactComponents

def approximationNontrivial (d : RungeDatum) : Prop :=
  0 < d.approximationDegree

def rungeReady (d : RungeDatum) : Prop :=
  nonemptyCompactFamily d ∧ approximationNontrivial d

def rungeComplexity (d : RungeDatum) : ℕ :=
  d.compactComponents * d.approximationDegree + d.errorBudget

theorem rungeReady.degree {d : RungeDatum}
    (h : rungeReady d) :
    nonemptyCompactFamily d ∧ approximationNontrivial d ∧
      d.errorBudget ≤ rungeComplexity d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold rungeComplexity
  omega

theorem rungeComplexity_ge_error (d : RungeDatum) :
    d.errorBudget ≤ rungeComplexity d := by
  unfold rungeComplexity
  omega

def sampleRunge : RungeDatum :=
  { compactComponents := 2, approximationDegree := 5, errorBudget := 3 }

example : rungeReady sampleRunge := by
  norm_num [rungeReady, nonemptyCompactFamily, approximationNontrivial, sampleRunge]

example : rungeComplexity sampleRunge = 13 := by
  native_decide

structure RungeWindow where
  compactWindow : ℕ
  degreeWindow : ℕ
  errorWindow : ℕ
  approximationBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RungeWindow.errorControlled (w : RungeWindow) : Prop :=
  w.errorWindow ≤ w.compactWindow * w.degreeWindow + w.slack

def rungeWindowReady (w : RungeWindow) : Prop :=
  0 < w.compactWindow ∧ 0 < w.degreeWindow ∧ w.errorControlled ∧
    w.approximationBudget ≤ w.compactWindow * w.degreeWindow + w.errorWindow + w.slack

def RungeWindow.certificate (w : RungeWindow) : ℕ :=
  w.compactWindow * w.degreeWindow + w.errorWindow + w.approximationBudget + w.slack

theorem runge_approximationBudget_le_certificate (w : RungeWindow) :
    w.approximationBudget ≤ w.certificate := by
  unfold RungeWindow.certificate
  omega

def sampleRungeWindow : RungeWindow :=
  { compactWindow := 2, degreeWindow := 5, errorWindow := 3,
    approximationBudget := 14, slack := 1 }

example : rungeWindowReady sampleRungeWindow := by
  norm_num [rungeWindowReady, RungeWindow.errorControlled, sampleRungeWindow]


structure RungeApproximationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RungeApproximationModelsBudgetCertificate.controlled
    (c : RungeApproximationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RungeApproximationModelsBudgetCertificate.budgetControlled
    (c : RungeApproximationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RungeApproximationModelsBudgetCertificate.Ready
    (c : RungeApproximationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RungeApproximationModelsBudgetCertificate.size
    (c : RungeApproximationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem rungeApproximationModels_budgetCertificate_le_size
    (c : RungeApproximationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRungeApproximationModelsBudgetCertificate :
    RungeApproximationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRungeApproximationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RungeApproximationModelsBudgetCertificate.controlled,
      sampleRungeApproximationModelsBudgetCertificate]
  · norm_num [RungeApproximationModelsBudgetCertificate.budgetControlled,
      sampleRungeApproximationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRungeApproximationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRungeApproximationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRungeApproximationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [RungeApproximationModelsBudgetCertificate.controlled,
      sampleRungeApproximationModelsBudgetCertificate]
  · norm_num [RungeApproximationModelsBudgetCertificate.budgetControlled,
      sampleRungeApproximationModelsBudgetCertificate]

example :
    sampleRungeApproximationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleRungeApproximationModelsBudgetCertificate.size := by
  apply rungeApproximationModels_budgetCertificate_le_size
  constructor
  · norm_num [RungeApproximationModelsBudgetCertificate.controlled,
      sampleRungeApproximationModelsBudgetCertificate]
  · norm_num [RungeApproximationModelsBudgetCertificate.budgetControlled,
      sampleRungeApproximationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RungeApproximationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRungeApproximationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleRungeApproximationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.RungeApproximationModels
