import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dirichlet series window schemas.

The finite record stores abscissa window, coefficient budget, and
vertical slack.
-/

namespace AnalyticCombinatorics.PartB.Ch5.DirichletSeriesWindowSchemas

structure DirichletSeriesWindowData where
  abscissaWindow : ℕ
  coefficientBudget : ℕ
  verticalSlack : ℕ
deriving DecidableEq, Repr

def abscissaWindowPositive (d : DirichletSeriesWindowData) : Prop :=
  0 < d.abscissaWindow

def coefficientsControlled (d : DirichletSeriesWindowData) : Prop :=
  d.coefficientBudget ≤ d.abscissaWindow + d.verticalSlack

def dirichletSeriesWindowReady (d : DirichletSeriesWindowData) : Prop :=
  abscissaWindowPositive d ∧ coefficientsControlled d

def dirichletSeriesWindowBudget (d : DirichletSeriesWindowData) : ℕ :=
  d.abscissaWindow + d.coefficientBudget + d.verticalSlack

theorem dirichletSeriesWindowReady.abscissa
    {d : DirichletSeriesWindowData}
    (h : dirichletSeriesWindowReady d) :
    abscissaWindowPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem coefficientBudget_le_dirichletWindowBudget
    (d : DirichletSeriesWindowData) :
    d.coefficientBudget ≤ dirichletSeriesWindowBudget d := by
  unfold dirichletSeriesWindowBudget
  omega

def sampleDirichletSeriesWindowData : DirichletSeriesWindowData :=
  { abscissaWindow := 6, coefficientBudget := 8, verticalSlack := 3 }

example : dirichletSeriesWindowReady sampleDirichletSeriesWindowData := by
  norm_num [dirichletSeriesWindowReady, abscissaWindowPositive]
  norm_num [coefficientsControlled, sampleDirichletSeriesWindowData]

example : dirichletSeriesWindowBudget sampleDirichletSeriesWindowData = 17 := by
  native_decide

structure DirichletSeriesWindowBudgetCertificate where
  abscissaWindow : ℕ
  coefficientBudgetWindow : ℕ
  verticalSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DirichletSeriesWindowBudgetCertificate.controlled
    (c : DirichletSeriesWindowBudgetCertificate) : Prop :=
  0 < c.abscissaWindow ∧
    c.coefficientBudgetWindow ≤ c.abscissaWindow + c.verticalSlackWindow + c.slack

def DirichletSeriesWindowBudgetCertificate.budgetControlled
    (c : DirichletSeriesWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.abscissaWindow + c.coefficientBudgetWindow + c.verticalSlackWindow + c.slack

def DirichletSeriesWindowBudgetCertificate.Ready
    (c : DirichletSeriesWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DirichletSeriesWindowBudgetCertificate.size
    (c : DirichletSeriesWindowBudgetCertificate) : ℕ :=
  c.abscissaWindow + c.coefficientBudgetWindow + c.verticalSlackWindow + c.slack

theorem dirichletSeriesWindow_budgetCertificate_le_size
    (c : DirichletSeriesWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDirichletSeriesWindowBudgetCertificate :
    DirichletSeriesWindowBudgetCertificate :=
  { abscissaWindow := 6
    coefficientBudgetWindow := 8
    verticalSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDirichletSeriesWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletSeriesWindowBudgetCertificate.controlled,
      sampleDirichletSeriesWindowBudgetCertificate]
  · norm_num [DirichletSeriesWindowBudgetCertificate.budgetControlled,
      sampleDirichletSeriesWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDirichletSeriesWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletSeriesWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDirichletSeriesWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [DirichletSeriesWindowBudgetCertificate.controlled,
      sampleDirichletSeriesWindowBudgetCertificate]
  · norm_num [DirichletSeriesWindowBudgetCertificate.budgetControlled,
      sampleDirichletSeriesWindowBudgetCertificate]

example :
    sampleDirichletSeriesWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleDirichletSeriesWindowBudgetCertificate.size := by
  apply dirichletSeriesWindow_budgetCertificate_le_size
  constructor
  · norm_num [DirichletSeriesWindowBudgetCertificate.controlled,
      sampleDirichletSeriesWindowBudgetCertificate]
  · norm_num [DirichletSeriesWindowBudgetCertificate.budgetControlled,
      sampleDirichletSeriesWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DirichletSeriesWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDirichletSeriesWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleDirichletSeriesWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.DirichletSeriesWindowSchemas
