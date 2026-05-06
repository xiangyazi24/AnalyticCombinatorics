import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Dominated convergence schema bookkeeping.

The module records finite pointwise convergence flags and domination
budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.DominatedConvergenceSchemas

structure DominatedConvergenceData where
  pointwiseConvergent : Prop
  dominationBudget : ℕ
  errorBudget : ℕ
deriving Repr

def positiveDominationBudget (d : DominatedConvergenceData) : Prop :=
  0 < d.dominationBudget

def dominatedConvergenceReady (d : DominatedConvergenceData) : Prop :=
  d.pointwiseConvergent ∧ positiveDominationBudget d

def dominatedErrorBudget (d : DominatedConvergenceData) : ℕ :=
  d.dominationBudget + d.errorBudget

theorem dominatedConvergenceReady.pointwise {d : DominatedConvergenceData}
    (h : dominatedConvergenceReady d) :
    d.pointwiseConvergent ∧ positiveDominationBudget d ∧
      d.dominationBudget ≤ dominatedErrorBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold dominatedErrorBudget
  omega

theorem dominationBudget_le_errorBudget (d : DominatedConvergenceData) :
    d.dominationBudget ≤ dominatedErrorBudget d := by
  unfold dominatedErrorBudget
  omega

def sampleDominatedConvergence : DominatedConvergenceData :=
  { pointwiseConvergent := 2 ≤ 6, dominationBudget := 6, errorBudget := 2 }

example : dominatedConvergenceReady sampleDominatedConvergence := by
  norm_num [dominatedConvergenceReady, positiveDominationBudget, sampleDominatedConvergence]

example : dominatedErrorBudget sampleDominatedConvergence = 8 := by
  native_decide

structure DominatedConvergenceWindow where
  dominationBudget : ℕ
  errorBudget : ℕ
  pointwiseTests : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominatedConvergenceWindow.dominationReady (w : DominatedConvergenceWindow) : Prop :=
  0 < w.dominationBudget

def DominatedConvergenceWindow.errorControlled (w : DominatedConvergenceWindow) : Prop :=
  w.errorBudget ≤ w.dominationBudget + w.slack

def DominatedConvergenceWindow.testControlled (w : DominatedConvergenceWindow) : Prop :=
  w.pointwiseTests ≤ w.dominationBudget + w.errorBudget + w.slack

def DominatedConvergenceWindow.ready (w : DominatedConvergenceWindow) : Prop :=
  w.dominationReady ∧ w.errorControlled ∧ w.testControlled

def DominatedConvergenceWindow.certificate (w : DominatedConvergenceWindow) : ℕ :=
  w.dominationBudget + w.errorBudget + w.pointwiseTests + w.slack

theorem pointwiseTests_le_certificate (w : DominatedConvergenceWindow) :
    w.pointwiseTests ≤ w.certificate := by
  unfold DominatedConvergenceWindow.certificate
  omega

def sampleDominatedConvergenceWindow : DominatedConvergenceWindow :=
  { dominationBudget := 6, errorBudget := 2, pointwiseTests := 5, slack := 0 }

example : sampleDominatedConvergenceWindow.ready := by
  norm_num [sampleDominatedConvergenceWindow, DominatedConvergenceWindow.ready,
    DominatedConvergenceWindow.dominationReady,
    DominatedConvergenceWindow.errorControlled,
    DominatedConvergenceWindow.testControlled]

/-- Finite executable readiness audit for dominated-convergence windows. -/
def dominatedConvergenceWindowListReady
    (windows : List DominatedConvergenceWindow) : Bool :=
  windows.all fun w =>
    0 < w.dominationBudget &&
      w.errorBudget ≤ w.dominationBudget + w.slack &&
        w.pointwiseTests ≤ w.dominationBudget + w.errorBudget + w.slack

theorem dominatedConvergenceWindowList_readyWindow :
    dominatedConvergenceWindowListReady
      [{ dominationBudget := 4, errorBudget := 1, pointwiseTests := 4, slack := 1 },
       { dominationBudget := 6, errorBudget := 2, pointwiseTests := 5, slack := 0 }] =
      true := by
  unfold dominatedConvergenceWindowListReady
  native_decide

/-- A refinement certificate for dominated convergence windows. -/
structure DominatedConvergenceCertificate where
  dominationWindow : ℕ
  errorWindow : ℕ
  pointwiseTestWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Domination budget controls error and pointwise tests. -/
def dominatedConvergenceCertificateControlled
    (w : DominatedConvergenceCertificate) : Prop :=
  0 < w.dominationWindow ∧
    w.errorWindow ≤ w.dominationWindow + w.slack ∧
      w.pointwiseTestWindow ≤ w.dominationWindow + w.errorWindow + w.slack

/-- Readiness for a dominated convergence certificate. -/
def dominatedConvergenceCertificateReady
    (w : DominatedConvergenceCertificate) : Prop :=
  dominatedConvergenceCertificateControlled w ∧
    w.certificateBudget ≤ w.dominationWindow + w.pointwiseTestWindow + w.slack

/-- Total size of a dominated convergence certificate. -/
def dominatedConvergenceCertificateSize
    (w : DominatedConvergenceCertificate) : ℕ :=
  w.dominationWindow + w.errorWindow + w.pointwiseTestWindow +
    w.certificateBudget + w.slack

theorem dominatedConvergenceCertificate_budget_le_size
    (w : DominatedConvergenceCertificate)
    (h : dominatedConvergenceCertificateReady w) :
    w.certificateBudget ≤ dominatedConvergenceCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold dominatedConvergenceCertificateSize
  omega

def sampleDominatedConvergenceCertificate :
    DominatedConvergenceCertificate where
  dominationWindow := 6
  errorWindow := 2
  pointwiseTestWindow := 5
  certificateBudget := 11
  slack := 0

example :
    dominatedConvergenceCertificateReady
      sampleDominatedConvergenceCertificate := by
  norm_num [dominatedConvergenceCertificateReady,
    dominatedConvergenceCertificateControlled, sampleDominatedConvergenceCertificate]

example :
    sampleDominatedConvergenceCertificate.certificateBudget ≤
      dominatedConvergenceCertificateSize
        sampleDominatedConvergenceCertificate := by
  apply dominatedConvergenceCertificate_budget_le_size
  norm_num [dominatedConvergenceCertificateReady,
    dominatedConvergenceCertificateControlled, sampleDominatedConvergenceCertificate]

/-- A refinement certificate with the dominated-convergence budget separated from size. -/
structure DominatedConvergenceRefinementCertificate where
  dominationWindow : ℕ
  errorWindow : ℕ
  pointwiseTestWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominatedConvergenceRefinementCertificate.dominationControlled
    (cert : DominatedConvergenceRefinementCertificate) : Prop :=
  0 < cert.dominationWindow ∧
    cert.errorWindow ≤ cert.dominationWindow + cert.slack ∧
      cert.pointwiseTestWindow ≤ cert.dominationWindow + cert.errorWindow + cert.slack

def DominatedConvergenceRefinementCertificate.budgetControlled
    (cert : DominatedConvergenceRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.dominationWindow + cert.errorWindow + cert.pointwiseTestWindow + cert.slack

def dominatedConvergenceRefinementReady
    (cert : DominatedConvergenceRefinementCertificate) : Prop :=
  cert.dominationControlled ∧ cert.budgetControlled

def DominatedConvergenceRefinementCertificate.size
    (cert : DominatedConvergenceRefinementCertificate) : ℕ :=
  cert.dominationWindow + cert.errorWindow + cert.pointwiseTestWindow + cert.slack

theorem dominatedConvergence_certificateBudgetWindow_le_size
    (cert : DominatedConvergenceRefinementCertificate)
    (h : dominatedConvergenceRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDominatedConvergenceRefinementCertificate :
    DominatedConvergenceRefinementCertificate :=
  { dominationWindow := 6, errorWindow := 2, pointwiseTestWindow := 5,
    certificateBudgetWindow := 13, slack := 0 }

example :
    dominatedConvergenceRefinementReady
      sampleDominatedConvergenceRefinementCertificate := by
  norm_num [dominatedConvergenceRefinementReady,
    DominatedConvergenceRefinementCertificate.dominationControlled,
    DominatedConvergenceRefinementCertificate.budgetControlled,
    sampleDominatedConvergenceRefinementCertificate]

example :
    sampleDominatedConvergenceRefinementCertificate.certificateBudgetWindow ≤
      sampleDominatedConvergenceRefinementCertificate.size := by
  apply dominatedConvergence_certificateBudgetWindow_le_size
  norm_num [dominatedConvergenceRefinementReady,
    DominatedConvergenceRefinementCertificate.dominationControlled,
    DominatedConvergenceRefinementCertificate.budgetControlled,
    sampleDominatedConvergenceRefinementCertificate]


structure DominatedConvergenceSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DominatedConvergenceSchemasBudgetCertificate.controlled
    (c : DominatedConvergenceSchemasBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def DominatedConvergenceSchemasBudgetCertificate.budgetControlled
    (c : DominatedConvergenceSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def DominatedConvergenceSchemasBudgetCertificate.Ready
    (c : DominatedConvergenceSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DominatedConvergenceSchemasBudgetCertificate.size
    (c : DominatedConvergenceSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem dominatedConvergenceSchemas_budgetCertificate_le_size
    (c : DominatedConvergenceSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDominatedConvergenceSchemasBudgetCertificate :
    DominatedConvergenceSchemasBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleDominatedConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.controlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]

example :
    sampleDominatedConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDominatedConvergenceSchemasBudgetCertificate.size := by
  apply dominatedConvergenceSchemas_budgetCertificate_le_size
  constructor
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.controlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleDominatedConvergenceSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.controlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]
  · norm_num [DominatedConvergenceSchemasBudgetCertificate.budgetControlled,
      sampleDominatedConvergenceSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDominatedConvergenceSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleDominatedConvergenceSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List DominatedConvergenceSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleDominatedConvergenceSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleDominatedConvergenceSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.DominatedConvergenceSchemas
