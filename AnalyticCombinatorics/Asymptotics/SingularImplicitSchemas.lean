import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Singular implicit schema bookkeeping.

This module records finite criticality and nondegeneracy conditions for
implicit-function singularity schemas.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularImplicitSchemas

structure SingularImplicitData where
  criticalEquationRank : ℕ
  derivativeOrder : ℕ
  perturbationBudget : ℕ
deriving DecidableEq, Repr

def criticalEquationNonzero (d : SingularImplicitData) : Prop :=
  0 < d.criticalEquationRank

def derivativeNonzero (d : SingularImplicitData) : Prop :=
  0 < d.derivativeOrder

def singularImplicitReady (d : SingularImplicitData) : Prop :=
  criticalEquationNonzero d ∧ derivativeNonzero d

def implicitBudget (d : SingularImplicitData) : ℕ :=
  d.criticalEquationRank * d.derivativeOrder + d.perturbationBudget

theorem singularImplicitReady.derivative {d : SingularImplicitData}
    (h : singularImplicitReady d) :
    criticalEquationNonzero d ∧ derivativeNonzero d ∧ d.perturbationBudget ≤ implicitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold implicitBudget
  omega

theorem perturbationBudget_le_implicitBudget (d : SingularImplicitData) :
    d.perturbationBudget ≤ implicitBudget d := by
  unfold implicitBudget
  omega

def sampleSingularImplicit : SingularImplicitData :=
  { criticalEquationRank := 2, derivativeOrder := 3, perturbationBudget := 4 }

example : singularImplicitReady sampleSingularImplicit := by
  norm_num
    [singularImplicitReady, criticalEquationNonzero, derivativeNonzero,
      sampleSingularImplicit]

example : implicitBudget sampleSingularImplicit = 10 := by
  native_decide

/-- Finite executable readiness audit for singular implicit data. -/
def singularImplicitDataListReady
    (data : List SingularImplicitData) : Bool :=
  data.all fun d => 0 < d.criticalEquationRank && 0 < d.derivativeOrder

theorem singularImplicitDataList_readyWindow :
    singularImplicitDataListReady
      [{ criticalEquationRank := 1, derivativeOrder := 2, perturbationBudget := 3 },
       { criticalEquationRank := 2, derivativeOrder := 3, perturbationBudget := 4 }] =
      true := by
  unfold singularImplicitDataListReady
  native_decide

/-- A certificate window for singular implicit schema data. -/
structure SingularImplicitCertificateWindow where
  criticalWindow : ℕ
  derivativeWindow : ℕ
  perturbationWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Perturbations are controlled by the critical and derivative windows. -/
def singularImplicitCertificateControlled
    (w : SingularImplicitCertificateWindow) : Prop :=
  w.perturbationWindow ≤ w.criticalWindow * w.derivativeWindow + w.slack

/-- Readiness for a singular implicit certificate. -/
def singularImplicitCertificateReady
    (w : SingularImplicitCertificateWindow) : Prop :=
  0 < w.criticalWindow ∧
    0 < w.derivativeWindow ∧
      singularImplicitCertificateControlled w ∧
        w.certificateBudget ≤
          w.criticalWindow * w.derivativeWindow + w.perturbationWindow + w.slack

/-- Total size of a singular implicit certificate. -/
def singularImplicitCertificate
    (w : SingularImplicitCertificateWindow) : ℕ :=
  w.criticalWindow + w.derivativeWindow + w.perturbationWindow +
    w.certificateBudget + w.slack

theorem singularImplicitCertificate_budget_le_certificate
    (w : SingularImplicitCertificateWindow)
    (h : singularImplicitCertificateReady w) :
    w.certificateBudget ≤ singularImplicitCertificate w := by
  rcases h with ⟨_, _, _, hbudget⟩
  unfold singularImplicitCertificate
  omega

def sampleSingularImplicitCertificateWindow :
    SingularImplicitCertificateWindow where
  criticalWindow := 3
  derivativeWindow := 4
  perturbationWindow := 8
  certificateBudget := 18
  slack := 2

example :
    singularImplicitCertificateReady
      sampleSingularImplicitCertificateWindow := by
  norm_num [singularImplicitCertificateReady,
    singularImplicitCertificateControlled,
    sampleSingularImplicitCertificateWindow]

example :
    sampleSingularImplicitCertificateWindow.certificateBudget ≤
      singularImplicitCertificate sampleSingularImplicitCertificateWindow := by
  apply singularImplicitCertificate_budget_le_certificate
  norm_num [singularImplicitCertificateReady,
    singularImplicitCertificateControlled,
    sampleSingularImplicitCertificateWindow]

structure SingularImplicitRefinementCertificate where
  criticalWindow : ℕ
  derivativeWindow : ℕ
  perturbationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularImplicitRefinementCertificate.perturbationControlled
    (c : SingularImplicitRefinementCertificate) : Prop :=
  c.perturbationWindow ≤ c.criticalWindow * c.derivativeWindow + c.slack

def SingularImplicitRefinementCertificate.certificateBudgetControlled
    (c : SingularImplicitRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalWindow * c.derivativeWindow + c.perturbationWindow + c.slack

def singularImplicitRefinementReady
    (c : SingularImplicitRefinementCertificate) : Prop :=
  0 < c.criticalWindow ∧
    0 < c.derivativeWindow ∧
    c.perturbationControlled ∧
    c.certificateBudgetControlled

def SingularImplicitRefinementCertificate.size
    (c : SingularImplicitRefinementCertificate) : ℕ :=
  c.criticalWindow * c.derivativeWindow + c.perturbationWindow + c.slack

theorem singularImplicit_certificateBudgetWindow_le_size
    {c : SingularImplicitRefinementCertificate}
    (h : singularImplicitRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, _, hbudget⟩
  exact hbudget

def sampleSingularImplicitRefinementCertificate :
    SingularImplicitRefinementCertificate :=
  { criticalWindow := 3, derivativeWindow := 4, perturbationWindow := 8,
    certificateBudgetWindow := 18, slack := 2 }

example : singularImplicitRefinementReady
    sampleSingularImplicitRefinementCertificate := by
  norm_num [singularImplicitRefinementReady,
    SingularImplicitRefinementCertificate.perturbationControlled,
    SingularImplicitRefinementCertificate.certificateBudgetControlled,
    sampleSingularImplicitRefinementCertificate]

example :
    sampleSingularImplicitRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularImplicitRefinementCertificate.size := by
  norm_num [SingularImplicitRefinementCertificate.size,
    sampleSingularImplicitRefinementCertificate]

structure SingularImplicitBudgetCertificate where
  criticalWindow : ℕ
  derivativeWindow : ℕ
  perturbationWindow : ℕ
  implicitBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularImplicitBudgetCertificate.controlled
    (c : SingularImplicitBudgetCertificate) : Prop :=
  0 < c.criticalWindow ∧
    0 < c.derivativeWindow ∧
      c.perturbationWindow ≤ c.criticalWindow * c.derivativeWindow + c.slack ∧
        c.implicitBudgetWindow ≤
          c.criticalWindow * c.derivativeWindow + c.perturbationWindow + c.slack

def SingularImplicitBudgetCertificate.budgetControlled
    (c : SingularImplicitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.criticalWindow * c.derivativeWindow + c.perturbationWindow +
      c.implicitBudgetWindow + c.slack

def SingularImplicitBudgetCertificate.Ready
    (c : SingularImplicitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularImplicitBudgetCertificate.size
    (c : SingularImplicitBudgetCertificate) : ℕ :=
  c.criticalWindow * c.derivativeWindow + c.perturbationWindow +
    c.implicitBudgetWindow + c.slack

theorem singularImplicit_budgetCertificate_le_size
    (c : SingularImplicitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularImplicitBudgetCertificate :
    SingularImplicitBudgetCertificate :=
  { criticalWindow := 3
    derivativeWindow := 4
    perturbationWindow := 8
    implicitBudgetWindow := 22
    certificateBudgetWindow := 44
    slack := 2 }

example : sampleSingularImplicitBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularImplicitBudgetCertificate.controlled,
      sampleSingularImplicitBudgetCertificate]
  · norm_num [SingularImplicitBudgetCertificate.budgetControlled,
      sampleSingularImplicitBudgetCertificate]

example :
    sampleSingularImplicitBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularImplicitBudgetCertificate.size := by
  apply singularImplicit_budgetCertificate_le_size
  constructor
  · norm_num [SingularImplicitBudgetCertificate.controlled,
      sampleSingularImplicitBudgetCertificate]
  · norm_num [SingularImplicitBudgetCertificate.budgetControlled,
      sampleSingularImplicitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularImplicitBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularImplicitBudgetCertificate.controlled,
      sampleSingularImplicitBudgetCertificate]
  · norm_num [SingularImplicitBudgetCertificate.budgetControlled,
      sampleSingularImplicitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularImplicitBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularImplicitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularImplicitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularImplicitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularImplicitBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularImplicitSchemas
