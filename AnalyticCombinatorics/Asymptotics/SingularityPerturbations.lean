import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perturbation budgets around dominant singularities.

The elementary inequalities here model the finite side of uniform
singularity perturbation arguments.
-/

namespace AnalyticCombinatorics.Asymptotics.SingularityPerturbations

structure PerturbationBudget where
  baseRadius : ℕ
  radiusShift : ℕ
  errorMargin : ℕ
deriving DecidableEq, Repr

def perturbationStable (p : PerturbationBudget) : Prop :=
  p.radiusShift + p.errorMargin ≤ p.baseRadius

def remainingRadius (p : PerturbationBudget) : ℕ :=
  p.baseRadius - (p.radiusShift + p.errorMargin)

theorem perturbationStable_error_le {p : PerturbationBudget}
    (h : perturbationStable p) :
    p.errorMargin ≤ p.baseRadius := by
  unfold perturbationStable at h
  omega

theorem perturbationStable_shift_le {p : PerturbationBudget}
    (h : perturbationStable p) :
    p.radiusShift ≤ p.baseRadius := by
  unfold perturbationStable at h
  omega

def samplePerturbation : PerturbationBudget :=
  { baseRadius := 10, radiusShift := 3, errorMargin := 2 }

example : perturbationStable samplePerturbation := by
  norm_num [perturbationStable, samplePerturbation]

example : remainingRadius samplePerturbation = 5 := by
  native_decide

/-- Finite executable readiness audit for singularity perturbation budgets. -/
def perturbationBudgetListReady (budgets : List PerturbationBudget) : Bool :=
  budgets.all fun p => p.radiusShift + p.errorMargin ≤ p.baseRadius

theorem perturbationBudgetList_readyWindow :
    perturbationBudgetListReady
      [{ baseRadius := 8, radiusShift := 2, errorMargin := 1 },
       { baseRadius := 10, radiusShift := 3, errorMargin := 2 }] = true := by
  unfold perturbationBudgetListReady
  native_decide

structure SingularityPerturbationWindow where
  baseRadius : ℕ
  perturbationRadius : ℕ
  coefficientError : ℕ
  stabilitySlack : ℕ
deriving DecidableEq, Repr

def SingularityPerturbationWindow.radiusControlled (w : SingularityPerturbationWindow) : Prop :=
  w.perturbationRadius + w.coefficientError ≤ w.baseRadius + w.stabilitySlack

def SingularityPerturbationWindow.nonzeroBase (w : SingularityPerturbationWindow) : Prop :=
  0 < w.baseRadius

def SingularityPerturbationWindow.ready (w : SingularityPerturbationWindow) : Prop :=
  w.nonzeroBase ∧ w.radiusControlled

def SingularityPerturbationWindow.certificate (w : SingularityPerturbationWindow) : ℕ :=
  w.baseRadius + w.perturbationRadius + w.coefficientError + w.stabilitySlack

theorem coefficientError_le_certificate (w : SingularityPerturbationWindow) :
    w.coefficientError ≤ w.certificate := by
  unfold SingularityPerturbationWindow.certificate
  omega

def sampleSingularityPerturbationWindow : SingularityPerturbationWindow :=
  { baseRadius := 10, perturbationRadius := 3, coefficientError := 2, stabilitySlack := 0 }

example : sampleSingularityPerturbationWindow.ready := by
  norm_num [sampleSingularityPerturbationWindow, SingularityPerturbationWindow.ready,
    SingularityPerturbationWindow.nonzeroBase,
    SingularityPerturbationWindow.radiusControlled]

/-- A refinement certificate for singularity perturbation windows. -/
structure SingularityPerturbationCertificate where
  baseWindow : ℕ
  perturbationWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Perturbation and error windows stay inside the base window up to slack. -/
def singularityPerturbationCertificateControlled
    (w : SingularityPerturbationCertificate) : Prop :=
  0 < w.baseWindow ∧
    w.perturbationWindow + w.errorWindow ≤ w.baseWindow + w.slack

/-- Readiness for a singularity perturbation certificate. -/
def singularityPerturbationCertificateReady
    (w : SingularityPerturbationCertificate) : Prop :=
  singularityPerturbationCertificateControlled w ∧
    w.certificateBudget ≤ w.baseWindow + w.perturbationWindow + w.errorWindow + w.slack

/-- Total size of a singularity perturbation certificate. -/
def singularityPerturbationCertificateSize
    (w : SingularityPerturbationCertificate) : ℕ :=
  w.baseWindow + w.perturbationWindow + w.errorWindow +
    w.certificateBudget + w.slack

theorem singularityPerturbationCertificate_budget_le_size
    (w : SingularityPerturbationCertificate)
    (h : singularityPerturbationCertificateReady w) :
    w.certificateBudget ≤ singularityPerturbationCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold singularityPerturbationCertificateSize
  omega

def sampleSingularityPerturbationCertificate :
    SingularityPerturbationCertificate where
  baseWindow := 10
  perturbationWindow := 3
  errorWindow := 2
  certificateBudget := 15
  slack := 0

example :
    singularityPerturbationCertificateReady
      sampleSingularityPerturbationCertificate := by
  norm_num [singularityPerturbationCertificateReady,
    singularityPerturbationCertificateControlled,
    sampleSingularityPerturbationCertificate]

example :
    sampleSingularityPerturbationCertificate.certificateBudget ≤
      singularityPerturbationCertificateSize
        sampleSingularityPerturbationCertificate := by
  apply singularityPerturbationCertificate_budget_le_size
  norm_num [singularityPerturbationCertificateReady,
    singularityPerturbationCertificateControlled,
    sampleSingularityPerturbationCertificate]

/-- A refinement certificate with the perturbation budget separated from size. -/
structure SingularityPerturbationRefinementCertificate where
  baseWindow : ℕ
  perturbationWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def SingularityPerturbationRefinementCertificate.radiusControlled
    (cert : SingularityPerturbationRefinementCertificate) : Prop :=
  0 < cert.baseWindow ∧
    cert.perturbationWindow + cert.errorWindow ≤ cert.baseWindow + cert.slack

def SingularityPerturbationRefinementCertificate.budgetControlled
    (cert : SingularityPerturbationRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.baseWindow + cert.perturbationWindow + cert.errorWindow + cert.slack

def singularityPerturbationRefinementReady
    (cert : SingularityPerturbationRefinementCertificate) : Prop :=
  cert.radiusControlled ∧ cert.budgetControlled

def SingularityPerturbationRefinementCertificate.size
    (cert : SingularityPerturbationRefinementCertificate) : ℕ :=
  cert.baseWindow + cert.perturbationWindow + cert.errorWindow + cert.slack

theorem singularityPerturbation_certificateBudgetWindow_le_size
    (cert : SingularityPerturbationRefinementCertificate)
    (h : singularityPerturbationRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityPerturbationRefinementCertificate :
    SingularityPerturbationRefinementCertificate where
  baseWindow := 10
  perturbationWindow := 3
  errorWindow := 2
  certificateBudgetWindow := 15
  slack := 0

example :
    singularityPerturbationRefinementReady
      sampleSingularityPerturbationRefinementCertificate := by
  norm_num [singularityPerturbationRefinementReady,
    SingularityPerturbationRefinementCertificate.radiusControlled,
    SingularityPerturbationRefinementCertificate.budgetControlled,
    sampleSingularityPerturbationRefinementCertificate]

example :
    sampleSingularityPerturbationRefinementCertificate.certificateBudgetWindow ≤
      sampleSingularityPerturbationRefinementCertificate.size := by
  apply singularityPerturbation_certificateBudgetWindow_le_size
  norm_num [singularityPerturbationRefinementReady,
    SingularityPerturbationRefinementCertificate.radiusControlled,
    SingularityPerturbationRefinementCertificate.budgetControlled,
    sampleSingularityPerturbationRefinementCertificate]


structure SingularityPerturbationsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityPerturbationsBudgetCertificate.controlled
    (c : SingularityPerturbationsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def SingularityPerturbationsBudgetCertificate.budgetControlled
    (c : SingularityPerturbationsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def SingularityPerturbationsBudgetCertificate.Ready
    (c : SingularityPerturbationsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SingularityPerturbationsBudgetCertificate.size
    (c : SingularityPerturbationsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem singularityPerturbations_budgetCertificate_le_size
    (c : SingularityPerturbationsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleSingularityPerturbationsBudgetCertificate :
    SingularityPerturbationsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleSingularityPerturbationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityPerturbationsBudgetCertificate.controlled,
      sampleSingularityPerturbationsBudgetCertificate]
  · norm_num [SingularityPerturbationsBudgetCertificate.budgetControlled,
      sampleSingularityPerturbationsBudgetCertificate]

example :
    sampleSingularityPerturbationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityPerturbationsBudgetCertificate.size := by
  apply singularityPerturbations_budgetCertificate_le_size
  constructor
  · norm_num [SingularityPerturbationsBudgetCertificate.controlled,
      sampleSingularityPerturbationsBudgetCertificate]
  · norm_num [SingularityPerturbationsBudgetCertificate.budgetControlled,
      sampleSingularityPerturbationsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleSingularityPerturbationsBudgetCertificate.Ready := by
  constructor
  · norm_num [SingularityPerturbationsBudgetCertificate.controlled,
      sampleSingularityPerturbationsBudgetCertificate]
  · norm_num [SingularityPerturbationsBudgetCertificate.budgetControlled,
      sampleSingularityPerturbationsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSingularityPerturbationsBudgetCertificate.certificateBudgetWindow ≤
      sampleSingularityPerturbationsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List SingularityPerturbationsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleSingularityPerturbationsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleSingularityPerturbationsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.SingularityPerturbations
