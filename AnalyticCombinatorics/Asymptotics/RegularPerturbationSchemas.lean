import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Regular perturbation schema bookkeeping.

The finite record tracks base term, perturbation size, and admissible error
budget.
-/

namespace AnalyticCombinatorics.Asymptotics.RegularPerturbationSchemas

structure RegularPerturbationData where
  baseTerm : ℕ
  perturbationTerm : ℕ
  admissibleError : ℕ
deriving DecidableEq, Repr

def perturbationSmall (d : RegularPerturbationData) : Prop :=
  d.perturbationTerm ≤ d.baseTerm

def errorAbsorbed (d : RegularPerturbationData) : Prop :=
  d.admissibleError ≤ d.baseTerm + d.perturbationTerm

def regularPerturbationReady (d : RegularPerturbationData) : Prop :=
  perturbationSmall d ∧ errorAbsorbed d

def perturbationBudget (d : RegularPerturbationData) : ℕ :=
  d.baseTerm + d.perturbationTerm + d.admissibleError

theorem regularPerturbationReady.small {d : RegularPerturbationData}
    (h : regularPerturbationReady d) :
    perturbationSmall d ∧ errorAbsorbed d ∧ d.admissibleError ≤ perturbationBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold perturbationBudget
  omega

theorem baseTerm_le_budget (d : RegularPerturbationData) :
    d.baseTerm ≤ perturbationBudget d := by
  unfold perturbationBudget
  omega

def sampleRegularPerturbation : RegularPerturbationData :=
  { baseTerm := 10, perturbationTerm := 3, admissibleError := 4 }

example : regularPerturbationReady sampleRegularPerturbation := by
  norm_num
    [regularPerturbationReady, perturbationSmall, errorAbsorbed,
      sampleRegularPerturbation]

example : perturbationBudget sampleRegularPerturbation = 17 := by
  native_decide

/-- Finite executable readiness audit for regular perturbation data. -/
def regularPerturbationDataListReady
    (data : List RegularPerturbationData) : Bool :=
  data.all fun d =>
    d.perturbationTerm ≤ d.baseTerm &&
      d.admissibleError ≤ d.baseTerm + d.perturbationTerm

theorem regularPerturbationDataList_readyWindow :
    regularPerturbationDataListReady
      [{ baseTerm := 8, perturbationTerm := 2, admissibleError := 3 },
       { baseTerm := 10, perturbationTerm := 3, admissibleError := 4 }] = true := by
  unfold regularPerturbationDataListReady
  native_decide

/-- A certificate window for regular perturbation bookkeeping. -/
structure RegularPerturbationCertificateWindow where
  baseWindow : ℕ
  perturbationWindow : ℕ
  errorWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Local control for perturbation and error windows. -/
def regularPerturbationCertificateControlled
    (w : RegularPerturbationCertificateWindow) : Prop :=
  w.perturbationWindow ≤ w.baseWindow + w.slack ∧
    w.errorWindow ≤ w.baseWindow + w.perturbationWindow + w.slack

/-- Readiness for a regular perturbation certificate window. -/
def regularPerturbationCertificateReady
    (w : RegularPerturbationCertificateWindow) : Prop :=
  0 < w.baseWindow ∧
    regularPerturbationCertificateControlled w ∧
      w.certificateBudget ≤
        w.baseWindow + w.perturbationWindow + w.errorWindow + w.slack

/-- Total size of the regular perturbation certificate. -/
def regularPerturbationCertificate
    (w : RegularPerturbationCertificateWindow) : ℕ :=
  w.baseWindow + w.perturbationWindow + w.errorWindow +
    w.certificateBudget + w.slack

theorem regularPerturbationCertificate_budget_le_certificate
    (w : RegularPerturbationCertificateWindow)
    (h : regularPerturbationCertificateReady w) :
    w.certificateBudget ≤ regularPerturbationCertificate w := by
  rcases h with ⟨_, _, hbudget⟩
  unfold regularPerturbationCertificate
  omega

def sampleRegularPerturbationCertificateWindow :
    RegularPerturbationCertificateWindow where
  baseWindow := 10
  perturbationWindow := 4
  errorWindow := 6
  certificateBudget := 18
  slack := 2

example :
    regularPerturbationCertificateReady
      sampleRegularPerturbationCertificateWindow := by
  norm_num [regularPerturbationCertificateReady,
    regularPerturbationCertificateControlled,
    sampleRegularPerturbationCertificateWindow]

example :
    sampleRegularPerturbationCertificateWindow.certificateBudget ≤
      regularPerturbationCertificate
        sampleRegularPerturbationCertificateWindow := by
  apply regularPerturbationCertificate_budget_le_certificate
  norm_num [regularPerturbationCertificateReady,
    regularPerturbationCertificateControlled,
    sampleRegularPerturbationCertificateWindow]

structure RegularPerturbationRefinementCertificate where
  baseWindow : ℕ
  perturbationWindow : ℕ
  errorWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularPerturbationRefinementCertificate.localControlled
    (c : RegularPerturbationRefinementCertificate) : Prop :=
  c.perturbationWindow ≤ c.baseWindow + c.slack ∧
    c.errorWindow ≤ c.baseWindow + c.perturbationWindow + c.slack

def RegularPerturbationRefinementCertificate.certificateBudgetControlled
    (c : RegularPerturbationRefinementCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.perturbationWindow + c.errorWindow + c.slack

def regularPerturbationRefinementReady
    (c : RegularPerturbationRefinementCertificate) : Prop :=
  0 < c.baseWindow ∧ c.localControlled ∧ c.certificateBudgetControlled

def RegularPerturbationRefinementCertificate.size
    (c : RegularPerturbationRefinementCertificate) : ℕ :=
  c.baseWindow + c.perturbationWindow + c.errorWindow + c.slack

theorem regularPerturbation_certificateBudgetWindow_le_size
    {c : RegularPerturbationRefinementCertificate}
    (h : regularPerturbationRefinementReady c) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, _, hbudget⟩
  exact hbudget

def sampleRegularPerturbationRefinementCertificate :
    RegularPerturbationRefinementCertificate :=
  { baseWindow := 10, perturbationWindow := 4, errorWindow := 6,
    certificateBudgetWindow := 22, slack := 2 }

example : regularPerturbationRefinementReady
    sampleRegularPerturbationRefinementCertificate := by
  norm_num [regularPerturbationRefinementReady,
    RegularPerturbationRefinementCertificate.localControlled,
    RegularPerturbationRefinementCertificate.certificateBudgetControlled,
    sampleRegularPerturbationRefinementCertificate]

example :
    sampleRegularPerturbationRefinementCertificate.certificateBudgetWindow ≤
      sampleRegularPerturbationRefinementCertificate.size := by
  norm_num [RegularPerturbationRefinementCertificate.size,
    sampleRegularPerturbationRefinementCertificate]

structure RegularPerturbationBudgetCertificate where
  baseWindow : ℕ
  perturbationWindow : ℕ
  errorWindow : ℕ
  perturbationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularPerturbationBudgetCertificate.controlled
    (c : RegularPerturbationBudgetCertificate) : Prop :=
  0 < c.baseWindow ∧
    c.perturbationWindow ≤ c.baseWindow + c.slack ∧
      c.errorWindow ≤ c.baseWindow + c.perturbationWindow + c.slack ∧
        c.perturbationBudgetWindow ≤
          c.baseWindow + c.perturbationWindow + c.errorWindow + c.slack

def RegularPerturbationBudgetCertificate.budgetControlled
    (c : RegularPerturbationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.baseWindow + c.perturbationWindow + c.errorWindow +
      c.perturbationBudgetWindow + c.slack

def RegularPerturbationBudgetCertificate.Ready
    (c : RegularPerturbationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularPerturbationBudgetCertificate.size
    (c : RegularPerturbationBudgetCertificate) : ℕ :=
  c.baseWindow + c.perturbationWindow + c.errorWindow +
    c.perturbationBudgetWindow + c.slack

theorem regularPerturbation_budgetCertificate_le_size
    (c : RegularPerturbationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRegularPerturbationBudgetCertificate :
    RegularPerturbationBudgetCertificate :=
  { baseWindow := 10
    perturbationWindow := 4
    errorWindow := 6
    perturbationBudgetWindow := 22
    certificateBudgetWindow := 44
    slack := 2 }

example : sampleRegularPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularPerturbationBudgetCertificate.controlled,
      sampleRegularPerturbationBudgetCertificate]
  · norm_num [RegularPerturbationBudgetCertificate.budgetControlled,
      sampleRegularPerturbationBudgetCertificate]

example :
    sampleRegularPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularPerturbationBudgetCertificate.size := by
  apply regularPerturbation_budgetCertificate_le_size
  constructor
  · norm_num [RegularPerturbationBudgetCertificate.controlled,
      sampleRegularPerturbationBudgetCertificate]
  · norm_num [RegularPerturbationBudgetCertificate.budgetControlled,
      sampleRegularPerturbationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRegularPerturbationBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularPerturbationBudgetCertificate.controlled,
      sampleRegularPerturbationBudgetCertificate]
  · norm_num [RegularPerturbationBudgetCertificate.budgetControlled,
      sampleRegularPerturbationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularPerturbationBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularPerturbationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RegularPerturbationBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRegularPerturbationBudgetCertificate] =
      true := by
  unfold budgetCertificateListReady sampleRegularPerturbationBudgetCertificate
  native_decide

end AnalyticCombinatorics.Asymptotics.RegularPerturbationSchemas
