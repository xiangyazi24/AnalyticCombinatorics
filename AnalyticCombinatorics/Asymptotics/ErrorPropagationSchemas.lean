import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Error-propagation schemas.

The file records finite rules for adding and composing asymptotic error
budgets.
-/

namespace AnalyticCombinatorics.Asymptotics.ErrorPropagationSchemas

structure ErrorBudget where
  mainError : ℕ
  secondaryError : ℕ
  propagatedError : ℕ
deriving DecidableEq, Repr

def propagationControlled (e : ErrorBudget) : Prop :=
  e.mainError + e.secondaryError ≤ e.propagatedError

def totalInputError (e : ErrorBudget) : ℕ :=
  e.mainError + e.secondaryError

def remainingErrorSlack (e : ErrorBudget) : ℕ :=
  e.propagatedError - totalInputError e

theorem propagationControlled.input_le {e : ErrorBudget}
    (h : propagationControlled e) :
    totalInputError e ≤ e.propagatedError := by
  simpa [propagationControlled, totalInputError] using h

theorem remainingErrorSlack_add {e : ErrorBudget}
    (h : propagationControlled e) :
    remainingErrorSlack e + totalInputError e = e.propagatedError := by
  unfold remainingErrorSlack propagationControlled totalInputError at *
  omega

def sampleErrorBudget : ErrorBudget :=
  { mainError := 3, secondaryError := 4, propagatedError := 10 }

example : propagationControlled sampleErrorBudget := by
  norm_num [propagationControlled, sampleErrorBudget]

example : remainingErrorSlack sampleErrorBudget = 3 := by
  native_decide

/-- Finite executable readiness audit for error propagation budgets. -/
def errorBudgetListReady (budgets : List ErrorBudget) : Bool :=
  budgets.all fun e => e.mainError + e.secondaryError ≤ e.propagatedError

theorem errorBudgetList_readyWindow :
    errorBudgetListReady
      [{ mainError := 1, secondaryError := 2, propagatedError := 4 },
       { mainError := 3, secondaryError := 4, propagatedError := 10 }] = true := by
  unfold errorBudgetListReady
  native_decide

structure ErrorPropagationWindow where
  primaryError : ℕ
  secondaryError : ℕ
  propagatedError : ℕ
  compositionSlack : ℕ
deriving DecidableEq, Repr

def ErrorPropagationWindow.inputError (w : ErrorPropagationWindow) : ℕ :=
  w.primaryError + w.secondaryError

def ErrorPropagationWindow.ready (w : ErrorPropagationWindow) : Prop :=
  w.inputError ≤ w.propagatedError + w.compositionSlack

def ErrorPropagationWindow.certificate (w : ErrorPropagationWindow) : ℕ :=
  w.primaryError + w.secondaryError + w.propagatedError + w.compositionSlack

theorem propagatedError_le_certificate (w : ErrorPropagationWindow) :
    w.propagatedError ≤ w.certificate := by
  unfold ErrorPropagationWindow.certificate
  omega

def sampleErrorPropagationWindow : ErrorPropagationWindow :=
  { primaryError := 3, secondaryError := 4, propagatedError := 10, compositionSlack := 0 }

example : sampleErrorPropagationWindow.ready := by
  norm_num [sampleErrorPropagationWindow, ErrorPropagationWindow.ready,
    ErrorPropagationWindow.inputError]

/-- A refinement certificate for error propagation windows. -/
structure ErrorPropagationCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  propagatedWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- Propagated error absorbs primary and secondary errors up to slack. -/
def errorPropagationCertificateControlled
    (w : ErrorPropagationCertificate) : Prop :=
  w.primaryWindow + w.secondaryWindow ≤ w.propagatedWindow + w.slack

/-- Readiness for an error propagation certificate. -/
def errorPropagationCertificateReady
    (w : ErrorPropagationCertificate) : Prop :=
  errorPropagationCertificateControlled w ∧
    w.certificateBudget ≤ w.primaryWindow + w.propagatedWindow + w.slack

/-- Total size of an error propagation certificate. -/
def errorPropagationCertificateSize
    (w : ErrorPropagationCertificate) : ℕ :=
  w.primaryWindow + w.secondaryWindow + w.propagatedWindow +
    w.certificateBudget + w.slack

theorem errorPropagationCertificate_budget_le_size
    (w : ErrorPropagationCertificate)
    (h : errorPropagationCertificateReady w) :
    w.certificateBudget ≤ errorPropagationCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold errorPropagationCertificateSize
  omega

def sampleErrorPropagationCertificate : ErrorPropagationCertificate where
  primaryWindow := 3
  secondaryWindow := 4
  propagatedWindow := 10
  certificateBudget := 13
  slack := 0

example :
    errorPropagationCertificateReady sampleErrorPropagationCertificate := by
  norm_num [errorPropagationCertificateReady,
    errorPropagationCertificateControlled, sampleErrorPropagationCertificate]

example :
    sampleErrorPropagationCertificate.certificateBudget ≤
      errorPropagationCertificateSize sampleErrorPropagationCertificate := by
  apply errorPropagationCertificate_budget_le_size
  norm_num [errorPropagationCertificateReady,
    errorPropagationCertificateControlled, sampleErrorPropagationCertificate]

/-- A refinement certificate with the bookkeeping budget kept external to size. -/
structure ErrorPropagationRefinementCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  propagatedWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ

def ErrorPropagationRefinementCertificate.propagationControlled
    (cert : ErrorPropagationRefinementCertificate) : Prop :=
  cert.primaryWindow + cert.secondaryWindow ≤ cert.propagatedWindow + cert.slack

def ErrorPropagationRefinementCertificate.budgetControlled
    (cert : ErrorPropagationRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.primaryWindow + cert.secondaryWindow + cert.propagatedWindow + cert.slack

def errorPropagationRefinementReady
    (cert : ErrorPropagationRefinementCertificate) : Prop :=
  cert.propagationControlled ∧ cert.budgetControlled

def ErrorPropagationRefinementCertificate.size
    (cert : ErrorPropagationRefinementCertificate) : ℕ :=
  cert.primaryWindow + cert.secondaryWindow + cert.propagatedWindow + cert.slack

theorem errorPropagation_certificateBudgetWindow_le_size
    (cert : ErrorPropagationRefinementCertificate)
    (h : errorPropagationRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleErrorPropagationRefinementCertificate :
    ErrorPropagationRefinementCertificate where
  primaryWindow := 3
  secondaryWindow := 4
  propagatedWindow := 10
  certificateBudgetWindow := 17
  slack := 0

example :
    errorPropagationRefinementReady sampleErrorPropagationRefinementCertificate := by
  norm_num [errorPropagationRefinementReady,
    ErrorPropagationRefinementCertificate.propagationControlled,
    ErrorPropagationRefinementCertificate.budgetControlled,
    sampleErrorPropagationRefinementCertificate]

example :
    sampleErrorPropagationRefinementCertificate.certificateBudgetWindow ≤
      sampleErrorPropagationRefinementCertificate.size := by
  apply errorPropagation_certificateBudgetWindow_le_size
  norm_num [errorPropagationRefinementReady,
    ErrorPropagationRefinementCertificate.propagationControlled,
    ErrorPropagationRefinementCertificate.budgetControlled,
    sampleErrorPropagationRefinementCertificate]

structure ErrorPropagationBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  propagatedWindow : ℕ
  propagationBudgetWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ErrorPropagationBudgetCertificate.controlled
    (c : ErrorPropagationBudgetCertificate) : Prop :=
  c.primaryWindow + c.secondaryWindow ≤ c.propagatedWindow + c.slack ∧
    c.propagationBudgetWindow ≤
      c.primaryWindow + c.secondaryWindow + c.propagatedWindow + c.slack

def ErrorPropagationBudgetCertificate.budgetControlled
    (c : ErrorPropagationBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.primaryWindow + c.secondaryWindow + c.propagatedWindow +
      c.propagationBudgetWindow + c.slack

def ErrorPropagationBudgetCertificate.Ready
    (c : ErrorPropagationBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ErrorPropagationBudgetCertificate.size
    (c : ErrorPropagationBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.propagatedWindow +
    c.propagationBudgetWindow + c.slack

theorem errorPropagation_budgetCertificate_le_size
    (c : ErrorPropagationBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleErrorPropagationBudgetCertificate :
    ErrorPropagationBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 4
    propagatedWindow := 10
    propagationBudgetWindow := 17
    certificateBudgetWindow := 34
    slack := 0 }

example : sampleErrorPropagationBudgetCertificate.Ready := by
  constructor
  · norm_num [ErrorPropagationBudgetCertificate.controlled,
      sampleErrorPropagationBudgetCertificate]
  · norm_num [ErrorPropagationBudgetCertificate.budgetControlled,
      sampleErrorPropagationBudgetCertificate]

example :
    sampleErrorPropagationBudgetCertificate.certificateBudgetWindow ≤
      sampleErrorPropagationBudgetCertificate.size := by
  apply errorPropagation_budgetCertificate_le_size
  constructor
  · norm_num [ErrorPropagationBudgetCertificate.controlled,
      sampleErrorPropagationBudgetCertificate]
  · norm_num [ErrorPropagationBudgetCertificate.budgetControlled,
      sampleErrorPropagationBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleErrorPropagationBudgetCertificate.Ready := by
  constructor
  · norm_num [ErrorPropagationBudgetCertificate.controlled,
      sampleErrorPropagationBudgetCertificate]
  · norm_num [ErrorPropagationBudgetCertificate.budgetControlled,
      sampleErrorPropagationBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleErrorPropagationBudgetCertificate.certificateBudgetWindow ≤
      sampleErrorPropagationBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List ErrorPropagationBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleErrorPropagationBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleErrorPropagationBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.ErrorPropagationSchemas
