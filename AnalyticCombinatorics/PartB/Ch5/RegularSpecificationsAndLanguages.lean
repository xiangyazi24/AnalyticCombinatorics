import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Regular specifications and languages
-/

namespace AnalyticCombinatorics.PartB.Ch5.RegularSpecificationsAndLanguages

def regularLanguageStateBudget (states transitions : ℕ) : ℕ :=
  states + transitions

theorem regularLanguageStateBudget_samples :
    regularLanguageStateBudget 3 5 = 8 ∧
      regularLanguageStateBudget 1 0 = 1 := by
  native_decide

structure RegularSpecificationWindow where
  stateWindow : ℕ
  transitionWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSpecificationWindow.ready
    (w : RegularSpecificationWindow) : Prop :=
  0 < w.stateWindow ∧
    w.transitionWindow ≤ w.stateWindow + w.transferWindow + w.slack

def sampleRegularSpecificationWindow : RegularSpecificationWindow :=
  { stateWindow := 3, transitionWindow := 5, transferWindow := 2, slack := 0 }

example : sampleRegularSpecificationWindow.ready := by
  norm_num [RegularSpecificationWindow.ready, sampleRegularSpecificationWindow]

/-- A finite regular-language transition budget is symmetric at the coarse count level. -/
theorem regularLanguageStateBudget_comm (states transitions : ℕ) :
    regularLanguageStateBudget states transitions =
      regularLanguageStateBudget transitions states := by
  unfold regularLanguageStateBudget
  omega

/-- Adding a dead state increments the finite state budget by one. -/
theorem regularLanguageStateBudget_add_dead_state (states transitions : ℕ) :
    regularLanguageStateBudget (states + 1) transitions =
      regularLanguageStateBudget states transitions + 1 := by
  unfold regularLanguageStateBudget
  omega

structure RegularSpecificationsAndLanguagesBudgetCertificate where
  stateWindow : ℕ
  transitionWindow : ℕ
  languageWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSpecificationsAndLanguagesBudgetCertificate.controlled
    (c : RegularSpecificationsAndLanguagesBudgetCertificate) : Prop :=
  0 < c.stateWindow ∧
    c.transitionWindow ≤ c.stateWindow + c.languageWindow + c.slack

def RegularSpecificationsAndLanguagesBudgetCertificate.budgetControlled
    (c : RegularSpecificationsAndLanguagesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stateWindow + c.transitionWindow + c.languageWindow + c.slack

def RegularSpecificationsAndLanguagesBudgetCertificate.Ready
    (c : RegularSpecificationsAndLanguagesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularSpecificationsAndLanguagesBudgetCertificate.size
    (c : RegularSpecificationsAndLanguagesBudgetCertificate) : ℕ :=
  c.stateWindow + c.transitionWindow + c.languageWindow + c.slack

def sampleRegularSpecificationsAndLanguagesBudgetCertificate :
    RegularSpecificationsAndLanguagesBudgetCertificate :=
  { stateWindow := 3
    transitionWindow := 5
    languageWindow := 2
    certificateBudgetWindow := 11
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRegularSpecificationsAndLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSpecificationsAndLanguagesBudgetCertificate.controlled,
      sampleRegularSpecificationsAndLanguagesBudgetCertificate]
  · norm_num [RegularSpecificationsAndLanguagesBudgetCertificate.budgetControlled,
      sampleRegularSpecificationsAndLanguagesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularSpecificationsAndLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularSpecificationsAndLanguagesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRegularSpecificationsAndLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSpecificationsAndLanguagesBudgetCertificate.controlled,
      sampleRegularSpecificationsAndLanguagesBudgetCertificate]
  · norm_num
      [RegularSpecificationsAndLanguagesBudgetCertificate.budgetControlled,
        sampleRegularSpecificationsAndLanguagesBudgetCertificate]

def budgetCertificateListReady
    (data : List RegularSpecificationsAndLanguagesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRegularSpecificationsAndLanguagesBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRegularSpecificationsAndLanguagesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.RegularSpecificationsAndLanguages
