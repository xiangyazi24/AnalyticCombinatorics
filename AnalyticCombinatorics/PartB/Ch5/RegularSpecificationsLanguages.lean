import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Regular specifications and languages.

Finite automaton and transfer-matrix bookkeeping for regular language
enumeration.
-/

namespace AnalyticCombinatorics.PartB.Ch5.RegularSpecificationsLanguages

/-- Two-state automaton for words with no consecutive ones. -/
def noAdjacentOnesTransition (state symbol : Fin 2) : Fin 2 :=
  match state.val, symbol.val with
  | 1, 1 => ⟨1, by norm_num⟩
  | _, 1 => ⟨1, by norm_num⟩
  | _, _ => ⟨0, by norm_num⟩

/-- A finite regular specification accepts all transitions except `1 -> 1`. -/
def noAdjacentOnesAllowed (state symbol : Fin 2) : Bool :=
  !(state.val = 1 && symbol.val = 1)

/-- Finite transition-count audit for a regular specification. -/
def regularTransitionCount : ℕ :=
  (List.finRange 2).foldl
    (fun total state =>
      total + (List.finRange 2).foldl
        (fun inner symbol => if noAdjacentOnesAllowed state symbol then inner + 1 else inner) 0)
    0

theorem regularTransitionCount_noAdjacentOnes :
    regularTransitionCount = 3 := by
  unfold regularTransitionCount noAdjacentOnesAllowed
  native_decide

structure RegularSpecificationWindow where
  stateCount : ℕ
  transitionCount : ℕ
  wordLengthDepth : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def regularSpecificationReady (w : RegularSpecificationWindow) : Prop :=
  0 < w.stateCount ∧
    w.wordLengthDepth ≤ w.stateCount + w.transitionCount + w.slack

def regularSpecificationBudget (w : RegularSpecificationWindow) : ℕ :=
  w.stateCount + w.transitionCount + w.wordLengthDepth + w.slack

theorem wordLengthDepth_le_regularBudget
    (w : RegularSpecificationWindow) :
    w.wordLengthDepth ≤ regularSpecificationBudget w := by
  unfold regularSpecificationBudget
  omega

def sampleRegularSpecificationWindow : RegularSpecificationWindow :=
  { stateCount := 4, transitionCount := 7, wordLengthDepth := 9, slack := 1 }

example : regularSpecificationReady sampleRegularSpecificationWindow := by
  norm_num [regularSpecificationReady, sampleRegularSpecificationWindow]

structure RegularSpecificationsLanguagesBudgetCertificate where
  stateWindow : ℕ
  transitionWindow : ℕ
  languageWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularSpecificationsLanguagesBudgetCertificate.controlled
    (c : RegularSpecificationsLanguagesBudgetCertificate) : Prop :=
  0 < c.stateWindow ∧
    c.languageWindow ≤ c.stateWindow + c.transitionWindow + c.slack

def RegularSpecificationsLanguagesBudgetCertificate.budgetControlled
    (c : RegularSpecificationsLanguagesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stateWindow + c.transitionWindow + c.languageWindow + c.slack

def RegularSpecificationsLanguagesBudgetCertificate.Ready
    (c : RegularSpecificationsLanguagesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularSpecificationsLanguagesBudgetCertificate.size
    (c : RegularSpecificationsLanguagesBudgetCertificate) : ℕ :=
  c.stateWindow + c.transitionWindow + c.languageWindow + c.slack

theorem regularSpecificationsLanguages_budgetCertificate_le_size
    (c : RegularSpecificationsLanguagesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRegularSpecificationsLanguagesBudgetCertificate :
    RegularSpecificationsLanguagesBudgetCertificate :=
  { stateWindow := 4
    transitionWindow := 7
    languageWindow := 9
    certificateBudgetWindow := 21
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRegularSpecificationsLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSpecificationsLanguagesBudgetCertificate.controlled,
      sampleRegularSpecificationsLanguagesBudgetCertificate]
  · norm_num [RegularSpecificationsLanguagesBudgetCertificate.budgetControlled,
      sampleRegularSpecificationsLanguagesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularSpecificationsLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularSpecificationsLanguagesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRegularSpecificationsLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularSpecificationsLanguagesBudgetCertificate.controlled,
      sampleRegularSpecificationsLanguagesBudgetCertificate]
  · norm_num [RegularSpecificationsLanguagesBudgetCertificate.budgetControlled,
      sampleRegularSpecificationsLanguagesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RegularSpecificationsLanguagesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRegularSpecificationsLanguagesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRegularSpecificationsLanguagesBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch5.RegularSpecificationsLanguages
