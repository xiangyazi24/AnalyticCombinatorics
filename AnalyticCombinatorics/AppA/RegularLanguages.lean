import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Appendix A: regular languages.

Finite automaton, state, transition, and transfer-matrix windows.
-/

namespace AnalyticCombinatorics.AppA.RegularLanguages

/-- Deterministic transition table over a binary alphabet, represented by states `Fin 2`. -/
def togglingTransition (state symbol : Fin 2) : Fin 2 :=
  if symbol.val = 0 then state else ⟨1 - state.val, by omega⟩

/-- Acceptance of even parity after reading a finite binary word sample. -/
def acceptsEvenParity (word : List (Fin 2)) : Bool :=
  let finalState := word.foldl togglingTransition ⟨0, by norm_num⟩
  finalState.val = 0

/-- Finite language count by enumerating binary words of length at most two. -/
def shortEvenParityAcceptedCount : ℕ :=
  [[], [⟨0, by norm_num⟩], [⟨1, by norm_num⟩],
    [⟨0, by norm_num⟩, ⟨0, by norm_num⟩],
    [⟨0, by norm_num⟩, ⟨1, by norm_num⟩],
    [⟨1, by norm_num⟩, ⟨0, by norm_num⟩],
    [⟨1, by norm_num⟩, ⟨1, by norm_num⟩]].foldl
      (fun total word => if acceptsEvenParity word then total + 1 else total) 0

theorem shortEvenParityAcceptedCount_value :
    shortEvenParityAcceptedCount = 4 := by
  unfold shortEvenParityAcceptedCount acceptsEvenParity togglingTransition
  native_decide

/-- Finite audit of parity acceptance on singleton words. -/
def singletonParityAudit : Bool :=
  acceptsEvenParity [⟨0, by norm_num⟩] &&
    !acceptsEvenParity [⟨1, by norm_num⟩]

theorem singletonParityAudit_window :
    singletonParityAudit = true := by
  unfold singletonParityAudit acceptsEvenParity togglingTransition
  native_decide

structure RegularLanguageWindow where
  stateCount : ℕ
  alphabetSize : ℕ
  transitionCount : ℕ
  automatonSlack : ℕ
deriving DecidableEq, Repr

def regularLanguageReady (w : RegularLanguageWindow) : Prop :=
  0 < w.stateCount ∧ 0 < w.alphabetSize ∧
    w.transitionCount ≤ w.stateCount * w.alphabetSize + w.automatonSlack

def regularLanguageBudget (w : RegularLanguageWindow) : ℕ :=
  w.stateCount + w.alphabetSize + w.transitionCount + w.automatonSlack

theorem transitionCount_le_budget
    (w : RegularLanguageWindow) :
    w.transitionCount ≤ regularLanguageBudget w + w.stateCount * w.alphabetSize := by
  unfold regularLanguageBudget
  omega

def sampleRegularLanguageWindow : RegularLanguageWindow :=
  { stateCount := 3, alphabetSize := 2, transitionCount := 6, automatonSlack := 0 }

example : regularLanguageReady sampleRegularLanguageWindow := by
  norm_num [regularLanguageReady, sampleRegularLanguageWindow]

structure RegularLanguagesBudgetCertificate where
  stateWindow : ℕ
  alphabetWindow : ℕ
  transitionWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RegularLanguagesBudgetCertificate.controlled
    (c : RegularLanguagesBudgetCertificate) : Prop :=
  0 < c.stateWindow ∧ 0 < c.alphabetWindow ∧
    c.transitionWindow ≤ c.stateWindow * c.alphabetWindow + c.slack

def RegularLanguagesBudgetCertificate.budgetControlled
    (c : RegularLanguagesBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.stateWindow + c.alphabetWindow + c.transitionWindow + c.slack

def RegularLanguagesBudgetCertificate.Ready
    (c : RegularLanguagesBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RegularLanguagesBudgetCertificate.size
    (c : RegularLanguagesBudgetCertificate) : ℕ :=
  c.stateWindow + c.alphabetWindow + c.transitionWindow + c.slack

theorem regularLanguages_budgetCertificate_le_size
    (c : RegularLanguagesBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleRegularLanguagesBudgetCertificate :
    RegularLanguagesBudgetCertificate :=
  { stateWindow := 3
    alphabetWindow := 2
    transitionWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRegularLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularLanguagesBudgetCertificate.controlled,
      sampleRegularLanguagesBudgetCertificate]
  · norm_num [RegularLanguagesBudgetCertificate.budgetControlled,
      sampleRegularLanguagesBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRegularLanguagesBudgetCertificate.certificateBudgetWindow ≤
      sampleRegularLanguagesBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRegularLanguagesBudgetCertificate.Ready := by
  constructor
  · norm_num [RegularLanguagesBudgetCertificate.controlled,
      sampleRegularLanguagesBudgetCertificate]
  · norm_num [RegularLanguagesBudgetCertificate.budgetControlled,
      sampleRegularLanguagesBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List RegularLanguagesBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleRegularLanguagesBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleRegularLanguagesBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.RegularLanguages
