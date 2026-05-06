import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite automaton models.

The file records small transition-table calculations used by rational
language and transfer-matrix examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteAutomatonModels

def transitionLookup (fallback : ℕ) (transitions : List ((ℕ × ℕ) × ℕ))
    (state symbol : ℕ) : ℕ :=
  match transitions.find? (fun entry => entry.1.1 == state && entry.1.2 == symbol) with
  | some entry => entry.2
  | none => fallback

def acceptingState (accepting : List ℕ) (state : ℕ) : Bool :=
  accepting.any (fun s => s == state)

def transitionCount (transitions : List ((ℕ × ℕ) × ℕ)) : ℕ :=
  transitions.length

theorem transitionCount_nil :
    transitionCount [] = 0 := by
  rfl

theorem transitionCount_cons (t : (ℕ × ℕ) × ℕ) (ts : List ((ℕ × ℕ) × ℕ)) :
    transitionCount (t :: ts) = transitionCount ts + 1 := by
  simp [transitionCount]

def sampleTransitions : List ((ℕ × ℕ) × ℕ) :=
  [((0, 0), 0), ((0, 1), 1), ((1, 0), 1), ((1, 1), 0)]

example : transitionLookup 0 sampleTransitions 0 1 = 1 := by
  native_decide

example : transitionLookup 7 sampleTransitions 2 1 = 7 := by
  native_decide

example : acceptingState [1, 3] 1 = true := by
  native_decide

example : transitionCount sampleTransitions = 4 := by
  native_decide

structure AutomatonWindow where
  states : ℕ
  alphabetSize : ℕ
  transitions : ℕ
  acceptingStates : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AutomatonWindow.transitionControlled (w : AutomatonWindow) : Prop :=
  w.transitions ≤ w.states * w.alphabetSize + w.slack

def AutomatonWindow.acceptingControlled (w : AutomatonWindow) : Prop :=
  w.acceptingStates ≤ w.states

def AutomatonWindow.ready (w : AutomatonWindow) : Prop :=
  0 < w.states ∧ 0 < w.alphabetSize ∧
    w.transitionControlled ∧ w.acceptingControlled

def AutomatonWindow.certificate (w : AutomatonWindow) : ℕ :=
  w.states + w.alphabetSize + w.transitions + w.acceptingStates + w.slack

theorem transitions_le_certificate (w : AutomatonWindow) :
    w.transitions ≤ w.certificate := by
  unfold AutomatonWindow.certificate
  omega

def sampleAutomatonWindow : AutomatonWindow :=
  { states := 2, alphabetSize := 2, transitions := 4, acceptingStates := 1, slack := 0 }

example : sampleAutomatonWindow.ready := by
  norm_num [sampleAutomatonWindow, AutomatonWindow.ready,
    AutomatonWindow.transitionControlled, AutomatonWindow.acceptingControlled]


structure FiniteAutomatonModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteAutomatonModelsBudgetCertificate.controlled
    (c : FiniteAutomatonModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteAutomatonModelsBudgetCertificate.budgetControlled
    (c : FiniteAutomatonModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteAutomatonModelsBudgetCertificate.Ready
    (c : FiniteAutomatonModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteAutomatonModelsBudgetCertificate.size
    (c : FiniteAutomatonModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteAutomatonModels_budgetCertificate_le_size
    (c : FiniteAutomatonModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteAutomatonModelsBudgetCertificate :
    FiniteAutomatonModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteAutomatonModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAutomatonModelsBudgetCertificate.controlled,
      sampleFiniteAutomatonModelsBudgetCertificate]
  · norm_num [FiniteAutomatonModelsBudgetCertificate.budgetControlled,
      sampleFiniteAutomatonModelsBudgetCertificate]

example :
    sampleFiniteAutomatonModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAutomatonModelsBudgetCertificate.size := by
  apply finiteAutomatonModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteAutomatonModelsBudgetCertificate.controlled,
      sampleFiniteAutomatonModelsBudgetCertificate]
  · norm_num [FiniteAutomatonModelsBudgetCertificate.budgetControlled,
      sampleFiniteAutomatonModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-automaton certificates. -/
def finiteAutomatonModelsBudgetCertificateListReady
    (data : List FiniteAutomatonModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteAutomatonModelsBudgetCertificateList_readyWindow :
    finiteAutomatonModelsBudgetCertificateListReady
      [sampleFiniteAutomatonModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteAutomatonModelsBudgetCertificateListReady
    sampleFiniteAutomatonModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteAutomatonModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteAutomatonModelsBudgetCertificate.controlled,
      sampleFiniteAutomatonModelsBudgetCertificate]
  · norm_num [FiniteAutomatonModelsBudgetCertificate.budgetControlled,
      sampleFiniteAutomatonModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteAutomatonModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteAutomatonModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteAutomatonModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteAutomatonModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteAutomatonModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteAutomatonModels
