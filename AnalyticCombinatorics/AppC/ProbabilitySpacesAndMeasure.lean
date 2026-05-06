import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Probability spaces and measure
-/

namespace AnalyticCombinatorics.AppC.ProbabilitySpacesAndMeasure

/-- Finite event measure over `0, ..., N`. -/
def finiteMeasure (mass : ℕ → ℚ) (event : ℕ → Bool) (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun total k => if event k then total + mass k else total) 0

def wholeEvent (_ : ℕ) : Bool := true

def emptyEvent (_ : ℕ) : Bool := false

theorem finiteMeasure_empty (mass : ℕ → ℚ) (N : ℕ) :
    finiteMeasure mass emptyEvent N = 0 := by
  unfold finiteMeasure emptyEvent
  simp

def pointMassZero : ℕ → ℚ
  | 0 => 1
  | _ => 0

theorem finiteMeasure_pointMass_whole :
    finiteMeasure pointMassZero wholeEvent 4 = 1 := by
  unfold finiteMeasure pointMassZero wholeEvent
  native_decide

def singletonEvent (target : ℕ) (n : ℕ) : Bool :=
  n == target

theorem finiteMeasure_pointMass_singleton_zero :
    finiteMeasure pointMassZero (singletonEvent 0) 4 = 1 := by
  unfold finiteMeasure pointMassZero singletonEvent
  native_decide

theorem finiteMeasure_pointMass_singleton_one :
    finiteMeasure pointMassZero (singletonEvent 1) 4 = 0 := by
  unfold finiteMeasure pointMassZero singletonEvent
  native_decide

example : singletonEvent 2 2 = true := by
  unfold singletonEvent
  native_decide

example : finiteMeasure pointMassZero (singletonEvent 0) 0 = 1 := by
  unfold finiteMeasure pointMassZero singletonEvent
  native_decide

structure BudgetCertificate where
  spaceWindow : ℕ
  measureWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.spaceWindow ∧ c.measureWindow ≤ c.spaceWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.spaceWindow + c.measureWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.spaceWindow + c.measureWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { spaceWindow := 5, measureWindow := 6, certificateBudgetWindow := 12,
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.ProbabilitySpacesAndMeasure
