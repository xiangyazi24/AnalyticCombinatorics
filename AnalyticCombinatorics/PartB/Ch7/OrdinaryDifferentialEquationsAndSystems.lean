import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Ordinary differential equations and systems
-/

namespace AnalyticCombinatorics.PartB.Ch7.OrdinaryDifferentialEquationsAndSystems

/-- Finite order data for a differential equation with analytic coefficients. -/
structure DifferentialEquationData where
  order : ℕ
  coefficientWindow : ℕ
  singularWindow : ℕ
deriving DecidableEq, Repr

def DifferentialEquationData.regular
    (d : DifferentialEquationData) : Prop :=
  0 < d.order ∧ d.singularWindow ≤ d.order + d.coefficientWindow

theorem differentialEquationData_sample_regular :
    ({ order := 2, coefficientWindow := 5,
       singularWindow := 7 } : DifferentialEquationData).regular := by
  norm_num [DifferentialEquationData.regular]

/-- Cleared recurrence budget obtained from an ODE system. -/
def differentialRecurrenceBudget (order coefficientWindow : ℕ) : ℕ :=
  order + coefficientWindow

theorem differentialRecurrenceBudget_sample :
    differentialRecurrenceBudget 2 5 = 7 := by
  native_decide

structure DifferentialSystemWindow where
  equationWindow : ℕ
  systemWindow : ℕ
  singularWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DifferentialSystemWindow.ready (w : DifferentialSystemWindow) : Prop :=
  0 < w.equationWindow ∧
    w.systemWindow ≤ w.equationWindow + w.singularWindow + w.slack

def sampleDifferentialSystemWindow : DifferentialSystemWindow :=
  { equationWindow := 4, systemWindow := 7, singularWindow := 3, slack := 0 }

example : sampleDifferentialSystemWindow.ready := by
  norm_num [DifferentialSystemWindow.ready, sampleDifferentialSystemWindow]

structure BudgetCertificate where
  equationWindow : ℕ
  systemWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.equationWindow ∧ c.systemWindow ≤ c.equationWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.equationWindow + c.systemWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.equationWindow + c.systemWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { equationWindow := 5, systemWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificate_le_size
    (c : BudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  have h : sampleBudgetCertificate.Ready := by
    constructor
    · norm_num [BudgetCertificate.controlled,
        sampleBudgetCertificate]
    · norm_num [BudgetCertificate.budgetControlled,
        sampleBudgetCertificate]
  exact h.2

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch7.OrdinaryDifferentialEquationsAndSystems
