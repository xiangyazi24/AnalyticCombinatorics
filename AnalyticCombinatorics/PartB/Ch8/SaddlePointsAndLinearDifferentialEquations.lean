import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Saddle-points and linear differential equations
-/

namespace AnalyticCombinatorics.PartB.Ch8.SaddlePointsAndLinearDifferentialEquations

/-- Recurrence data extracted from a saddle-point ODE representation. -/
structure SaddleRecurrenceData where
  order : ℕ
  saddleScale : ℕ
  coefficientWindow : ℕ
deriving DecidableEq, Repr

def SaddleRecurrenceData.ready (d : SaddleRecurrenceData) : Prop :=
  0 < d.order ∧ d.coefficientWindow ≤ d.order + d.saddleScale

theorem saddleRecurrenceData_sample_ready :
    ({ order := 2, saddleScale := 5,
       coefficientWindow := 7 } : SaddleRecurrenceData).ready := by
  norm_num [SaddleRecurrenceData.ready]

/-- Finite ODE-to-saddle transfer budget. -/
def saddleDifferentialBudget (order saddleScale : ℕ) : ℕ :=
  order + saddleScale

theorem saddleDifferentialBudget_sample :
    saddleDifferentialBudget 2 5 = 7 := by
  native_decide

structure SaddleDifferentialWindow where
  saddleWindow : ℕ
  differentialWindow : ℕ
  recurrenceWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddleDifferentialWindow.ready (w : SaddleDifferentialWindow) : Prop :=
  0 < w.saddleWindow ∧
    w.recurrenceWindow ≤ w.saddleWindow + w.differentialWindow + w.slack

def sampleSaddleDifferentialWindow : SaddleDifferentialWindow :=
  { saddleWindow := 4, differentialWindow := 3,
    recurrenceWindow := 7, slack := 0 }

example : sampleSaddleDifferentialWindow.ready := by
  norm_num [SaddleDifferentialWindow.ready, sampleSaddleDifferentialWindow]

structure BudgetCertificate where
  saddleWindow : ℕ
  differentialWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.differentialWindow ≤ c.saddleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.saddleWindow + c.differentialWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.saddleWindow + c.differentialWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { saddleWindow := 5, differentialWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch8.SaddlePointsAndLinearDifferentialEquations
