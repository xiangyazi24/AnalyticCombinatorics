import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Perturbation of saddle-point asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationOfSaddlePointAsymptotics

/-- Perturbed saddle datum with finite curvature and error windows. -/
structure SaddlePerturbationData where
  curvature : ℕ
  perturbationScale : ℕ
  errorWindow : ℕ
deriving DecidableEq, Repr

def SaddlePerturbationData.stable (d : SaddlePerturbationData) : Prop :=
  0 < d.curvature ∧ d.errorWindow ≤ d.curvature + d.perturbationScale

theorem saddlePerturbationData_sample_stable :
    ({ curvature := 9, perturbationScale := 2,
       errorWindow := 11 } : SaddlePerturbationData).stable := by
  norm_num [SaddlePerturbationData.stable]

/-- Perturbed Gaussian denominator after clearing constants. -/
def perturbedSaddleDenominator (curvature perturbation : ℕ) : ℕ :=
  curvature + perturbation

theorem perturbedSaddleDenominator_sample :
    perturbedSaddleDenominator 9 2 = 11 := by
  native_decide

structure SaddlePerturbationWindow where
  saddleWindow : ℕ
  perturbationWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SaddlePerturbationWindow.ready
    (w : SaddlePerturbationWindow) : Prop :=
  0 < w.saddleWindow ∧
    w.transferWindow ≤ w.saddleWindow + w.perturbationWindow + w.slack

def sampleSaddlePerturbationWindow : SaddlePerturbationWindow :=
  { saddleWindow := 4, perturbationWindow := 3,
    transferWindow := 7, slack := 0 }

example : sampleSaddlePerturbationWindow.ready := by
  norm_num [SaddlePerturbationWindow.ready, sampleSaddlePerturbationWindow]

structure BudgetCertificate where
  saddleWindow : ℕ
  perturbationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧ c.perturbationWindow ≤ c.saddleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.saddleWindow + c.perturbationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.saddleWindow + c.perturbationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { saddleWindow := 5, perturbationWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch9.PerturbationOfSaddlePointAsymptotics
