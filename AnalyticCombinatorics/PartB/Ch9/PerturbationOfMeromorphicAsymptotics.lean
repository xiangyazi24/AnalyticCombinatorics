import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Perturbation of meromorphic asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationOfMeromorphicAsymptotics

/-- Pole perturbation data after clearing analytic denominators. -/
structure MeromorphicPerturbationData where
  poleOrder : ℕ
  perturbationDegree : ℕ
  residueScale : ℕ
deriving DecidableEq, Repr

def MeromorphicPerturbationData.valid
    (d : MeromorphicPerturbationData) : Prop :=
  0 < d.poleOrder ∧ d.perturbationDegree ≤ d.residueScale + d.poleOrder

theorem meromorphicPerturbationData_sample_valid :
    ({ poleOrder := 1, perturbationDegree := 4,
       residueScale := 3 } : MeromorphicPerturbationData).valid := by
  norm_num [MeromorphicPerturbationData.valid]

/-- First-order perturbed pole coefficient model. -/
def perturbedPoleCoeff (base perturbation : ℕ) : ℕ :=
  base + perturbation

theorem perturbedPoleCoeff_sample :
    perturbedPoleCoeff 12 5 = 17 := by
  native_decide

structure MeromorphicPerturbationWindow where
  poleWindow : ℕ
  perturbationWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MeromorphicPerturbationWindow.ready
    (w : MeromorphicPerturbationWindow) : Prop :=
  0 < w.poleWindow ∧
    w.transferWindow ≤ w.poleWindow + w.perturbationWindow + w.slack

def sampleMeromorphicPerturbationWindow : MeromorphicPerturbationWindow :=
  { poleWindow := 4, perturbationWindow := 3,
    transferWindow := 7, slack := 0 }

example : sampleMeromorphicPerturbationWindow.ready := by
  norm_num [MeromorphicPerturbationWindow.ready,
    sampleMeromorphicPerturbationWindow]

structure BudgetCertificate where
  poleWindow : ℕ
  perturbationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.poleWindow ∧ c.perturbationWindow ≤ c.poleWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.poleWindow + c.perturbationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.poleWindow + c.perturbationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { poleWindow := 5, perturbationWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch9.PerturbationOfMeromorphicAsymptotics
