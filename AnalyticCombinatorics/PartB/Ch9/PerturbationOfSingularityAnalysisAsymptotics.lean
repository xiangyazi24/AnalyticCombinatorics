import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Perturbation of singularity analysis asymptotics
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationOfSingularityAnalysisAsymptotics

/-- Perturbed local singular expansion after clearing exponents. -/
structure SingularityPerturbationData where
  baseExponent : ℕ
  perturbationExponent : ℕ
  transferScale : ℕ
deriving DecidableEq, Repr

def SingularityPerturbationData.transferReady
    (d : SingularityPerturbationData) : Prop :=
  d.baseExponent + d.perturbationExponent ≤ d.transferScale

theorem singularityPerturbationData_sample_ready :
    ({ baseExponent := 2, perturbationExponent := 3,
       transferScale := 5 } : SingularityPerturbationData).transferReady := by
  norm_num [SingularityPerturbationData.transferReady]

/-- Perturbed transfer envelope in a finite coefficient window. -/
def perturbedTransferEnvelope (scale n : ℕ) : ℕ :=
  scale * (n + 1)

theorem perturbedTransferEnvelope_sample :
    perturbedTransferEnvelope 5 4 = 25 := by
  native_decide

structure SingularityPerturbationWindow where
  singularityWindow : ℕ
  perturbationWindow : ℕ
  transferWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SingularityPerturbationWindow.ready
    (w : SingularityPerturbationWindow) : Prop :=
  0 < w.singularityWindow ∧
    w.transferWindow ≤ w.singularityWindow + w.perturbationWindow + w.slack

def sampleSingularityPerturbationWindow : SingularityPerturbationWindow :=
  { singularityWindow := 4, perturbationWindow := 3,
    transferWindow := 7, slack := 0 }

example : sampleSingularityPerturbationWindow.ready := by
  norm_num [SingularityPerturbationWindow.ready,
    sampleSingularityPerturbationWindow]

structure BudgetCertificate where
  singularityWindow : ℕ
  perturbationWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.singularityWindow ∧
    c.perturbationWindow ≤ c.singularityWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.perturbationWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.singularityWindow + c.perturbationWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { singularityWindow := 5, perturbationWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch9.PerturbationOfSingularityAnalysisAsymptotics
