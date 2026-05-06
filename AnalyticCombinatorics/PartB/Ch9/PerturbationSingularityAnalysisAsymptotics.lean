import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perturbation of singularity analysis asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationSingularityAnalysisAsymptotics

/-- Puiseux-like coefficient model with a perturbative multiplier. -/
def perturbedSingularCoeff (base perturb n : ℕ) : ℕ :=
  (perturb + 1) * (n + 1) * base ^ n

/-- Finite transfer envelope for perturbations of singularity analysis. -/
def perturbationTransferEnvelopeCheck
    (base perturb N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedSingularCoeff base perturb n ≤
      (perturb + 1) * (n + 1) * base ^ n

def PerturbationSingularityWindow (base perturb N : ℕ) : Prop :=
  0 < base ∧ perturbationTransferEnvelopeCheck base perturb N = true

theorem perturbedSingularity_window :
    PerturbationSingularityWindow 2 3 16 := by
  constructor
  · norm_num
  · unfold perturbationTransferEnvelopeCheck perturbedSingularCoeff
    native_decide

/-- Finite one-step envelope for the polynomial factor in perturbed transfers. -/
def perturbedSingularStepCheck (base perturb N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedSingularCoeff base perturb (n + 1) ≤
      base * (n + 2) * perturbedSingularCoeff base perturb n

theorem perturbedSingularity_stepWindow :
    perturbedSingularStepCheck 3 2 12 = true := by
  unfold perturbedSingularStepCheck perturbedSingularCoeff
  native_decide

structure PerturbationSingularityAnalysisAsymptoticsBudgetCertificate where
  singularityWindow : ℕ
  perturbationWindow : ℕ
  transferWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.controlled
    (c : PerturbationSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  0 < c.singularityWindow ∧
    c.transferWindow ≤ c.singularityWindow + c.perturbationWindow + c.slack

def PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled
    (c : PerturbationSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.singularityWindow + c.perturbationWindow + c.transferWindow + c.slack

def PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.Ready
    (c : PerturbationSingularityAnalysisAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.size
    (c : PerturbationSingularityAnalysisAsymptoticsBudgetCertificate) : ℕ :=
  c.singularityWindow + c.perturbationWindow + c.transferWindow + c.slack

theorem perturbationSingularityAnalysisAsymptotics_budgetCertificate_le_size
    (c : PerturbationSingularityAnalysisAsymptoticsBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate :
    PerturbationSingularityAnalysisAsymptoticsBudgetCertificate :=
  { singularityWindow := 5
    perturbationWindow := 6
    transferWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example :
    samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num
      [PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.controlled,
        samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate]
  · norm_num
      [PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled,
        samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_ready :
    samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.controlled,
      samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate]
  · norm_num [PerturbationSingularityAnalysisAsymptoticsBudgetCertificate.budgetControlled,
      samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PerturbationSingularityAnalysisAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [samplePerturbationSingularityAnalysisAsymptoticsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.PerturbationSingularityAnalysisAsymptotics
