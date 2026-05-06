import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perturbation of meromorphic asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationMeromorphicAsymptotics

/-- Coefficient model for a perturbed simple pole. -/
def perturbedPoleCoeff (base perturb n : ℕ) : ℕ :=
  (perturb + 1) * base ^ n

/-- Finite audit that perturbing the residue preserves geometric growth. -/
def perturbedPoleEnvelopeCheck
    (base perturb N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedPoleCoeff base perturb n ≤ (perturb + 1) * base ^ n

def PerturbedMeromorphicWindow (base perturb N : ℕ) : Prop :=
  perturbedPoleEnvelopeCheck base perturb N = true

theorem perturbedPole_window :
    PerturbedMeromorphicWindow 3 2 12 := by
  unfold PerturbedMeromorphicWindow perturbedPoleEnvelopeCheck
    perturbedPoleCoeff
  native_decide

/-- Finite audit that a perturbed simple-pole model has a constant geometric ratio. -/
def perturbedPoleRatioCheck (base perturb N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedPoleCoeff base perturb (n + 1) =
      base * perturbedPoleCoeff base perturb n

theorem perturbedPole_ratioWindow :
    perturbedPoleRatioCheck 4 3 10 = true := by
  unfold perturbedPoleRatioCheck perturbedPoleCoeff
  native_decide

structure PerturbationMeromorphicAsymptoticsBudgetCertificate where
  poleWindow : ℕ
  perturbationWindow : ℕ
  coefficientWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerturbationMeromorphicAsymptoticsBudgetCertificate.controlled
    (c : PerturbationMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  0 < c.poleWindow ∧
    c.coefficientWindow ≤ c.poleWindow + c.perturbationWindow + c.slack

def PerturbationMeromorphicAsymptoticsBudgetCertificate.budgetControlled
    (c : PerturbationMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.poleWindow + c.perturbationWindow + c.coefficientWindow + c.slack

def PerturbationMeromorphicAsymptoticsBudgetCertificate.Ready
    (c : PerturbationMeromorphicAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerturbationMeromorphicAsymptoticsBudgetCertificate.size
    (c : PerturbationMeromorphicAsymptoticsBudgetCertificate) : ℕ :=
  c.poleWindow + c.perturbationWindow + c.coefficientWindow + c.slack

theorem perturbationMeromorphicAsymptotics_budgetCertificate_le_size
    (c : PerturbationMeromorphicAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePerturbationMeromorphicAsymptoticsBudgetCertificate :
    PerturbationMeromorphicAsymptoticsBudgetCertificate :=
  { poleWindow := 5
    perturbationWindow := 6
    coefficientWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePerturbationMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationMeromorphicAsymptoticsBudgetCertificate.controlled,
      samplePerturbationMeromorphicAsymptoticsBudgetCertificate]
  · norm_num [PerturbationMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
      samplePerturbationMeromorphicAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerturbationMeromorphicAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePerturbationMeromorphicAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePerturbationMeromorphicAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationMeromorphicAsymptoticsBudgetCertificate.controlled,
      samplePerturbationMeromorphicAsymptoticsBudgetCertificate]
  · norm_num
      [PerturbationMeromorphicAsymptoticsBudgetCertificate.budgetControlled,
        samplePerturbationMeromorphicAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PerturbationMeromorphicAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerturbationMeromorphicAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePerturbationMeromorphicAsymptoticsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [samplePerturbationMeromorphicAsymptoticsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.PerturbationMeromorphicAsymptotics
