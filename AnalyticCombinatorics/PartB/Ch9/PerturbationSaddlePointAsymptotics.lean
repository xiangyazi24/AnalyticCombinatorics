import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Perturbation of saddle-point asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.PerturbationSaddlePointAsymptotics

/-- Quadratic saddle phase with a linear perturbation. -/
def perturbedQuadraticPhase (epsilon center n : ℕ) : ℤ :=
  ((n : ℤ) - (center : ℤ)) ^ 2 + epsilon * n

/-- Finite perturbation audit: perturbation changes phase by a bounded amount. -/
def perturbationBoundCheck
    (epsilon center bound N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedQuadraticPhase epsilon center n -
        perturbedQuadraticPhase 0 center n ≤ bound * n

def PerturbedSaddleWindow (epsilon center bound N : ℕ) : Prop :=
  perturbationBoundCheck epsilon center bound N = true

theorem linearPerturbation_saddleWindow :
    PerturbedSaddleWindow 2 5 2 16 := by
  unfold PerturbedSaddleWindow perturbationBoundCheck
    perturbedQuadraticPhase
  native_decide

/-- Finite audit that the unperturbed quadratic phase is minimized at the center. -/
def unperturbedMinimumCheck (center N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    perturbedQuadraticPhase 0 center center ≤
      perturbedQuadraticPhase 0 center n

theorem unperturbedQuadratic_minimumWindow :
    unperturbedMinimumCheck 5 12 = true := by
  unfold unperturbedMinimumCheck perturbedQuadraticPhase
  native_decide

structure PerturbationSaddlePointAsymptoticsBudgetCertificate where
  saddleWindow : ℕ
  perturbationWindow : ℕ
  gaussianWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PerturbationSaddlePointAsymptoticsBudgetCertificate.controlled
    (c : PerturbationSaddlePointAsymptoticsBudgetCertificate) : Prop :=
  0 < c.saddleWindow ∧
    c.gaussianWindow ≤ c.saddleWindow + c.perturbationWindow + c.slack

def PerturbationSaddlePointAsymptoticsBudgetCertificate.budgetControlled
    (c : PerturbationSaddlePointAsymptoticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleWindow + c.perturbationWindow + c.gaussianWindow + c.slack

def PerturbationSaddlePointAsymptoticsBudgetCertificate.Ready
    (c : PerturbationSaddlePointAsymptoticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def PerturbationSaddlePointAsymptoticsBudgetCertificate.size
    (c : PerturbationSaddlePointAsymptoticsBudgetCertificate) : ℕ :=
  c.saddleWindow + c.perturbationWindow + c.gaussianWindow + c.slack

theorem perturbationSaddlePointAsymptotics_budgetCertificate_le_size
    (c : PerturbationSaddlePointAsymptoticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def samplePerturbationSaddlePointAsymptoticsBudgetCertificate :
    PerturbationSaddlePointAsymptoticsBudgetCertificate :=
  { saddleWindow := 5
    perturbationWindow := 6
    gaussianWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    samplePerturbationSaddlePointAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationSaddlePointAsymptoticsBudgetCertificate.controlled,
      samplePerturbationSaddlePointAsymptoticsBudgetCertificate]
  · norm_num [PerturbationSaddlePointAsymptoticsBudgetCertificate.budgetControlled,
      samplePerturbationSaddlePointAsymptoticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    samplePerturbationSaddlePointAsymptoticsBudgetCertificate.certificateBudgetWindow ≤
      samplePerturbationSaddlePointAsymptoticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : samplePerturbationSaddlePointAsymptoticsBudgetCertificate.Ready := by
  constructor
  · norm_num [PerturbationSaddlePointAsymptoticsBudgetCertificate.controlled,
      samplePerturbationSaddlePointAsymptoticsBudgetCertificate]
  · norm_num [PerturbationSaddlePointAsymptoticsBudgetCertificate.budgetControlled,
      samplePerturbationSaddlePointAsymptoticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List PerturbationSaddlePointAsymptoticsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [samplePerturbationSaddlePointAsymptoticsBudgetCertificate] = true := by
  unfold budgetCertificateListReady samplePerturbationSaddlePointAsymptoticsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [samplePerturbationSaddlePointAsymptoticsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartB.Ch9.PerturbationSaddlePointAsymptotics
