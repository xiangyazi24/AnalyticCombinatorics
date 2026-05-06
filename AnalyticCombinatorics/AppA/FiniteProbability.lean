import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Appendix A: Finite Probability

Finite rational probability tools used in random structures, parameters, and
limit-law checks.
-/

namespace AnalyticCombinatorics.AppA.FiniteProbability

/-- A finite rational mass function. -/
structure FiniteDistribution where
  weights : List ℚ
  deriving DecidableEq

def totalMass (p : FiniteDistribution) : ℚ :=
  p.weights.foldl (fun s x => s + x) 0

def expectation (p : FiniteDistribution) : ℚ :=
  (List.range p.weights.length).foldl
    (fun (s : ℚ) (k : ℕ) => s + (k : ℚ) * p.weights.getD k 0) 0

def secondMoment (p : FiniteDistribution) : ℚ :=
  (List.range p.weights.length).foldl
    (fun (s : ℚ) (k : ℕ) => s + (k : ℚ) ^ 2 * p.weights.getD k 0) 0

def variance (p : FiniteDistribution) : ℚ :=
  secondMoment p - expectation p ^ 2

def bernoulliHalf : FiniteDistribution where
  weights := [1 / 2, 1 / 2]

def die0to5 : FiniteDistribution where
  weights := [1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6, 1 / 6]

theorem bernoulliHalf_moments :
    totalMass bernoulliHalf = 1 ∧
    expectation bernoulliHalf = 1 / 2 ∧
    secondMoment bernoulliHalf = 1 / 2 ∧
    variance bernoulliHalf = 1 / 4 := by
  native_decide

theorem die0to5_mass_expectation :
    totalMass die0to5 = 1 ∧ expectation die0to5 = 5 / 2 := by
  native_decide

/-- Convolution of two finite distributions. -/
def convolution (p q : FiniteDistribution) : FiniteDistribution where
  weights :=
    (List.range (p.weights.length + q.weights.length - 1)).map fun n =>
      (List.range (n + 1)).foldl
        (fun (s : ℚ) (k : ℕ) => s + p.weights.getD k 0 * q.weights.getD (n - k) 0)
        0

def twoBernoulliHalves : FiniteDistribution :=
  convolution bernoulliHalf bernoulliHalf

theorem twoBernoulliHalves_weights :
    twoBernoulliHalves.weights = [1 / 4, 1 / 2, 1 / 4] := by
  native_decide

theorem twoBernoulliHalves_moments :
    totalMass twoBernoulliHalves = 1 ∧
    expectation twoBernoulliHalves = 1 ∧
    variance twoBernoulliHalves = 1 / 2 := by
  native_decide

/-- Probability generating function coefficient lookup. -/
def pgfCoeff (p : FiniteDistribution) (n : ℕ) : ℚ :=
  p.weights.getD n 0

theorem pgfCoeff_twoBernoulli :
    pgfCoeff twoBernoulliHalves 0 = 1 / 4 ∧
    pgfCoeff twoBernoulliHalves 1 = 1 / 2 ∧
    pgfCoeff twoBernoulliHalves 2 = 1 / 4 ∧
    pgfCoeff twoBernoulliHalves 3 = 0 := by
  native_decide

/-- Finite convergence certificate by equality of sampled mass tables. -/
def FiniteDistributionConvergence
    (seq : ℕ → FiniteDistribution) (limit : FiniteDistribution) (N : ℕ) : Prop :=
  (List.range (N + 1)).all (fun n => seq n = limit) = true

theorem finite_distribution_convergence_statement :
    FiniteDistributionConvergence (fun _ => bernoulliHalf) bernoulliHalf 8 := by
  unfold FiniteDistributionConvergence bernoulliHalf
  native_decide


structure FiniteProbabilityBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteProbabilityBudgetCertificate.controlled
    (c : FiniteProbabilityBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteProbabilityBudgetCertificate.budgetControlled
    (c : FiniteProbabilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteProbabilityBudgetCertificate.Ready
    (c : FiniteProbabilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteProbabilityBudgetCertificate.size
    (c : FiniteProbabilityBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteProbability_budgetCertificate_le_size
    (c : FiniteProbabilityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteProbabilityBudgetCertificate :
    FiniteProbabilityBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProbabilityBudgetCertificate.controlled,
      sampleFiniteProbabilityBudgetCertificate]
  · norm_num [FiniteProbabilityBudgetCertificate.budgetControlled,
      sampleFiniteProbabilityBudgetCertificate]

example :
    sampleFiniteProbabilityBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProbabilityBudgetCertificate.size := by
  apply finiteProbability_budgetCertificate_le_size
  constructor
  · norm_num [FiniteProbabilityBudgetCertificate.controlled,
      sampleFiniteProbabilityBudgetCertificate]
  · norm_num [FiniteProbabilityBudgetCertificate.budgetControlled,
      sampleFiniteProbabilityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProbabilityBudgetCertificate.controlled,
      sampleFiniteProbabilityBudgetCertificate]
  · norm_num [FiniteProbabilityBudgetCertificate.budgetControlled,
      sampleFiniteProbabilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteProbabilityBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProbabilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteProbabilityBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteProbabilityBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteProbabilityBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteProbability
