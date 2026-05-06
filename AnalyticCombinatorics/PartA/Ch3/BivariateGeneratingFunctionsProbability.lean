import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bivariate generating functions and probability distributions.

Finite mass and moment bookkeeping extracted from bivariate coefficients.
-/

namespace AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctionsProbability

/-- Finite bivariate mass table. -/
def bivariateMass (i j : ℕ) : ℚ :=
  if i = 0 ∧ j = 0 then 1 / 2
  else if i = 1 ∧ j = 0 then 1 / 4
  else if i = 0 ∧ j = 1 then 1 / 4
  else 0

/-- Total mass on a square window. -/
def bivariateMassTotal (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (i : ℕ) =>
      total + (List.range (N + 1)).foldl
        (fun (inner : ℚ) (j : ℕ) => inner + bivariateMass i j) 0)
    0

/-- First moment of the first coordinate on a square window. -/
def bivariateFirstMomentX (N : ℕ) : ℚ :=
  (List.range (N + 1)).foldl
    (fun (total : ℚ) (i : ℕ) =>
      total + (List.range (N + 1)).foldl
        (fun (inner : ℚ) (j : ℕ) => inner + (i : ℚ) * bivariateMass i j) 0)
    0

theorem bivariateMass_probabilityWindow :
    bivariateMassTotal 1 = 1 ∧ bivariateFirstMomentX 1 = 1 / 4 := by
  unfold bivariateMassTotal bivariateFirstMomentX bivariateMass
  native_decide

structure BivariateProbabilityWindow where
  totalMass : ℕ
  firstMoment : ℕ
  secondMoment : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def bivariateProbabilityReady (w : BivariateProbabilityWindow) : Prop :=
  0 < w.totalMass ∧ w.firstMoment ≤ w.secondMoment + w.totalMass + w.slack

def bivariateProbabilityBudget (w : BivariateProbabilityWindow) : ℕ :=
  w.totalMass + w.firstMoment + w.secondMoment + w.slack

theorem firstMoment_le_budget (w : BivariateProbabilityWindow) :
    w.firstMoment ≤ bivariateProbabilityBudget w := by
  unfold bivariateProbabilityBudget
  omega

def sampleBivariateProbabilityWindow : BivariateProbabilityWindow :=
  { totalMass := 8, firstMoment := 14, secondMoment := 9, slack := 1 }

example : bivariateProbabilityReady sampleBivariateProbabilityWindow := by
  norm_num [bivariateProbabilityReady, sampleBivariateProbabilityWindow]

structure BivariateGeneratingFunctionsProbabilityBudgetCertificate where
  massWindow : ℕ
  momentWindow : ℕ
  varianceWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BivariateGeneratingFunctionsProbabilityBudgetCertificate.controlled
    (c : BivariateGeneratingFunctionsProbabilityBudgetCertificate) : Prop :=
  0 < c.massWindow ∧
    c.momentWindow ≤ c.massWindow + c.varianceWindow + c.slack

def BivariateGeneratingFunctionsProbabilityBudgetCertificate.budgetControlled
    (c : BivariateGeneratingFunctionsProbabilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.massWindow + c.momentWindow + c.varianceWindow + c.slack

def BivariateGeneratingFunctionsProbabilityBudgetCertificate.Ready
    (c : BivariateGeneratingFunctionsProbabilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BivariateGeneratingFunctionsProbabilityBudgetCertificate.size
    (c : BivariateGeneratingFunctionsProbabilityBudgetCertificate) : ℕ :=
  c.massWindow + c.momentWindow + c.varianceWindow + c.slack

theorem bivariateGeneratingFunctionsProbability_budgetCertificate_le_size
    (c : BivariateGeneratingFunctionsProbabilityBudgetCertificate)
    (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate :
    BivariateGeneratingFunctionsProbabilityBudgetCertificate :=
  { massWindow := 8
    momentWindow := 14
    varianceWindow := 9
    certificateBudgetWindow := 32
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num
      [BivariateGeneratingFunctionsProbabilityBudgetCertificate.controlled,
        sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate]
  · norm_num
      [BivariateGeneratingFunctionsProbabilityBudgetCertificate.budgetControlled,
        sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate.certificateBudgetWindow ≤
      sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example :
    sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num
      [BivariateGeneratingFunctionsProbabilityBudgetCertificate.controlled,
        sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate]
  · norm_num
      [BivariateGeneratingFunctionsProbabilityBudgetCertificate.budgetControlled,
        sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BivariateGeneratingFunctionsProbabilityBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBivariateGeneratingFunctionsProbabilityBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.BivariateGeneratingFunctionsProbability
