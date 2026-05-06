import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Cumulant controls for limit-law proofs.

The predicates here encode the finite algebraic checks usually extracted
from logarithmic moment-generating functions.
-/

namespace AnalyticCombinatorics.PartA.Ch3.CumulantLimitSchemas

structure CumulantBounds where
  second : ℕ
  third : ℕ
  fourth : ℕ
deriving DecidableEq, Repr

def variancePositive (c : CumulantBounds) : Prop :=
  0 < c.second

def gaussianScaleControlled (c : CumulantBounds) : Prop :=
  c.third ≤ c.second ∧ c.fourth ≤ c.second * c.second

def admissibleCumulants (c : CumulantBounds) : Prop :=
  variancePositive c ∧ gaussianScaleControlled c

theorem admissibleCumulants_intro {c : CumulantBounds}
    (hv : variancePositive c) (hg : gaussianScaleControlled c) :
    admissibleCumulants c := by
  exact ⟨hv, hg⟩

theorem admissibleCumulants.variance {c : CumulantBounds}
    (h : admissibleCumulants c) :
    variancePositive c := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem admissibleCumulants.third_bound {c : CumulantBounds}
    (h : admissibleCumulants c) :
    c.third ≤ c.second := h.2.1

def sampleCumulants : CumulantBounds :=
  { second := 4, third := 2, fourth := 9 }

example : variancePositive sampleCumulants := by
  norm_num [variancePositive, sampleCumulants]

example : gaussianScaleControlled sampleCumulants := by
  norm_num [gaussianScaleControlled, sampleCumulants]

example : admissibleCumulants sampleCumulants := by
  norm_num [admissibleCumulants, variancePositive, gaussianScaleControlled, sampleCumulants]

structure CumulantBudgetCertificate where
  varianceWindow : ℕ
  thirdCumulantWindow : ℕ
  fourthCumulantWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CumulantBudgetCertificate.controlled
    (c : CumulantBudgetCertificate) : Prop :=
  0 < c.varianceWindow ∧
    c.thirdCumulantWindow ≤ c.varianceWindow + c.slack ∧
      c.fourthCumulantWindow ≤ c.varianceWindow * c.varianceWindow + c.slack

def CumulantBudgetCertificate.budgetControlled
    (c : CumulantBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.varianceWindow + c.thirdCumulantWindow + c.fourthCumulantWindow + c.slack

def CumulantBudgetCertificate.Ready
    (c : CumulantBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CumulantBudgetCertificate.size
    (c : CumulantBudgetCertificate) : ℕ :=
  c.varianceWindow + c.thirdCumulantWindow + c.fourthCumulantWindow + c.slack

theorem cumulant_budgetCertificate_le_size
    (c : CumulantBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleCumulantBudgetCertificate :
    CumulantBudgetCertificate :=
  { varianceWindow := 4
    thirdCumulantWindow := 2
    fourthCumulantWindow := 9
    certificateBudgetWindow := 16
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleCumulantBudgetCertificate.Ready := by
  constructor
  · norm_num [CumulantBudgetCertificate.controlled,
      sampleCumulantBudgetCertificate]
  · norm_num [CumulantBudgetCertificate.budgetControlled,
      sampleCumulantBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCumulantBudgetCertificate.certificateBudgetWindow ≤
      sampleCumulantBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleCumulantBudgetCertificate.Ready := by
  constructor
  · norm_num [CumulantBudgetCertificate.controlled,
      sampleCumulantBudgetCertificate]
  · norm_num [CumulantBudgetCertificate.budgetControlled,
      sampleCumulantBudgetCertificate]

example :
    sampleCumulantBudgetCertificate.certificateBudgetWindow ≤
      sampleCumulantBudgetCertificate.size := by
  apply cumulant_budgetCertificate_le_size
  constructor
  · norm_num [CumulantBudgetCertificate.controlled,
      sampleCumulantBudgetCertificate]
  · norm_num [CumulantBudgetCertificate.budgetControlled,
      sampleCumulantBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List CumulantBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleCumulantBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleCumulantBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch3.CumulantLimitSchemas
