import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Limit laws and combinatorial structures
-/

namespace AnalyticCombinatorics.PartB.Ch9.LimitLawsAndCombinatorialStructures

/-- Finite distribution summary attached to a combinatorial parameter. -/
structure LimitLawSummary where
  mass : ℕ
  meanNumerator : ℕ
  varianceNumerator : ℕ
deriving DecidableEq, Repr

def LimitLawSummary.normalizable (s : LimitLawSummary) : Prop :=
  0 < s.mass

theorem limitLawSummary_sample_normalizable :
    ({ mass := 10, meanNumerator := 15,
       varianceNumerator := 21 } : LimitLawSummary).normalizable := by
  norm_num [LimitLawSummary.normalizable]

/-- Cleared variance scale used by finite limit-law certificates. -/
def limitLawVarianceScale (mass varianceNumerator : ℕ) : ℕ :=
  mass * varianceNumerator

theorem limitLawVarianceScale_sample :
    limitLawVarianceScale 10 21 = 210 := by
  native_decide

structure StructureLimitWindow where
  structureWindow : ℕ
  parameterWindow : ℕ
  lawWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StructureLimitWindow.ready (w : StructureLimitWindow) : Prop :=
  0 < w.structureWindow ∧
    w.lawWindow ≤ w.structureWindow + w.parameterWindow + w.slack

def sampleStructureLimitWindow : StructureLimitWindow :=
  { structureWindow := 4, parameterWindow := 3, lawWindow := 7, slack := 0 }

example : sampleStructureLimitWindow.ready := by
  norm_num [StructureLimitWindow.ready, sampleStructureLimitWindow]

structure BudgetCertificate where
  structureWindow : ℕ
  lawWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.structureWindow ∧ c.lawWindow ≤ c.structureWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.structureWindow + c.lawWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.structureWindow + c.lawWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { structureWindow := 5, lawWindow := 6,
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

end AnalyticCombinatorics.PartB.Ch9.LimitLawsAndCombinatorialStructures
