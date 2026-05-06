import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Inherited parameters and exponential MGFs
-/

namespace AnalyticCombinatorics.PartA.Ch3.InheritedParametersAndExponentialMGFs

/-- Labelled inherited parameter data: count and total parameter weight. -/
structure LabelledParameterClass where
  labelledCount : ℕ
  totalParameterWeight : ℕ
deriving DecidableEq, Repr

def LabelledParameterClass.meanNumerator (c : LabelledParameterClass) : ℕ :=
  c.totalParameterWeight

def LabelledParameterClass.meanDenominator (c : LabelledParameterClass) : ℕ :=
  c.labelledCount

theorem labelledParameterClass_sample :
    ({ labelledCount := 8, totalParameterWeight := 20 } :
      LabelledParameterClass).meanNumerator = 20 := by
  native_decide

/-- Exponential MGF coefficient certificate after clearing factorial denominators. -/
def exponentialMGFClearedCoeff (labelledCount parameterPower : ℕ) : ℕ :=
  labelledCount * parameterPower

theorem exponentialMGFClearedCoeff_sample :
    exponentialMGFClearedCoeff 12 9 = 108 := by
  native_decide

/-- Product rule for inherited labelled parameters at the level of total weights. -/
def inheritedLabelledProductWeight
    (leftCount leftWeight rightCount rightWeight : ℕ) : ℕ :=
  leftWeight * rightCount + rightWeight * leftCount

theorem inheritedLabelledProductWeight_sample :
    inheritedLabelledProductWeight 3 4 5 6 = 38 := by
  native_decide

structure BudgetCertificate where
  inheritedWindow : ℕ
  exponentialMGFWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BudgetCertificate.controlled (c : BudgetCertificate) : Prop :=
  0 < c.inheritedWindow ∧
    c.exponentialMGFWindow ≤ c.inheritedWindow + c.slack

def BudgetCertificate.budgetControlled (c : BudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.inheritedWindow + c.exponentialMGFWindow + c.slack

def BudgetCertificate.Ready (c : BudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BudgetCertificate.size (c : BudgetCertificate) : ℕ :=
  c.inheritedWindow + c.exponentialMGFWindow + c.slack

def sampleBudgetCertificate : BudgetCertificate :=
  { inheritedWindow := 5, exponentialMGFWindow := 6,
    certificateBudgetWindow := 12, slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled,
      sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled,
      sampleBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBudgetCertificate.certificateBudgetWindow ≤
      sampleBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBudgetCertificate.Ready := by
  constructor
  · norm_num [BudgetCertificate.controlled, sampleBudgetCertificate]
  · norm_num [BudgetCertificate.budgetControlled, sampleBudgetCertificate]

def budgetCertificateListReady (data : List BudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartA.Ch3.InheritedParametersAndExponentialMGFs
