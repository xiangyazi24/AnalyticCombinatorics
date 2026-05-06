import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Limit laws and combinatorial structures.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LimitLawsCombinatorialStructures

/-- Finite structure family with a size and an additive parameter. -/
structure StructureSample where
  size : ℕ
  parameter : ℕ
deriving DecidableEq, Repr

def parameterBounded (s : StructureSample) : Prop :=
  s.parameter ≤ s.size

/-- Boolean form of the parameter-bound audit. -/
def parameterBoundedBool (s : StructureSample) : Bool :=
  s.parameter ≤ s.size

/-- Finite audit that sampled parameters stay inside their structure size. -/
def parameterBoundedUpTo
    (samples : ℕ → StructureSample) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => parameterBoundedBool (samples n)

def subsetParameterSample (n : ℕ) : StructureSample :=
  { size := n + 1, parameter := n / 2 }

def CombinatorialLimitWindow (samples : ℕ → StructureSample) (N : ℕ) : Prop :=
  parameterBoundedUpTo samples N = true

theorem subsetParameter_limitWindow :
    CombinatorialLimitWindow subsetParameterSample 24 := by
  unfold CombinatorialLimitWindow parameterBoundedUpTo
    parameterBoundedBool subsetParameterSample
  native_decide

/-- Prefix sum of sampled additive parameters. -/
def parameterPrefixSum (samples : ℕ → StructureSample) (N : ℕ) : ℕ :=
  (List.range (N + 1)).foldl
    (fun total n => total + (samples n).parameter) 0

def ParameterPrefixWindow (samples : ℕ → StructureSample) (N total : ℕ) : Prop :=
  parameterPrefixSum samples N = total

theorem subsetParameter_prefixWindow :
    ParameterPrefixWindow subsetParameterSample 6 9 := by
  unfold ParameterPrefixWindow parameterPrefixSum subsetParameterSample
  native_decide

example : parameterBoundedBool (subsetParameterSample 8) = true := by
  unfold parameterBoundedBool subsetParameterSample
  native_decide

example : parameterPrefixSum subsetParameterSample 4 = 4 := by
  unfold parameterPrefixSum subsetParameterSample
  native_decide

structure LimitLawsCombinatorialStructuresBudgetCertificate where
  structureWindow : ℕ
  parameterWindow : ℕ
  limitWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LimitLawsCombinatorialStructuresBudgetCertificate.controlled
    (c : LimitLawsCombinatorialStructuresBudgetCertificate) : Prop :=
  0 < c.structureWindow ∧
    c.limitWindow ≤ c.structureWindow + c.parameterWindow + c.slack

def LimitLawsCombinatorialStructuresBudgetCertificate.budgetControlled
    (c : LimitLawsCombinatorialStructuresBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.structureWindow + c.parameterWindow + c.limitWindow + c.slack

def LimitLawsCombinatorialStructuresBudgetCertificate.Ready
    (c : LimitLawsCombinatorialStructuresBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LimitLawsCombinatorialStructuresBudgetCertificate.size
    (c : LimitLawsCombinatorialStructuresBudgetCertificate) : ℕ :=
  c.structureWindow + c.parameterWindow + c.limitWindow + c.slack

theorem limitLawsCombinatorialStructures_budgetCertificate_le_size
    (c : LimitLawsCombinatorialStructuresBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleLimitLawsCombinatorialStructuresBudgetCertificate :
    LimitLawsCombinatorialStructuresBudgetCertificate :=
  { structureWindow := 5
    parameterWindow := 6
    limitWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLimitLawsCombinatorialStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsCombinatorialStructuresBudgetCertificate.controlled,
      sampleLimitLawsCombinatorialStructuresBudgetCertificate]
  · norm_num [LimitLawsCombinatorialStructuresBudgetCertificate.budgetControlled,
      sampleLimitLawsCombinatorialStructuresBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLimitLawsCombinatorialStructuresBudgetCertificate.certificateBudgetWindow ≤
      sampleLimitLawsCombinatorialStructuresBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLimitLawsCombinatorialStructuresBudgetCertificate.Ready := by
  constructor
  · norm_num [LimitLawsCombinatorialStructuresBudgetCertificate.controlled,
      sampleLimitLawsCombinatorialStructuresBudgetCertificate]
  · norm_num [LimitLawsCombinatorialStructuresBudgetCertificate.budgetControlled,
      sampleLimitLawsCombinatorialStructuresBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List LimitLawsCombinatorialStructuresBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLimitLawsCombinatorialStructuresBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLimitLawsCombinatorialStructuresBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.LimitLawsCombinatorialStructures
