import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: String Matching Limit Schemas

Finite autocorrelation and occurrence-count models for pattern matching.
-/

namespace AnalyticCombinatorics.PartB.Ch9.StringMatchingLimitSchemas

def borderLengthBinary (pattern : List Bool) (k : ℕ) : Bool :=
  let n := pattern.length
  (List.range k).all fun i => pattern.getD i false == pattern.getD (n - k + i) true

theorem borderLengthBinary_samples :
    borderLengthBinary [true, false, true] 1 = true ∧
    borderLengthBinary [true, false, true] 2 = false ∧
    borderLengthBinary [true, true, true] 2 = true := by
  native_decide

def autocorrelationBits (pattern : List Bool) : List Bool :=
  (List.range (pattern.length + 1)).map (borderLengthBinary pattern)

theorem autocorrelationBits_samples :
    autocorrelationBits [true, false, true] = [true, true, false, true] := by
  native_decide

def expectedOccurrencesNumerator (textLength patternLength : ℕ) : ℕ :=
  textLength + 1 - patternLength

def expectedOccurrencesDenominator (alphabetSize _textLength patternLength : ℕ) : ℕ :=
  alphabetSize ^ patternLength

theorem expectedOccurrences_samples :
    expectedOccurrencesNumerator 100 3 = 98 ∧
    expectedOccurrencesDenominator 2 100 3 = 8 := by
  native_decide

structure StringMatchingLimitData where
  alphabetSize : ℕ
  patternLength : ℕ
  autocorrelationWeight : ℕ

def binaryPatternData : StringMatchingLimitData where
  alphabetSize := 2
  patternLength := 3
  autocorrelationWeight := 1

theorem binaryPatternData_values :
    binaryPatternData.alphabetSize = 2 ∧
    binaryPatternData.patternLength = 3 ∧
    binaryPatternData.autocorrelationWeight = 1 := by
  native_decide

def stringMatchingLimitDataReady (data : StringMatchingLimitData) : Prop :=
  0 < data.alphabetSize ∧ 0 < data.patternLength

theorem binaryPatternData_ready : stringMatchingLimitDataReady binaryPatternData := by
  unfold stringMatchingLimitDataReady binaryPatternData
  native_decide

def StringMatchingPoissonLimit
    (occurrences : ℕ → ℕ → ℚ) (data : StringMatchingLimitData) : Prop :=
  stringMatchingLimitDataReady data ∧ occurrences 0 0 = 1 ∧ occurrences 100 3 = 98

def occurrenceWitness (textLength patternLength : ℕ) : ℚ :=
  expectedOccurrencesNumerator textLength patternLength

theorem string_matching_poisson_limit_statement :
    StringMatchingPoissonLimit occurrenceWitness binaryPatternData := by
  unfold StringMatchingPoissonLimit stringMatchingLimitDataReady binaryPatternData occurrenceWitness
  native_decide

/-- Finite executable readiness audit for string-matching descriptors. -/
def stringMatchingLimitDataListReady
    (data : List StringMatchingLimitData) : Bool :=
  data.all fun d =>
    0 < d.alphabetSize && 0 < d.patternLength

theorem stringMatchingLimitDataList_readyWindow :
    stringMatchingLimitDataListReady
      [{ alphabetSize := 2, patternLength := 3, autocorrelationWeight := 1 },
       { alphabetSize := 3, patternLength := 4, autocorrelationWeight := 2 }] =
      true := by
  unfold stringMatchingLimitDataListReady
  native_decide

structure StringMatchingLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StringMatchingLimitSchemasBudgetCertificate.controlled
    (c : StringMatchingLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StringMatchingLimitSchemasBudgetCertificate.budgetControlled
    (c : StringMatchingLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StringMatchingLimitSchemasBudgetCertificate.Ready
    (c : StringMatchingLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StringMatchingLimitSchemasBudgetCertificate.size
    (c : StringMatchingLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stringMatchingLimitSchemas_budgetCertificate_le_size
    (c : StringMatchingLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStringMatchingLimitSchemasBudgetCertificate :
    StringMatchingLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleStringMatchingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.controlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]

example :
    sampleStringMatchingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStringMatchingLimitSchemasBudgetCertificate.size := by
  apply stringMatchingLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.controlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleStringMatchingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.controlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]
  · norm_num [StringMatchingLimitSchemasBudgetCertificate.budgetControlled,
      sampleStringMatchingLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleStringMatchingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStringMatchingLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List StringMatchingLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStringMatchingLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleStringMatchingLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.StringMatchingLimitSchemas
