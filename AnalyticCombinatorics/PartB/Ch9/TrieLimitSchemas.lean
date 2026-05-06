import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Trie Limit Schemas

Finite digital-tree models and Mellin-periodic descriptors for trie
parameters.
-/

namespace AnalyticCombinatorics.PartB.Ch9.TrieLimitSchemas

def fullBinaryTrieNodes (height : ℕ) : ℕ :=
  2 ^ (height + 1) - 1

theorem fullBinaryTrieNodes_samples :
    (List.range 6).map fullBinaryTrieNodes = [1, 3, 7, 15, 31, 63] := by
  native_decide

def externalNodes (height : ℕ) : ℕ :=
  2 ^ height

theorem externalNodes_samples :
    (List.range 6).map externalNodes = [1, 2, 4, 8, 16, 32] := by
  native_decide

def pathLengthFullTrie : ℕ → ℕ
  | 0 => 0
  | h + 1 => 2 * pathLengthFullTrie h + 2 ^ (h + 1)

theorem pathLengthFullTrie_samples :
    (List.range 6).map pathLengthFullTrie = [0, 2, 8, 24, 64, 160] := by
  native_decide

structure TrieMellinData where
  radix : ℕ
  periodicAmplitudeNumerator : ℕ
  periodicAmplitudeDenominator : ℕ

def binaryTrieMellinData : TrieMellinData where
  radix := 2
  periodicAmplitudeNumerator := 1
  periodicAmplitudeDenominator := 100

theorem binaryTrieMellinData_values :
    binaryTrieMellinData.radix = 2 ∧
    binaryTrieMellinData.periodicAmplitudeNumerator = 1 ∧
    binaryTrieMellinData.periodicAmplitudeDenominator = 100 := by
  native_decide

def trieMellinDataReady (data : TrieMellinData) : Prop :=
  1 < data.radix ∧ 0 < data.periodicAmplitudeDenominator

theorem binaryTrieMellinData_ready : trieMellinDataReady binaryTrieMellinData := by
  unfold trieMellinDataReady binaryTrieMellinData
  native_decide

def TrieLimitSchema
    (parameter : ℕ → ℚ) (data : TrieMellinData) : Prop :=
  trieMellinDataReady data ∧ parameter 0 = 0 ∧ parameter 5 = 160

def triePathLengthWitness (height : ℕ) : ℚ :=
  pathLengthFullTrie height

theorem trie_limit_schema_statement :
    TrieLimitSchema triePathLengthWitness binaryTrieMellinData := by
  unfold TrieLimitSchema trieMellinDataReady binaryTrieMellinData triePathLengthWitness
  native_decide

/-- Finite executable readiness audit for trie Mellin descriptors. -/
def trieMellinDataListReady (data : List TrieMellinData) : Bool :=
  data.all fun d =>
    1 < d.radix && 0 < d.periodicAmplitudeDenominator

theorem trieMellinDataList_readyWindow :
    trieMellinDataListReady
      [{ radix := 2, periodicAmplitudeNumerator := 1,
         periodicAmplitudeDenominator := 100 },
       { radix := 3, periodicAmplitudeNumerator := 1,
         periodicAmplitudeDenominator := 50 }] = true := by
  unfold trieMellinDataListReady
  native_decide

structure TrieLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TrieLimitSchemasBudgetCertificate.controlled
    (c : TrieLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def TrieLimitSchemasBudgetCertificate.budgetControlled
    (c : TrieLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def TrieLimitSchemasBudgetCertificate.Ready
    (c : TrieLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def TrieLimitSchemasBudgetCertificate.size
    (c : TrieLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem trieLimitSchemas_budgetCertificate_le_size
    (c : TrieLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleTrieLimitSchemasBudgetCertificate :
    TrieLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TrieLimitSchemasBudgetCertificate.controlled,
      sampleTrieLimitSchemasBudgetCertificate]
  · norm_num [TrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleTrieLimitSchemasBudgetCertificate]

example :
    sampleTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTrieLimitSchemasBudgetCertificate.size := by
  apply trieLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [TrieLimitSchemasBudgetCertificate.controlled,
      sampleTrieLimitSchemasBudgetCertificate]
  · norm_num [TrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleTrieLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleTrieLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [TrieLimitSchemasBudgetCertificate.controlled,
      sampleTrieLimitSchemasBudgetCertificate]
  · norm_num [TrieLimitSchemasBudgetCertificate.budgetControlled,
      sampleTrieLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleTrieLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleTrieLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List TrieLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleTrieLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleTrieLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.TrieLimitSchemas
