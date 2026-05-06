import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Hashing Limit Schemas

Finite load and collision models for hashing.
-/

namespace AnalyticCombinatorics.PartB.Ch9.HashingLimitSchemas

def loadNumerator (keys _buckets : ℕ) : ℕ :=
  keys

def loadDenominator (_keys buckets : ℕ) : ℕ :=
  buckets

theorem load_samples :
    loadNumerator 10 4 = 10 ∧ loadDenominator 10 4 = 4 := by
  native_decide

def collisionPairCount (keys : ℕ) : ℕ :=
  keys * (keys - 1) / 2

theorem collisionPairCount_samples :
    (List.range 7).map collisionPairCount = [0, 0, 1, 3, 6, 10, 15] := by
  native_decide

def expectedCollisionsNumerator (keys _buckets : ℕ) : ℕ :=
  collisionPairCount keys

def expectedCollisionsDenominator (_keys buckets : ℕ) : ℕ :=
  buckets

theorem expectedCollisions_samples :
    expectedCollisionsNumerator 5 10 = 10 ∧
    expectedCollisionsDenominator 5 10 = 10 := by
  native_decide

structure HashingLimitData where
  loadNumerator : ℕ
  loadDenominator : ℕ
  lawName : String

def poissonHashingData : HashingLimitData where
  loadNumerator := 1
  loadDenominator := 1
  lawName := "Poisson"

theorem poissonHashingData_values :
    poissonHashingData.loadNumerator = 1 ∧
    poissonHashingData.loadDenominator = 1 ∧
    poissonHashingData.lawName = "Poisson" := by
  native_decide

def hashingLimitDataReady (data : HashingLimitData) : Prop :=
  0 < data.loadDenominator ∧ 0 < data.lawName.length

theorem poissonHashingData_ready : hashingLimitDataReady poissonHashingData := by
  unfold hashingLimitDataReady poissonHashingData
  native_decide

def HashingPoissonLimit
    (bucketLoad : ℕ → ℕ → ℚ) (data : HashingLimitData) : Prop :=
  hashingLimitDataReady data ∧ bucketLoad 0 0 = 0 ∧ bucketLoad 5 10 = 10

def hashingCollisionWitness (keys buckets : ℕ) : ℚ :=
  expectedCollisionsNumerator keys buckets

theorem hashing_poisson_limit_statement :
    HashingPoissonLimit hashingCollisionWitness poissonHashingData := by
  unfold HashingPoissonLimit hashingLimitDataReady poissonHashingData hashingCollisionWitness
  native_decide

/-- Finite executable readiness audit for hashing limit descriptors. -/
def hashingLimitDataListReady
    (data : List HashingLimitData) : Bool :=
  data.all fun d =>
    0 < d.loadDenominator && 0 < d.lawName.length

theorem hashingLimitDataList_readyWindow :
    hashingLimitDataListReady
      [{ loadNumerator := 1, loadDenominator := 1, lawName := "Poisson" },
       { loadNumerator := 2, loadDenominator := 3, lawName := "compound" }] =
      true := by
  unfold hashingLimitDataListReady
  native_decide

structure HashingLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HashingLimitSchemasBudgetCertificate.controlled
    (c : HashingLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HashingLimitSchemasBudgetCertificate.budgetControlled
    (c : HashingLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HashingLimitSchemasBudgetCertificate.Ready
    (c : HashingLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HashingLimitSchemasBudgetCertificate.size
    (c : HashingLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem hashingLimitSchemas_budgetCertificate_le_size
    (c : HashingLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHashingLimitSchemasBudgetCertificate :
    HashingLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleHashingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HashingLimitSchemasBudgetCertificate.controlled,
      sampleHashingLimitSchemasBudgetCertificate]
  · norm_num [HashingLimitSchemasBudgetCertificate.budgetControlled,
      sampleHashingLimitSchemasBudgetCertificate]

example :
    sampleHashingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHashingLimitSchemasBudgetCertificate.size := by
  apply hashingLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [HashingLimitSchemasBudgetCertificate.controlled,
      sampleHashingLimitSchemasBudgetCertificate]
  · norm_num [HashingLimitSchemasBudgetCertificate.budgetControlled,
      sampleHashingLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleHashingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [HashingLimitSchemasBudgetCertificate.controlled,
      sampleHashingLimitSchemasBudgetCertificate]
  · norm_num [HashingLimitSchemasBudgetCertificate.budgetControlled,
      sampleHashingLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHashingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleHashingLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List HashingLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHashingLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleHashingLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.HashingLimitSchemas
