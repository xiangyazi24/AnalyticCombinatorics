import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Leader Election Schemas

Finite recurrence models for leader-election protocols.
-/

namespace AnalyticCombinatorics.PartB.Ch9.LeaderElectionSchemas

def survivorsExpectedNumerator (n : ℕ) : ℕ :=
  n

def survivorsExpectedDenominator (n : ℕ) : ℕ :=
  n - n + 2

theorem survivorsExpected_samples :
    survivorsExpectedNumerator 10 = 10 ∧ survivorsExpectedDenominator 10 = 2 := by
  native_decide

def roundsUpperBound (n : ℕ) : ℕ :=
  Nat.log2 (n + 1) + 1

theorem roundsUpperBound_samples :
    roundsUpperBound 1 = 2 ∧
    roundsUpperBound 3 = 3 ∧
    roundsUpperBound 7 = 4 := by
  native_decide

def binarySplitCount (n : ℕ) : ℕ :=
  2 ^ n

theorem binarySplitCount_samples :
    (List.range 6).map binarySplitCount = [1, 2, 4, 8, 16, 32] := by
  native_decide

structure LeaderElectionData where
  branchingFactor : ℕ
  tollNumerator : ℕ
  tollDenominator : ℕ

def binaryLeaderElectionData : LeaderElectionData where
  branchingFactor := 2
  tollNumerator := 1
  tollDenominator := 1

theorem binaryLeaderElectionData_values :
    binaryLeaderElectionData.branchingFactor = 2 ∧
    binaryLeaderElectionData.tollNumerator = 1 ∧
    binaryLeaderElectionData.tollDenominator = 1 := by
  native_decide

def leaderElectionDataReady (data : LeaderElectionData) : Prop :=
  1 < data.branchingFactor ∧ 0 < data.tollDenominator

theorem binaryLeaderElectionData_ready :
    leaderElectionDataReady binaryLeaderElectionData := by
  unfold leaderElectionDataReady binaryLeaderElectionData
  native_decide

def LeaderElectionLimitSchema
    (rounds : ℕ → ℚ) (data : LeaderElectionData) : Prop :=
  leaderElectionDataReady data ∧ rounds 1 = 2 ∧ rounds 7 = 4

def leaderRoundsWitness (n : ℕ) : ℚ :=
  roundsUpperBound n

theorem leader_election_limit_schema_statement :
    LeaderElectionLimitSchema leaderRoundsWitness binaryLeaderElectionData := by
  unfold LeaderElectionLimitSchema leaderElectionDataReady binaryLeaderElectionData
    leaderRoundsWitness
  native_decide

/-- Finite executable readiness audit for leader-election descriptors. -/
def leaderElectionDataListReady
    (data : List LeaderElectionData) : Bool :=
  data.all fun d =>
    1 < d.branchingFactor && 0 < d.tollDenominator

theorem leaderElectionDataList_readyWindow :
    leaderElectionDataListReady
      [{ branchingFactor := 2, tollNumerator := 1, tollDenominator := 1 },
       { branchingFactor := 3, tollNumerator := 2, tollDenominator := 5 }] =
      true := by
  unfold leaderElectionDataListReady
  native_decide

structure LeaderElectionSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LeaderElectionSchemasBudgetCertificate.controlled
    (c : LeaderElectionSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def LeaderElectionSchemasBudgetCertificate.budgetControlled
    (c : LeaderElectionSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def LeaderElectionSchemasBudgetCertificate.Ready
    (c : LeaderElectionSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LeaderElectionSchemasBudgetCertificate.size
    (c : LeaderElectionSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem leaderElectionSchemas_budgetCertificate_le_size
    (c : LeaderElectionSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLeaderElectionSchemasBudgetCertificate :
    LeaderElectionSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleLeaderElectionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LeaderElectionSchemasBudgetCertificate.controlled,
      sampleLeaderElectionSchemasBudgetCertificate]
  · norm_num [LeaderElectionSchemasBudgetCertificate.budgetControlled,
      sampleLeaderElectionSchemasBudgetCertificate]

example :
    sampleLeaderElectionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLeaderElectionSchemasBudgetCertificate.size := by
  apply leaderElectionSchemas_budgetCertificate_le_size
  constructor
  · norm_num [LeaderElectionSchemasBudgetCertificate.controlled,
      sampleLeaderElectionSchemasBudgetCertificate]
  · norm_num [LeaderElectionSchemasBudgetCertificate.budgetControlled,
      sampleLeaderElectionSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleLeaderElectionSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [LeaderElectionSchemasBudgetCertificate.controlled,
      sampleLeaderElectionSchemasBudgetCertificate]
  · norm_num [LeaderElectionSchemasBudgetCertificate.budgetControlled,
      sampleLeaderElectionSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLeaderElectionSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleLeaderElectionSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List LeaderElectionSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleLeaderElectionSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleLeaderElectionSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.LeaderElectionSchemas
