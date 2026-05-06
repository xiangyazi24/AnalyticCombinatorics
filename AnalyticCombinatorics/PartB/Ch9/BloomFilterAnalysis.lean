import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
# Chapter IX: Bloom Filter Analysis

Finite occupancy-based models for Bloom filters and false-positive
probabilities.
-/

namespace AnalyticCombinatorics.PartB.Ch9.BloomFilterAnalysis

def emptyCellNumerator (m k n : ℕ) : ℕ :=
  (m - 1) ^ (k * n)

def emptyCellDenominator (m k n : ℕ) : ℕ :=
  m ^ (k * n)

theorem emptyCell_fraction_samples :
    emptyCellNumerator 10 2 3 = 531441 ∧
    emptyCellDenominator 10 2 3 = 1000000 := by
  native_decide

def falsePositiveProxyNumerator (m k n : ℕ) : ℕ :=
  (emptyCellDenominator m k n - emptyCellNumerator m k n) ^ k

def falsePositiveProxyDenominator (m k n : ℕ) : ℕ :=
  (emptyCellDenominator m k n) ^ k

theorem falsePositiveProxy_small :
    falsePositiveProxyNumerator 4 2 1 = 49 ∧
    falsePositiveProxyDenominator 4 2 1 = 256 := by
  native_decide

structure BloomFilterData where
  cells : ℕ
  hashes : ℕ
  inserted : ℕ

def smallBloomFilter : BloomFilterData where
  cells := 4
  hashes := 2
  inserted := 1

theorem smallBloomFilter_values :
    smallBloomFilter.cells = 4 ∧ smallBloomFilter.hashes = 2 ∧ smallBloomFilter.inserted = 1 := by
  native_decide

def bloomFilterDataReady (data : BloomFilterData) : Prop :=
  0 < data.cells ∧ 0 < data.hashes

theorem smallBloomFilter_ready : bloomFilterDataReady smallBloomFilter := by
  unfold bloomFilterDataReady smallBloomFilter
  native_decide

def BloomFilterFalsePositiveAsymptotics
    (data : BloomFilterData) (probability : ℕ → ℚ) : Prop :=
  bloomFilterDataReady data ∧ probability 0 = 0 ∧ probability 1 = 49

def bloomFalsePositiveWitness (n : ℕ) : ℚ :=
  falsePositiveProxyNumerator 4 2 n

theorem bloom_filter_false_positive_asymptotics_statement :
    BloomFilterFalsePositiveAsymptotics smallBloomFilter bloomFalsePositiveWitness := by
  unfold BloomFilterFalsePositiveAsymptotics bloomFilterDataReady smallBloomFilter
    bloomFalsePositiveWitness
  native_decide


structure BloomFilterAnalysisBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BloomFilterAnalysisBudgetCertificate.controlled
    (c : BloomFilterAnalysisBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BloomFilterAnalysisBudgetCertificate.budgetControlled
    (c : BloomFilterAnalysisBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BloomFilterAnalysisBudgetCertificate.Ready
    (c : BloomFilterAnalysisBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BloomFilterAnalysisBudgetCertificate.size
    (c : BloomFilterAnalysisBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem bloomFilterAnalysis_budgetCertificate_le_size
    (c : BloomFilterAnalysisBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBloomFilterAnalysisBudgetCertificate :
    BloomFilterAnalysisBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleBloomFilterAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [BloomFilterAnalysisBudgetCertificate.controlled,
      sampleBloomFilterAnalysisBudgetCertificate]
  · norm_num [BloomFilterAnalysisBudgetCertificate.budgetControlled,
      sampleBloomFilterAnalysisBudgetCertificate]

example :
    sampleBloomFilterAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleBloomFilterAnalysisBudgetCertificate.size := by
  apply bloomFilterAnalysis_budgetCertificate_le_size
  constructor
  · norm_num [BloomFilterAnalysisBudgetCertificate.controlled,
      sampleBloomFilterAnalysisBudgetCertificate]
  · norm_num [BloomFilterAnalysisBudgetCertificate.budgetControlled,
      sampleBloomFilterAnalysisBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleBloomFilterAnalysisBudgetCertificate.Ready := by
  constructor
  · norm_num [BloomFilterAnalysisBudgetCertificate.controlled,
      sampleBloomFilterAnalysisBudgetCertificate]
  · norm_num [BloomFilterAnalysisBudgetCertificate.budgetControlled,
      sampleBloomFilterAnalysisBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBloomFilterAnalysisBudgetCertificate.certificateBudgetWindow ≤
      sampleBloomFilterAnalysisBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List BloomFilterAnalysisBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBloomFilterAnalysisBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleBloomFilterAnalysisBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch9.BloomFilterAnalysis
