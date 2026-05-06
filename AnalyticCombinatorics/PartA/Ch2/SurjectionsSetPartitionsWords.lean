import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Surjections, set partitions, and words.
-/

namespace AnalyticCombinatorics.PartA.Ch2.SurjectionsSetPartitionsWords

/-- Word count for functions from an `n`-set to a `k`-set. -/
def wordFunctionCount (k n : ℕ) : ℕ :=
  k ^ n

/-- Surjections from an `n`-set onto a two-element set. -/
def twoSurjectionCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (n + 1) - 2

/-- Finite audit: surjections are bounded by all words/functions. -/
def surjectionWordEnvelopeCheck (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n =>
    twoSurjectionCount n ≤ wordFunctionCount 2 n

theorem twoSurjectionCount_samples :
    twoSurjectionCount 0 = 0 ∧
    twoSurjectionCount 1 = 0 ∧
    twoSurjectionCount 2 = 2 ∧
    twoSurjectionCount 3 = 6 ∧
    twoSurjectionCount 4 = 14 := by
  native_decide

theorem surjectionWordEnvelope_window :
    surjectionWordEnvelopeCheck 16 = true := by
  unfold surjectionWordEnvelopeCheck twoSurjectionCount wordFunctionCount
  native_decide

/-- Finite recurrence audit for two-colour surjections. -/
def twoSurjectionRecurrenceCheck (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    twoSurjectionCount (n + 2) = 2 * twoSurjectionCount (n + 1) + 2

theorem twoSurjection_recurrenceWindow :
    twoSurjectionRecurrenceCheck 12 = true := by
  unfold twoSurjectionRecurrenceCheck twoSurjectionCount
  native_decide

structure SurjectionsSetPartitionsWordsBudgetCertificate where
  surjectionWindow : ℕ
  partitionWindow : ℕ
  wordWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SurjectionsSetPartitionsWordsBudgetCertificate.controlled
    (c : SurjectionsSetPartitionsWordsBudgetCertificate) : Prop :=
  0 < c.surjectionWindow ∧
    c.wordWindow ≤ c.surjectionWindow + c.partitionWindow + c.slack

def SurjectionsSetPartitionsWordsBudgetCertificate.budgetControlled
    (c : SurjectionsSetPartitionsWordsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.surjectionWindow + c.partitionWindow + c.wordWindow + c.slack

def SurjectionsSetPartitionsWordsBudgetCertificate.Ready
    (c : SurjectionsSetPartitionsWordsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def SurjectionsSetPartitionsWordsBudgetCertificate.size
    (c : SurjectionsSetPartitionsWordsBudgetCertificate) : ℕ :=
  c.surjectionWindow + c.partitionWindow + c.wordWindow + c.slack

theorem surjectionsSetPartitionsWords_budgetCertificate_le_size
    (c : SurjectionsSetPartitionsWordsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleSurjectionsSetPartitionsWordsBudgetCertificate :
    SurjectionsSetPartitionsWordsBudgetCertificate :=
  { surjectionWindow := 5
    partitionWindow := 6
    wordWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleSurjectionsSetPartitionsWordsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsSetPartitionsWordsBudgetCertificate.controlled,
      sampleSurjectionsSetPartitionsWordsBudgetCertificate]
  · norm_num [SurjectionsSetPartitionsWordsBudgetCertificate.budgetControlled,
      sampleSurjectionsSetPartitionsWordsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleSurjectionsSetPartitionsWordsBudgetCertificate.certificateBudgetWindow ≤
      sampleSurjectionsSetPartitionsWordsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleSurjectionsSetPartitionsWordsBudgetCertificate.Ready := by
  constructor
  · norm_num [SurjectionsSetPartitionsWordsBudgetCertificate.controlled,
      sampleSurjectionsSetPartitionsWordsBudgetCertificate]
  · norm_num [SurjectionsSetPartitionsWordsBudgetCertificate.budgetControlled,
      sampleSurjectionsSetPartitionsWordsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List SurjectionsSetPartitionsWordsBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleSurjectionsSetPartitionsWordsBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleSurjectionsSetPartitionsWordsBudgetCertificate
  native_decide

example :
    budgetCertificateListReady
      [sampleSurjectionsSetPartitionsWordsBudgetCertificate] = true := by
  exact budgetCertificateList_readyWindow

end AnalyticCombinatorics.PartA.Ch2.SurjectionsSetPartitionsWords
