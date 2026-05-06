import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Combinatorial probability.
-/

namespace AnalyticCombinatorics.AppA.CombinatorialProbability

/-- Conditional probability from finite counts. -/
def conditionalProbabilityQ (eventAndCondition condition : ℕ) : ℚ :=
  eventAndCondition / (condition : ℚ)

/-- Finite Bayes-window audit by count inequalities. -/
def conditionalEventBoundedUpTo
    (eventAndCondition condition : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => eventAndCondition n ≤ condition n

def evenSubsetCondition (n : ℕ) : ℕ :=
  2 ^ n

def distinguishedEvenSubsetEvent : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ n

theorem conditionalDistinguished_window :
    conditionalEventBoundedUpTo distinguishedEvenSubsetEvent evenSubsetCondition 12 = true := by
  unfold conditionalEventBoundedUpTo distinguishedEvenSubsetEvent
    evenSubsetCondition
  native_decide

example : conditionalProbabilityQ 3 12 = 1 / 4 := by
  unfold conditionalProbabilityQ
  native_decide

example :
    conditionalEventBoundedUpTo
      distinguishedEvenSubsetEvent evenSubsetCondition 4 = true := by
  unfold conditionalEventBoundedUpTo distinguishedEvenSubsetEvent
    evenSubsetCondition
  native_decide

/-- Rational probability from finite counts. -/
def probabilityQ (eventCount sampleCount : ℕ) : ℚ :=
  eventCount / (sampleCount : ℚ)

/-- Finite probability audit: an event count is bounded by the sample space. -/
def eventBoundedUpTo
    (event sample : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => event n ≤ sample n

/-- Binomial sample-space size for subsets of an `n`-set. -/
def subsetSampleSpace (n : ℕ) : ℕ :=
  2 ^ n

/-- Event: subsets with a distinguished element, for `n > 0`. -/
def distinguishedElementEvent : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ n

def FiniteProbabilityWindow (event sample : ℕ → ℕ) (N : ℕ) : Prop :=
  eventBoundedUpTo event sample N = true

theorem distinguishedElement_probability_samples :
    probabilityQ (distinguishedElementEvent 1) (subsetSampleSpace 1) = 1 / 2 ∧
    probabilityQ (distinguishedElementEvent 2) (subsetSampleSpace 2) = 1 / 2 ∧
    probabilityQ (distinguishedElementEvent 3) (subsetSampleSpace 3) = 1 / 2 := by
  unfold probabilityQ distinguishedElementEvent subsetSampleSpace
  native_decide

theorem distinguishedElement_finiteProbabilityWindow :
    FiniteProbabilityWindow distinguishedElementEvent subsetSampleSpace 16 := by
  unfold FiniteProbabilityWindow eventBoundedUpTo distinguishedElementEvent
    subsetSampleSpace
  native_decide

structure CombinatorialProbabilityBudgetCertificate where
  sampleSpaceWindow : ℕ
  eventWindow : ℕ
  probabilityWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CombinatorialProbabilityBudgetCertificate.controlled
    (c : CombinatorialProbabilityBudgetCertificate) : Prop :=
  0 < c.sampleSpaceWindow ∧
    c.probabilityWindow ≤ c.sampleSpaceWindow + c.eventWindow + c.slack

def CombinatorialProbabilityBudgetCertificate.budgetControlled
    (c : CombinatorialProbabilityBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.sampleSpaceWindow + c.eventWindow + c.probabilityWindow + c.slack

def CombinatorialProbabilityBudgetCertificate.Ready
    (c : CombinatorialProbabilityBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def CombinatorialProbabilityBudgetCertificate.size
    (c : CombinatorialProbabilityBudgetCertificate) : ℕ :=
  c.sampleSpaceWindow + c.eventWindow + c.probabilityWindow + c.slack

theorem combinatorialProbability_budgetCertificate_le_size
    (c : CombinatorialProbabilityBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  exact h.2

def sampleCombinatorialProbabilityBudgetCertificate :
    CombinatorialProbabilityBudgetCertificate :=
  { sampleSpaceWindow := 5
    eventWindow := 6
    probabilityWindow := 10
    certificateBudgetWindow := 22
    slack := 1 }

example : sampleCombinatorialProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialProbabilityBudgetCertificate.controlled,
      sampleCombinatorialProbabilityBudgetCertificate]
  · norm_num [CombinatorialProbabilityBudgetCertificate.budgetControlled,
      sampleCombinatorialProbabilityBudgetCertificate]

/-- Finite executable readiness audit for combinatorial-probability certificates. -/
def combinatorialProbabilityBudgetCertificateListReady
    (data : List CombinatorialProbabilityBudgetCertificate) : Bool :=
  data.all fun c =>
    0 < c.sampleSpaceWindow &&
      c.probabilityWindow ≤ c.sampleSpaceWindow + c.eventWindow + c.slack &&
        c.certificateBudgetWindow ≤
          c.sampleSpaceWindow + c.eventWindow + c.probabilityWindow + c.slack

theorem combinatorialProbabilityBudgetCertificateList_readyWindow :
    combinatorialProbabilityBudgetCertificateListReady
      [sampleCombinatorialProbabilityBudgetCertificate,
       { sampleSpaceWindow := 4, eventWindow := 5, probabilityWindow := 8,
         certificateBudgetWindow := 18, slack := 1 }] = true := by
  unfold combinatorialProbabilityBudgetCertificateListReady
    sampleCombinatorialProbabilityBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleCombinatorialProbabilityBudgetCertificate.Ready := by
  constructor
  · norm_num [CombinatorialProbabilityBudgetCertificate.controlled,
      sampleCombinatorialProbabilityBudgetCertificate]
  · norm_num [CombinatorialProbabilityBudgetCertificate.budgetControlled,
      sampleCombinatorialProbabilityBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleCombinatorialProbabilityBudgetCertificate.certificateBudgetWindow ≤
      sampleCombinatorialProbabilityBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List CombinatorialProbabilityBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleCombinatorialProbabilityBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleCombinatorialProbabilityBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.CombinatorialProbability
