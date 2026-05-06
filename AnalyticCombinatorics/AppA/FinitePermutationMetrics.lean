import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite permutation metrics.

Permutations are list-encoded samples.  These metrics are used for small
permutation-statistics checks.
-/

namespace AnalyticCombinatorics.AppA.FinitePermutationMetrics

def descentCount (xs : List ℕ) : ℕ :=
  (xs.zip xs.tail).filter (fun pair => pair.2 < pair.1) |>.length

def fixedPointCount (xs : List ℕ) : ℕ :=
  (List.range xs.length).filter (fun i => xs.getD i 0 == i) |>.length

def inversionWitnessCount (xs : List ℕ) : ℕ :=
  (List.range xs.length).map
    (fun i => (List.range i).filter (fun j => xs.getD j 0 > xs.getD i 0) |>.length) |>.sum

theorem descentCount_nil :
    descentCount [] = 0 := by
  rfl

theorem fixedPointCount_nil :
    fixedPointCount [] = 0 := by
  rfl

def samplePermutation : List ℕ :=
  [2, 0, 3, 1]

example : descentCount samplePermutation = 2 := by
  native_decide

example : fixedPointCount samplePermutation = 0 := by
  native_decide

example : inversionWitnessCount samplePermutation = 3 := by
  native_decide

structure PermutationMetricWindow where
  length : ℕ
  descents : ℕ
  fixedPoints : ℕ
  inversions : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PermutationMetricWindow.descentsControlled (w : PermutationMetricWindow) : Prop :=
  w.descents ≤ w.length + w.slack

def PermutationMetricWindow.fixedPointsControlled (w : PermutationMetricWindow) : Prop :=
  w.fixedPoints ≤ w.length

def PermutationMetricWindow.inversionBudget (w : PermutationMetricWindow) : ℕ :=
  w.length * w.length + w.slack

def PermutationMetricWindow.ready (w : PermutationMetricWindow) : Prop :=
  w.descentsControlled ∧ w.fixedPointsControlled ∧ w.inversions ≤ w.inversionBudget

def PermutationMetricWindow.certificate (w : PermutationMetricWindow) : ℕ :=
  w.length + w.descents + w.fixedPoints + w.inversions + w.slack

theorem inversions_le_certificate (w : PermutationMetricWindow) :
    w.inversions ≤ w.certificate := by
  unfold PermutationMetricWindow.certificate
  omega

def samplePermutationMetricWindow : PermutationMetricWindow :=
  { length := 4, descents := 2, fixedPoints := 0, inversions := 3, slack := 0 }

example : samplePermutationMetricWindow.ready := by
  norm_num [samplePermutationMetricWindow, PermutationMetricWindow.ready,
    PermutationMetricWindow.descentsControlled, PermutationMetricWindow.fixedPointsControlled,
    PermutationMetricWindow.inversionBudget]


structure FinitePermutationMetricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePermutationMetricsBudgetCertificate.controlled
    (c : FinitePermutationMetricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePermutationMetricsBudgetCertificate.budgetControlled
    (c : FinitePermutationMetricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePermutationMetricsBudgetCertificate.Ready
    (c : FinitePermutationMetricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePermutationMetricsBudgetCertificate.size
    (c : FinitePermutationMetricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePermutationMetrics_budgetCertificate_le_size
    (c : FinitePermutationMetricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePermutationMetricsBudgetCertificate :
    FinitePermutationMetricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePermutationMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePermutationMetricsBudgetCertificate.controlled,
      sampleFinitePermutationMetricsBudgetCertificate]
  · norm_num [FinitePermutationMetricsBudgetCertificate.budgetControlled,
      sampleFinitePermutationMetricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePermutationMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePermutationMetricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePermutationMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePermutationMetricsBudgetCertificate.controlled,
      sampleFinitePermutationMetricsBudgetCertificate]
  · norm_num [FinitePermutationMetricsBudgetCertificate.budgetControlled,
      sampleFinitePermutationMetricsBudgetCertificate]

example :
    sampleFinitePermutationMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePermutationMetricsBudgetCertificate.size := by
  apply finitePermutationMetrics_budgetCertificate_le_size
  constructor
  · norm_num [FinitePermutationMetricsBudgetCertificate.controlled,
      sampleFinitePermutationMetricsBudgetCertificate]
  · norm_num [FinitePermutationMetricsBudgetCertificate.budgetControlled,
      sampleFinitePermutationMetricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FinitePermutationMetricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePermutationMetricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePermutationMetricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePermutationMetrics
