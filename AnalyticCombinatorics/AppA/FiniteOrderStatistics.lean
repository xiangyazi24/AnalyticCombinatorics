import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite order-statistic helpers for coefficient samples.

These list-based definitions support small ranked samples used in
probabilistic combinatorics examples.
-/

namespace AnalyticCombinatorics.AppA.FiniteOrderStatistics

def belowOrEqualCount (threshold : ℕ) (xs : List ℕ) : ℕ :=
  xs.filter (fun x => x ≤ threshold) |>.length

def aboveCount (threshold : ℕ) (xs : List ℕ) : ℕ :=
  xs.filter (fun x => threshold < x) |>.length

def sampleSize (xs : List ℕ) : ℕ :=
  xs.length

theorem belowOrEqualCount_nil (threshold : ℕ) :
    belowOrEqualCount threshold [] = 0 := by
  rfl

theorem aboveCount_nil (threshold : ℕ) :
    aboveCount threshold [] = 0 := by
  rfl

theorem sampleSize_cons (x : ℕ) (xs : List ℕ) :
    sampleSize (x :: xs) = sampleSize xs + 1 := by
  simp [sampleSize]

def sampleRanks : List ℕ :=
  [4, 1, 7, 3, 7, 2]

example : belowOrEqualCount 3 sampleRanks = 3 := by
  native_decide

example : aboveCount 3 sampleRanks = 3 := by
  native_decide

example : sampleSize sampleRanks = 6 := by
  native_decide

structure OrderStatisticWindow where
  sampleCardinality : ℕ
  threshold : ℕ
  belowOrEqual : ℕ
  above : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def OrderStatisticWindow.partitionReady (w : OrderStatisticWindow) : Prop :=
  w.belowOrEqual + w.above = w.sampleCardinality

def OrderStatisticWindow.thresholdControlled (w : OrderStatisticWindow) : Prop :=
  w.threshold ≤ w.sampleCardinality + w.slack

def OrderStatisticWindow.ready (w : OrderStatisticWindow) : Prop :=
  w.partitionReady ∧ w.thresholdControlled

def OrderStatisticWindow.certificate (w : OrderStatisticWindow) : ℕ :=
  w.sampleCardinality + w.threshold + w.belowOrEqual + w.above + w.slack

theorem above_le_certificate (w : OrderStatisticWindow) :
    w.above ≤ w.certificate := by
  unfold OrderStatisticWindow.certificate
  omega

def sampleOrderStatisticWindow : OrderStatisticWindow :=
  { sampleCardinality := 6, threshold := 3, belowOrEqual := 3, above := 3, slack := 0 }

example : sampleOrderStatisticWindow.ready := by
  norm_num [sampleOrderStatisticWindow, OrderStatisticWindow.ready,
    OrderStatisticWindow.partitionReady, OrderStatisticWindow.thresholdControlled]


structure FiniteOrderStatisticsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteOrderStatisticsBudgetCertificate.controlled
    (c : FiniteOrderStatisticsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteOrderStatisticsBudgetCertificate.budgetControlled
    (c : FiniteOrderStatisticsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteOrderStatisticsBudgetCertificate.Ready
    (c : FiniteOrderStatisticsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteOrderStatisticsBudgetCertificate.size
    (c : FiniteOrderStatisticsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteOrderStatistics_budgetCertificate_le_size
    (c : FiniteOrderStatisticsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteOrderStatisticsBudgetCertificate :
    FiniteOrderStatisticsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteOrderStatisticsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrderStatisticsBudgetCertificate.controlled,
      sampleFiniteOrderStatisticsBudgetCertificate]
  · norm_num [FiniteOrderStatisticsBudgetCertificate.budgetControlled,
      sampleFiniteOrderStatisticsBudgetCertificate]

example :
    sampleFiniteOrderStatisticsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrderStatisticsBudgetCertificate.size := by
  apply finiteOrderStatistics_budgetCertificate_le_size
  constructor
  · norm_num [FiniteOrderStatisticsBudgetCertificate.controlled,
      sampleFiniteOrderStatisticsBudgetCertificate]
  · norm_num [FiniteOrderStatisticsBudgetCertificate.budgetControlled,
      sampleFiniteOrderStatisticsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteOrderStatisticsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteOrderStatisticsBudgetCertificate.controlled,
      sampleFiniteOrderStatisticsBudgetCertificate]
  · norm_num [FiniteOrderStatisticsBudgetCertificate.budgetControlled,
      sampleFiniteOrderStatisticsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteOrderStatisticsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteOrderStatisticsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List FiniteOrderStatisticsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteOrderStatisticsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteOrderStatisticsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteOrderStatistics
