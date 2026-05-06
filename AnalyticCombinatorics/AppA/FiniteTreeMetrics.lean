import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite tree metrics.

The module gives simple size, leaf, and height budgets for tree-shaped
specifications represented by finite records.
-/

namespace AnalyticCombinatorics.AppA.FiniteTreeMetrics

structure TreeProfile where
  nodes : ℕ
  leaves : ℕ
  height : ℕ
deriving DecidableEq, Repr

def validTreeProfile (t : TreeProfile) : Prop :=
  0 < t.nodes ∧ t.leaves ≤ t.nodes ∧ t.height ≤ t.nodes

def internalNodes (t : TreeProfile) : ℕ :=
  t.nodes - t.leaves

def profileBudget (t : TreeProfile) : ℕ :=
  t.nodes + t.height

theorem validTreeProfile.leaves_le {t : TreeProfile}
    (h : validTreeProfile t) :
    t.leaves ≤ t.nodes := h.2.1

theorem profileBudget_ge_nodes (t : TreeProfile) :
    t.nodes ≤ profileBudget t := by
  unfold profileBudget
  omega

def sampleTreeProfile : TreeProfile :=
  { nodes := 7, leaves := 4, height := 3 }

example : validTreeProfile sampleTreeProfile := by
  norm_num [validTreeProfile, sampleTreeProfile]

example : internalNodes sampleTreeProfile = 3 := by
  native_decide

example : profileBudget sampleTreeProfile = 10 := by
  native_decide

structure TreeMetricWindow where
  nodes : ℕ
  leaves : ℕ
  internalNodes : ℕ
  height : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeMetricWindow.nodeBalance (w : TreeMetricWindow) : Prop :=
  w.leaves + w.internalNodes ≤ w.nodes + w.slack

def TreeMetricWindow.heightControlled (w : TreeMetricWindow) : Prop :=
  w.height ≤ w.nodes + w.slack

def TreeMetricWindow.ready (w : TreeMetricWindow) : Prop :=
  0 < w.nodes ∧ w.nodeBalance ∧ w.heightControlled

def TreeMetricWindow.certificate (w : TreeMetricWindow) : ℕ :=
  w.nodes + w.leaves + w.internalNodes + w.height + w.slack

theorem leaves_le_certificate (w : TreeMetricWindow) :
    w.leaves ≤ w.certificate := by
  unfold TreeMetricWindow.certificate
  omega

def sampleTreeMetricWindow : TreeMetricWindow :=
  { nodes := 7, leaves := 4, internalNodes := 3, height := 3, slack := 0 }

example : sampleTreeMetricWindow.ready := by
  norm_num [sampleTreeMetricWindow, TreeMetricWindow.ready,
    TreeMetricWindow.nodeBalance, TreeMetricWindow.heightControlled]


structure FiniteTreeMetricsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteTreeMetricsBudgetCertificate.controlled
    (c : FiniteTreeMetricsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteTreeMetricsBudgetCertificate.budgetControlled
    (c : FiniteTreeMetricsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteTreeMetricsBudgetCertificate.Ready
    (c : FiniteTreeMetricsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteTreeMetricsBudgetCertificate.size
    (c : FiniteTreeMetricsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteTreeMetrics_budgetCertificate_le_size
    (c : FiniteTreeMetricsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteTreeMetricsBudgetCertificate :
    FiniteTreeMetricsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteTreeMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTreeMetricsBudgetCertificate.controlled,
      sampleFiniteTreeMetricsBudgetCertificate]
  · norm_num [FiniteTreeMetricsBudgetCertificate.budgetControlled,
      sampleFiniteTreeMetricsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteTreeMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTreeMetricsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteTreeMetricsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTreeMetricsBudgetCertificate.controlled,
      sampleFiniteTreeMetricsBudgetCertificate]
  · norm_num [FiniteTreeMetricsBudgetCertificate.budgetControlled,
      sampleFiniteTreeMetricsBudgetCertificate]

example :
    sampleFiniteTreeMetricsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTreeMetricsBudgetCertificate.size := by
  apply finiteTreeMetrics_budgetCertificate_le_size
  constructor
  · norm_num [FiniteTreeMetricsBudgetCertificate.controlled,
      sampleFiniteTreeMetricsBudgetCertificate]
  · norm_num [FiniteTreeMetricsBudgetCertificate.budgetControlled,
      sampleFiniteTreeMetricsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteTreeMetricsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteTreeMetricsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteTreeMetricsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteTreeMetrics
