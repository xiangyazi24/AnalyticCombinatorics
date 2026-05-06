import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random cluster limit schemas.

The finite schema records cluster count, interaction budget, and scaling
slack.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomClusterLimitSchemas

structure RandomClusterLimitData where
  clusterCount : ℕ
  interactionBudget : ℕ
  scalingSlack : ℕ
deriving DecidableEq, Repr

def clusterCountPositive (d : RandomClusterLimitData) : Prop :=
  0 < d.clusterCount

def interactionsControlled (d : RandomClusterLimitData) : Prop :=
  d.interactionBudget ≤ d.clusterCount + d.scalingSlack

def randomClusterLimitReady (d : RandomClusterLimitData) : Prop :=
  clusterCountPositive d ∧ interactionsControlled d

def randomClusterLimitBudget (d : RandomClusterLimitData) : ℕ :=
  d.clusterCount + d.interactionBudget + d.scalingSlack

theorem randomClusterLimitReady.clusters {d : RandomClusterLimitData}
    (h : randomClusterLimitReady d) :
    clusterCountPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem interactionBudget_le_clusterLimitBudget
    (d : RandomClusterLimitData) :
    d.interactionBudget ≤ randomClusterLimitBudget d := by
  unfold randomClusterLimitBudget
  omega

def sampleRandomClusterLimitData : RandomClusterLimitData :=
  { clusterCount := 7, interactionBudget := 9, scalingSlack := 3 }

example : randomClusterLimitReady sampleRandomClusterLimitData := by
  norm_num [randomClusterLimitReady, clusterCountPositive]
  norm_num [interactionsControlled, sampleRandomClusterLimitData]

example : randomClusterLimitBudget sampleRandomClusterLimitData = 19 := by
  native_decide

/-- Finite executable readiness audit for random cluster-limit windows. -/
def randomClusterLimitListReady
    (windows : List RandomClusterLimitData) : Bool :=
  windows.all fun d =>
    0 < d.clusterCount && d.interactionBudget ≤ d.clusterCount + d.scalingSlack

theorem randomClusterLimitList_readyWindow :
    randomClusterLimitListReady
      [{ clusterCount := 4, interactionBudget := 5, scalingSlack := 1 },
       { clusterCount := 7, interactionBudget := 9, scalingSlack := 3 }] =
      true := by
  unfold randomClusterLimitListReady
  native_decide

structure RandomClusterLimitBudgetCertificate where
  clusterCountWindow : ℕ
  interactionBudgetWindow : ℕ
  scalingSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomClusterLimitBudgetCertificate.controlled
    (c : RandomClusterLimitBudgetCertificate) : Prop :=
  0 < c.clusterCountWindow ∧
    c.interactionBudgetWindow ≤
      c.clusterCountWindow + c.scalingSlackWindow + c.slack

def RandomClusterLimitBudgetCertificate.budgetControlled
    (c : RandomClusterLimitBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.clusterCountWindow + c.interactionBudgetWindow + c.scalingSlackWindow +
      c.slack

def RandomClusterLimitBudgetCertificate.Ready
    (c : RandomClusterLimitBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomClusterLimitBudgetCertificate.size
    (c : RandomClusterLimitBudgetCertificate) : ℕ :=
  c.clusterCountWindow + c.interactionBudgetWindow + c.scalingSlackWindow +
    c.slack

theorem randomClusterLimit_budgetCertificate_le_size
    (c : RandomClusterLimitBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomClusterLimitBudgetCertificate :
    RandomClusterLimitBudgetCertificate :=
  { clusterCountWindow := 7
    interactionBudgetWindow := 9
    scalingSlackWindow := 3
    certificateBudgetWindow := 20
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomClusterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomClusterLimitBudgetCertificate.controlled,
      sampleRandomClusterLimitBudgetCertificate]
  · norm_num [RandomClusterLimitBudgetCertificate.budgetControlled,
      sampleRandomClusterLimitBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomClusterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomClusterLimitBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomClusterLimitBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomClusterLimitBudgetCertificate.controlled,
      sampleRandomClusterLimitBudgetCertificate]
  · norm_num [RandomClusterLimitBudgetCertificate.budgetControlled,
      sampleRandomClusterLimitBudgetCertificate]

example :
    sampleRandomClusterLimitBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomClusterLimitBudgetCertificate.size := by
  apply randomClusterLimit_budgetCertificate_le_size
  constructor
  · norm_num [RandomClusterLimitBudgetCertificate.controlled,
      sampleRandomClusterLimitBudgetCertificate]
  · norm_num [RandomClusterLimitBudgetCertificate.budgetControlled,
      sampleRandomClusterLimitBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomClusterLimitBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomClusterLimitBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomClusterLimitBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomClusterLimitSchemas
