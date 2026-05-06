import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random network limit schema bookkeeping.

The finite data records node budget, edge budget, and variance budget for
random network asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomNetworkLimitSchemas

structure RandomNetworkData where
  nodeBudget : ℕ
  edgeBudget : ℕ
  varianceBudget : ℕ
deriving DecidableEq, Repr

def positiveNodeBudget (d : RandomNetworkData) : Prop :=
  0 < d.nodeBudget

def edgeBudgetControlled (d : RandomNetworkData) : Prop :=
  d.edgeBudget ≤ d.nodeBudget * d.nodeBudget

def randomNetworkReady (d : RandomNetworkData) : Prop :=
  positiveNodeBudget d ∧ edgeBudgetControlled d

def networkBudget (d : RandomNetworkData) : ℕ :=
  d.nodeBudget + d.edgeBudget + d.varianceBudget

theorem randomNetworkReady.nodes {d : RandomNetworkData}
    (h : randomNetworkReady d) :
    positiveNodeBudget d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem nodeBudget_le_networkBudget (d : RandomNetworkData) :
    d.nodeBudget ≤ networkBudget d := by
  unfold networkBudget
  omega

def sampleNetwork : RandomNetworkData :=
  { nodeBudget := 6, edgeBudget := 14, varianceBudget := 5 }

example : randomNetworkReady sampleNetwork := by
  norm_num [randomNetworkReady, positiveNodeBudget, edgeBudgetControlled, sampleNetwork]

example : networkBudget sampleNetwork = 25 := by
  native_decide

/-- Finite executable readiness audit for random network limit data. -/
def randomNetworkDataListReady
    (data : List RandomNetworkData) : Bool :=
  data.all fun d =>
    0 < d.nodeBudget && d.edgeBudget ≤ d.nodeBudget * d.nodeBudget

theorem randomNetworkDataList_readyWindow :
    randomNetworkDataListReady
      [{ nodeBudget := 4, edgeBudget := 8, varianceBudget := 3 },
       { nodeBudget := 6, edgeBudget := 14, varianceBudget := 5 }] = true := by
  unfold randomNetworkDataListReady
  native_decide

structure RandomNetworkWindow where
  nodeBudget : ℕ
  edgeBudget : ℕ
  varianceBudget : ℕ
  flowBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomNetworkWindow.edgeControlled (w : RandomNetworkWindow) : Prop :=
  w.edgeBudget ≤ w.nodeBudget * w.nodeBudget

def RandomNetworkWindow.flowControlled (w : RandomNetworkWindow) : Prop :=
  w.flowBudget ≤ w.edgeBudget + w.varianceBudget + w.slack

def randomNetworkWindowReady (w : RandomNetworkWindow) : Prop :=
  0 < w.nodeBudget ∧
    w.edgeControlled ∧
    w.flowControlled

def RandomNetworkWindow.certificate (w : RandomNetworkWindow) : ℕ :=
  w.edgeBudget + w.varianceBudget + w.slack

theorem randomNetwork_flowBudget_le_certificate {w : RandomNetworkWindow}
    (h : randomNetworkWindowReady w) :
    w.flowBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hflow⟩
  exact hflow

def sampleRandomNetworkWindow : RandomNetworkWindow :=
  { nodeBudget := 6, edgeBudget := 14, varianceBudget := 5, flowBudget := 18, slack := 0 }

example : randomNetworkWindowReady sampleRandomNetworkWindow := by
  norm_num [randomNetworkWindowReady, RandomNetworkWindow.edgeControlled,
    RandomNetworkWindow.flowControlled, sampleRandomNetworkWindow]

example : sampleRandomNetworkWindow.certificate = 19 := by
  native_decide


structure RandomNetworkLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomNetworkLimitSchemasBudgetCertificate.controlled
    (c : RandomNetworkLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomNetworkLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomNetworkLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomNetworkLimitSchemasBudgetCertificate.Ready
    (c : RandomNetworkLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomNetworkLimitSchemasBudgetCertificate.size
    (c : RandomNetworkLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomNetworkLimitSchemas_budgetCertificate_le_size
    (c : RandomNetworkLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomNetworkLimitSchemasBudgetCertificate :
    RandomNetworkLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleRandomNetworkLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.controlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]

example :
    sampleRandomNetworkLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomNetworkLimitSchemasBudgetCertificate.size := by
  apply randomNetworkLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.controlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleRandomNetworkLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.controlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]
  · norm_num [RandomNetworkLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomNetworkLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomNetworkLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomNetworkLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List RandomNetworkLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomNetworkLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomNetworkLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomNetworkLimitSchemas
