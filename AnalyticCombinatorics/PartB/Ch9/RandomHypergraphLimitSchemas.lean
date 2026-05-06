import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Random hypergraph limit schema bookkeeping.

The finite record stores vertex budget, hyperedge budget, and rank budget
for random hypergraph asymptotics.
-/

namespace AnalyticCombinatorics.PartB.Ch9.RandomHypergraphLimitSchemas

structure RandomHypergraphData where
  vertexBudget : ℕ
  hyperedgeBudget : ℕ
  rankBudget : ℕ
deriving DecidableEq, Repr

def positiveVertices (d : RandomHypergraphData) : Prop :=
  0 < d.vertexBudget

def positiveRank (d : RandomHypergraphData) : Prop :=
  0 < d.rankBudget

def hyperedgeBudgetControlled (d : RandomHypergraphData) : Prop :=
  d.hyperedgeBudget ≤ d.vertexBudget ^ d.rankBudget

def randomHypergraphReady (d : RandomHypergraphData) : Prop :=
  positiveVertices d ∧ positiveRank d ∧ hyperedgeBudgetControlled d

def hypergraphBudget (d : RandomHypergraphData) : ℕ :=
  d.vertexBudget + d.hyperedgeBudget + d.rankBudget

theorem randomHypergraphReady.vertices {d : RandomHypergraphData}
    (h : randomHypergraphReady d) :
    positiveVertices d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

def sampleHypergraph : RandomHypergraphData :=
  { vertexBudget := 4, hyperedgeBudget := 10, rankBudget := 2 }

example : randomHypergraphReady sampleHypergraph := by
  norm_num
    [randomHypergraphReady, positiveVertices, positiveRank, hyperedgeBudgetControlled,
      sampleHypergraph]

example : hypergraphBudget sampleHypergraph = 16 := by
  native_decide

/-- Finite executable readiness audit for random hypergraph data. -/
def randomHypergraphDataListReady
    (data : List RandomHypergraphData) : Bool :=
  data.all fun d =>
    0 < d.vertexBudget &&
      0 < d.rankBudget &&
        d.hyperedgeBudget ≤ d.vertexBudget ^ d.rankBudget

theorem randomHypergraphDataList_readyWindow :
    randomHypergraphDataListReady
      [{ vertexBudget := 3, hyperedgeBudget := 6, rankBudget := 2 },
       { vertexBudget := 4, hyperedgeBudget := 10, rankBudget := 2 }] = true := by
  unfold randomHypergraphDataListReady
  native_decide

structure RandomHypergraphWindow where
  vertexBudget : ℕ
  hyperedgeBudget : ℕ
  rankBudget : ℕ
  incidenceBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomHypergraphWindow.hyperedgeControlled (w : RandomHypergraphWindow) : Prop :=
  w.hyperedgeBudget ≤ w.vertexBudget ^ w.rankBudget

def RandomHypergraphWindow.incidenceControlled (w : RandomHypergraphWindow) : Prop :=
  w.incidenceBudget ≤ w.hyperedgeBudget * w.rankBudget + w.slack

def randomHypergraphWindowReady (w : RandomHypergraphWindow) : Prop :=
  0 < w.vertexBudget ∧
    0 < w.rankBudget ∧
    w.hyperedgeControlled ∧
    w.incidenceControlled

def RandomHypergraphWindow.certificate (w : RandomHypergraphWindow) : ℕ :=
  w.hyperedgeBudget * w.rankBudget + w.slack

theorem randomHypergraph_incidenceBudget_le_certificate {w : RandomHypergraphWindow}
    (h : randomHypergraphWindowReady w) :
    w.incidenceBudget ≤ w.certificate := by
  rcases h with ⟨_, _, _, hinc⟩
  exact hinc

def sampleRandomHypergraphWindow : RandomHypergraphWindow :=
  { vertexBudget := 4, hyperedgeBudget := 10, rankBudget := 2, incidenceBudget := 18,
    slack := 0 }

example : randomHypergraphWindowReady sampleRandomHypergraphWindow := by
  norm_num [randomHypergraphWindowReady, RandomHypergraphWindow.hyperedgeControlled,
    RandomHypergraphWindow.incidenceControlled, sampleRandomHypergraphWindow]

example : sampleRandomHypergraphWindow.certificate = 20 := by
  native_decide


structure RandomHypergraphLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RandomHypergraphLimitSchemasBudgetCertificate.controlled
    (c : RandomHypergraphLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def RandomHypergraphLimitSchemasBudgetCertificate.budgetControlled
    (c : RandomHypergraphLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def RandomHypergraphLimitSchemasBudgetCertificate.Ready
    (c : RandomHypergraphLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def RandomHypergraphLimitSchemasBudgetCertificate.size
    (c : RandomHypergraphLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem randomHypergraphLimitSchemas_budgetCertificate_le_size
    (c : RandomHypergraphLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleRandomHypergraphLimitSchemasBudgetCertificate :
    RandomHypergraphLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleRandomHypergraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleRandomHypergraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomHypergraphLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleRandomHypergraphLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]

example :
    sampleRandomHypergraphLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleRandomHypergraphLimitSchemasBudgetCertificate.size := by
  apply randomHypergraphLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.controlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]
  · norm_num [RandomHypergraphLimitSchemasBudgetCertificate.budgetControlled,
      sampleRandomHypergraphLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List RandomHypergraphLimitSchemasBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleRandomHypergraphLimitSchemasBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleRandomHypergraphLimitSchemasBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch9.RandomHypergraphLimitSchemas
