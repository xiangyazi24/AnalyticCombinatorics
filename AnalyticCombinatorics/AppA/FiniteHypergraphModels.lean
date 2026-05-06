import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite hypergraph models.

The finite schema stores vertex, hyperedge, and incidence budgets.
-/

namespace AnalyticCombinatorics.AppA.FiniteHypergraphModels

structure HypergraphData where
  vertices : ℕ
  hyperedges : ℕ
  incidences : ℕ
deriving DecidableEq, Repr

def hypergraphNonempty (d : HypergraphData) : Prop :=
  0 < d.vertices

def hyperedgesControlled (d : HypergraphData) : Prop :=
  d.hyperedges ≤ d.vertices + d.incidences

def hypergraphReady (d : HypergraphData) : Prop :=
  hypergraphNonempty d ∧ hyperedgesControlled d

def hypergraphBudget (d : HypergraphData) : ℕ :=
  d.vertices + d.hyperedges + d.incidences

theorem hypergraphReady.vertices {d : HypergraphData}
    (h : hypergraphReady d) :
    hypergraphNonempty d ∧ hyperedgesControlled d ∧ d.hyperedges ≤ hypergraphBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold hypergraphBudget
  omega

theorem incidences_le_hypergraphBudget (d : HypergraphData) :
    d.incidences ≤ hypergraphBudget d := by
  unfold hypergraphBudget
  omega

def sampleHypergraphData : HypergraphData :=
  { vertices := 6, hyperedges := 8, incidences := 4 }

example : hypergraphReady sampleHypergraphData := by
  norm_num [hypergraphReady, hypergraphNonempty]
  norm_num [hyperedgesControlled, sampleHypergraphData]

example : hypergraphBudget sampleHypergraphData = 18 := by
  native_decide

structure HypergraphWindow where
  vertices : ℕ
  hyperedges : ℕ
  incidences : ℕ
  rankBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HypergraphWindow.hyperedgesControlled (w : HypergraphWindow) : Prop :=
  w.hyperedges ≤ w.vertices + w.incidences + w.slack

def HypergraphWindow.rankControlled (w : HypergraphWindow) : Prop :=
  w.rankBudget ≤ w.vertices + w.hyperedges + w.incidences + w.slack

def hypergraphWindowReady (w : HypergraphWindow) : Prop :=
  0 < w.vertices ∧
    w.hyperedgesControlled ∧
    w.rankControlled

def HypergraphWindow.certificate (w : HypergraphWindow) : ℕ :=
  w.vertices + w.hyperedges + w.incidences + w.slack

theorem hypergraph_rankBudget_le_certificate {w : HypergraphWindow}
    (h : hypergraphWindowReady w) :
    w.rankBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hrank⟩
  exact hrank

def sampleHypergraphWindow : HypergraphWindow :=
  { vertices := 6, hyperedges := 8, incidences := 4, rankBudget := 15, slack := 0 }

example : hypergraphWindowReady sampleHypergraphWindow := by
  norm_num [hypergraphWindowReady, HypergraphWindow.hyperedgesControlled,
    HypergraphWindow.rankControlled, sampleHypergraphWindow]

example : sampleHypergraphWindow.certificate = 18 := by
  native_decide


structure FiniteHypergraphModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteHypergraphModelsBudgetCertificate.controlled
    (c : FiniteHypergraphModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteHypergraphModelsBudgetCertificate.budgetControlled
    (c : FiniteHypergraphModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteHypergraphModelsBudgetCertificate.Ready
    (c : FiniteHypergraphModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteHypergraphModelsBudgetCertificate.size
    (c : FiniteHypergraphModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteHypergraphModels_budgetCertificate_le_size
    (c : FiniteHypergraphModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteHypergraphModelsBudgetCertificate :
    FiniteHypergraphModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteHypergraphModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHypergraphModelsBudgetCertificate.controlled,
      sampleFiniteHypergraphModelsBudgetCertificate]
  · norm_num [FiniteHypergraphModelsBudgetCertificate.budgetControlled,
      sampleFiniteHypergraphModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteHypergraphModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHypergraphModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteHypergraphModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteHypergraphModelsBudgetCertificate.controlled,
      sampleFiniteHypergraphModelsBudgetCertificate]
  · norm_num [FiniteHypergraphModelsBudgetCertificate.budgetControlled,
      sampleFiniteHypergraphModelsBudgetCertificate]

example :
    sampleFiniteHypergraphModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteHypergraphModelsBudgetCertificate.size := by
  apply finiteHypergraphModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteHypergraphModelsBudgetCertificate.controlled,
      sampleFiniteHypergraphModelsBudgetCertificate]
  · norm_num [FiniteHypergraphModelsBudgetCertificate.budgetControlled,
      sampleFiniteHypergraphModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteHypergraphModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteHypergraphModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteHypergraphModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteHypergraphModels
