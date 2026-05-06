import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite bipartite graph models.

The definitions track left/right part sizes and edge budgets for bipartite
combinatorial specifications.
-/

namespace AnalyticCombinatorics.AppA.FiniteBipartiteModels

structure BipartiteProfile where
  leftSize : ℕ
  rightSize : ℕ
  edgeCount : ℕ
deriving DecidableEq, Repr

def nonemptySides (p : BipartiteProfile) : Prop :=
  0 < p.leftSize ∧ 0 < p.rightSize

def edgeBounded (p : BipartiteProfile) : Prop :=
  p.edgeCount ≤ p.leftSize * p.rightSize

def bipartiteReady (p : BipartiteProfile) : Prop :=
  nonemptySides p ∧ edgeBounded p

def maximumEdges (p : BipartiteProfile) : ℕ :=
  p.leftSize * p.rightSize

theorem bipartiteReady.bound {p : BipartiteProfile}
    (h : bipartiteReady p) :
    edgeBounded p := by
  rcases h with ⟨hleft, hright⟩
  exact hright

theorem edgeCount_le_maximum {p : BipartiteProfile}
    (h : edgeBounded p) :
    edgeBounded p ∧ p.edgeCount ≤ maximumEdges p := by
  exact ⟨h, h⟩

def sampleBipartite : BipartiteProfile :=
  { leftSize := 3, rightSize := 4, edgeCount := 7 }

example : bipartiteReady sampleBipartite := by
  norm_num [bipartiteReady, nonemptySides, edgeBounded, sampleBipartite]

example : maximumEdges sampleBipartite = 12 := by
  native_decide

structure BipartiteWindow where
  leftSize : ℕ
  rightSize : ℕ
  edgeCount : ℕ
  matchingSize : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BipartiteWindow.sidesReady (w : BipartiteWindow) : Prop :=
  0 < w.leftSize ∧ 0 < w.rightSize

def BipartiteWindow.edgeControlled (w : BipartiteWindow) : Prop :=
  w.edgeCount ≤ w.leftSize * w.rightSize + w.slack

def BipartiteWindow.matchingControlled (w : BipartiteWindow) : Prop :=
  w.matchingSize ≤ w.leftSize ∧ w.matchingSize ≤ w.rightSize

def BipartiteWindow.ready (w : BipartiteWindow) : Prop :=
  w.sidesReady ∧ w.edgeControlled ∧ w.matchingControlled

def BipartiteWindow.certificate (w : BipartiteWindow) : ℕ :=
  w.leftSize + w.rightSize + w.edgeCount + w.matchingSize + w.slack

theorem matchingSize_le_certificate (w : BipartiteWindow) :
    w.matchingSize ≤ w.certificate := by
  unfold BipartiteWindow.certificate
  omega

def sampleBipartiteWindow : BipartiteWindow :=
  { leftSize := 3, rightSize := 4, edgeCount := 7, matchingSize := 3, slack := 0 }

example : sampleBipartiteWindow.ready := by
  norm_num [sampleBipartiteWindow, BipartiteWindow.ready, BipartiteWindow.sidesReady,
    BipartiteWindow.edgeControlled, BipartiteWindow.matchingControlled]


structure FiniteBipartiteModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteBipartiteModelsBudgetCertificate.controlled
    (c : FiniteBipartiteModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteBipartiteModelsBudgetCertificate.budgetControlled
    (c : FiniteBipartiteModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteBipartiteModelsBudgetCertificate.Ready
    (c : FiniteBipartiteModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteBipartiteModelsBudgetCertificate.size
    (c : FiniteBipartiteModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBipartiteModels_budgetCertificate_le_size
    (c : FiniteBipartiteModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteBipartiteModelsBudgetCertificate :
    FiniteBipartiteModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteBipartiteModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBipartiteModelsBudgetCertificate.controlled,
      sampleFiniteBipartiteModelsBudgetCertificate]
  · norm_num [FiniteBipartiteModelsBudgetCertificate.budgetControlled,
      sampleFiniteBipartiteModelsBudgetCertificate]

example :
    sampleFiniteBipartiteModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBipartiteModelsBudgetCertificate.size := by
  apply finiteBipartiteModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteBipartiteModelsBudgetCertificate.controlled,
      sampleFiniteBipartiteModelsBudgetCertificate]
  · norm_num [FiniteBipartiteModelsBudgetCertificate.budgetControlled,
      sampleFiniteBipartiteModelsBudgetCertificate]

/-- Finite executable readiness audit for finite-bipartite certificates. -/
def finiteBipartiteModelsBudgetCertificateListReady
    (data : List FiniteBipartiteModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteBipartiteModelsBudgetCertificateList_readyWindow :
    finiteBipartiteModelsBudgetCertificateListReady
      [sampleFiniteBipartiteModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteBipartiteModelsBudgetCertificateListReady
    sampleFiniteBipartiteModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteBipartiteModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteBipartiteModelsBudgetCertificate.controlled,
      sampleFiniteBipartiteModelsBudgetCertificate]
  · norm_num [FiniteBipartiteModelsBudgetCertificate.budgetControlled,
      sampleFiniteBipartiteModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteBipartiteModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteBipartiteModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteBipartiteModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteBipartiteModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteBipartiteModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteBipartiteModels
