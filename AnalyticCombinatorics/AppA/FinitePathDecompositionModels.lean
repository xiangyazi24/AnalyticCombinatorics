import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite path decomposition models.

Paths are represented by segment lengths.  The definitions track decomposed
lengths and component counts.
-/

namespace AnalyticCombinatorics.AppA.FinitePathDecompositionModels

def pathLength (segments : List ℕ) : ℕ :=
  segments.sum

def componentCount (segments : List ℕ) : ℕ :=
  segments.length

def refinementBudget (segments : List ℕ) : ℕ :=
  pathLength segments + componentCount segments

def boundedPathLength (segments : List ℕ) (bound : ℕ) : Prop :=
  pathLength segments ≤ bound

theorem pathLength_cons (x : ℕ) (segments : List ℕ) :
    pathLength (x :: segments) = x + pathLength segments := by
  simp [pathLength]

theorem componentCount_cons (x : ℕ) (segments : List ℕ) :
    componentCount (x :: segments) = componentCount segments + 1 := by
  simp [componentCount]

theorem pathLength_le_refinementBudget (segments : List ℕ) :
    pathLength segments ≤ refinementBudget segments := by
  unfold refinementBudget
  omega

def samplePath : List ℕ :=
  [1, 3, 2, 5]

example : pathLength samplePath = 11 := by
  native_decide

example : componentCount samplePath = 4 := by
  native_decide

example : refinementBudget samplePath = 15 := by
  native_decide

structure PathDecompositionWindow where
  components : ℕ
  pathMass : ℕ
  refinementMass : ℕ
  maxSegment : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PathDecompositionWindow.refinementControlled (w : PathDecompositionWindow) : Prop :=
  w.refinementMass ≤ w.pathMass + w.components + w.slack

def PathDecompositionWindow.segmentControlled (w : PathDecompositionWindow) : Prop :=
  w.pathMass ≤ w.components * w.maxSegment + w.slack

def PathDecompositionWindow.ready (w : PathDecompositionWindow) : Prop :=
  w.refinementControlled ∧ w.segmentControlled

def PathDecompositionWindow.certificate (w : PathDecompositionWindow) : ℕ :=
  w.components + w.pathMass + w.refinementMass + w.maxSegment + w.slack

theorem refinementMass_le_certificate (w : PathDecompositionWindow) :
    w.refinementMass ≤ w.certificate := by
  unfold PathDecompositionWindow.certificate
  omega

def samplePathDecompositionWindow : PathDecompositionWindow :=
  { components := 4, pathMass := 11, refinementMass := 15, maxSegment := 5, slack := 0 }

example : samplePathDecompositionWindow.ready := by
  norm_num [samplePathDecompositionWindow, PathDecompositionWindow.ready,
    PathDecompositionWindow.refinementControlled, PathDecompositionWindow.segmentControlled]


structure FinitePathDecompositionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePathDecompositionModelsBudgetCertificate.controlled
    (c : FinitePathDecompositionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePathDecompositionModelsBudgetCertificate.budgetControlled
    (c : FinitePathDecompositionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePathDecompositionModelsBudgetCertificate.Ready
    (c : FinitePathDecompositionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePathDecompositionModelsBudgetCertificate.size
    (c : FinitePathDecompositionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePathDecompositionModels_budgetCertificate_le_size
    (c : FinitePathDecompositionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePathDecompositionModelsBudgetCertificate :
    FinitePathDecompositionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFinitePathDecompositionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.controlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.budgetControlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]

example :
    sampleFinitePathDecompositionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePathDecompositionModelsBudgetCertificate.size := by
  apply finitePathDecompositionModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.controlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.budgetControlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFinitePathDecompositionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.controlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]
  · norm_num [FinitePathDecompositionModelsBudgetCertificate.budgetControlled,
      sampleFinitePathDecompositionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePathDecompositionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePathDecompositionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FinitePathDecompositionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePathDecompositionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePathDecompositionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePathDecompositionModels
