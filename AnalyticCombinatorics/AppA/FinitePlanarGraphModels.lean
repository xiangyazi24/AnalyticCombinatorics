import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite planar graph models.

This schema records vertices, faces, and an edge budget for finite planar
graph estimates.
-/

namespace AnalyticCombinatorics.AppA.FinitePlanarGraphModels

structure PlanarGraphData where
  vertices : ℕ
  faces : ℕ
  edges : ℕ
deriving DecidableEq, Repr

def vertexNonempty (d : PlanarGraphData) : Prop :=
  0 < d.vertices

def edgesControlledByEulerBudget (d : PlanarGraphData) : Prop :=
  d.edges ≤ d.vertices + d.faces

def planarGraphReady (d : PlanarGraphData) : Prop :=
  vertexNonempty d ∧ edgesControlledByEulerBudget d

def planarGraphBudget (d : PlanarGraphData) : ℕ :=
  d.vertices + d.faces + d.edges

theorem planarGraphReady.vertices {d : PlanarGraphData}
    (h : planarGraphReady d) :
    vertexNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem faces_le_planarGraphBudget (d : PlanarGraphData) :
    d.faces ≤ planarGraphBudget d := by
  unfold planarGraphBudget
  omega

def samplePlanarGraphData : PlanarGraphData :=
  { vertices := 6, faces := 5, edges := 10 }

example : planarGraphReady samplePlanarGraphData := by
  norm_num [planarGraphReady, vertexNonempty]
  norm_num [edgesControlledByEulerBudget, samplePlanarGraphData]

example : planarGraphBudget samplePlanarGraphData = 21 := by
  native_decide

structure PlanarGraphWindow where
  vertices : ℕ
  faces : ℕ
  edges : ℕ
  embeddingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def PlanarGraphWindow.edgesControlled (w : PlanarGraphWindow) : Prop :=
  w.edges ≤ w.vertices + w.faces + w.slack

def PlanarGraphWindow.embeddingControlled (w : PlanarGraphWindow) : Prop :=
  w.embeddingBudget ≤ w.vertices + w.faces + w.edges + w.slack

def planarGraphWindowReady (w : PlanarGraphWindow) : Prop :=
  0 < w.vertices ∧
    w.edgesControlled ∧
    w.embeddingControlled

def PlanarGraphWindow.certificate (w : PlanarGraphWindow) : ℕ :=
  w.vertices + w.faces + w.edges + w.slack

theorem planarGraph_embeddingBudget_le_certificate {w : PlanarGraphWindow}
    (h : planarGraphWindowReady w) :
    w.embeddingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hembedding⟩
  exact hembedding

def samplePlanarGraphWindow : PlanarGraphWindow :=
  { vertices := 6, faces := 5, edges := 10, embeddingBudget := 19, slack := 0 }

example : planarGraphWindowReady samplePlanarGraphWindow := by
  norm_num [planarGraphWindowReady, PlanarGraphWindow.edgesControlled,
    PlanarGraphWindow.embeddingControlled, samplePlanarGraphWindow]

example : samplePlanarGraphWindow.certificate = 21 := by
  native_decide


structure FinitePlanarGraphModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePlanarGraphModelsBudgetCertificate.controlled
    (c : FinitePlanarGraphModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePlanarGraphModelsBudgetCertificate.budgetControlled
    (c : FinitePlanarGraphModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePlanarGraphModelsBudgetCertificate.Ready
    (c : FinitePlanarGraphModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePlanarGraphModelsBudgetCertificate.size
    (c : FinitePlanarGraphModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePlanarGraphModels_budgetCertificate_le_size
    (c : FinitePlanarGraphModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePlanarGraphModelsBudgetCertificate :
    FinitePlanarGraphModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePlanarGraphModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.controlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.budgetControlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePlanarGraphModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePlanarGraphModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePlanarGraphModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.controlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.budgetControlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]

example :
    sampleFinitePlanarGraphModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePlanarGraphModelsBudgetCertificate.size := by
  apply finitePlanarGraphModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.controlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]
  · norm_num [FinitePlanarGraphModelsBudgetCertificate.budgetControlled,
      sampleFinitePlanarGraphModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FinitePlanarGraphModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePlanarGraphModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFinitePlanarGraphModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FinitePlanarGraphModels
