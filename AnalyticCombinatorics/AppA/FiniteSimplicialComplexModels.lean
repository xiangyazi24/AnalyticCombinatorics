import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite simplicial complex models.

The finite schema records vertices, faces, and boundary-incidence
budgets.
-/

namespace AnalyticCombinatorics.AppA.FiniteSimplicialComplexModels

structure SimplicialComplexData where
  vertices : ℕ
  faces : ℕ
  boundaryIncidences : ℕ
deriving DecidableEq, Repr

def simplicialVerticesNonempty (d : SimplicialComplexData) : Prop :=
  0 < d.vertices

def facesControlled (d : SimplicialComplexData) : Prop :=
  d.faces ≤ d.vertices + d.boundaryIncidences

def simplicialComplexReady (d : SimplicialComplexData) : Prop :=
  simplicialVerticesNonempty d ∧ facesControlled d

def simplicialComplexBudget (d : SimplicialComplexData) : ℕ :=
  d.vertices + d.faces + d.boundaryIncidences

theorem simplicialComplexReady.vertices {d : SimplicialComplexData}
    (h : simplicialComplexReady d) :
    simplicialVerticesNonempty d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem faces_le_simplicialBudget (d : SimplicialComplexData) :
    d.faces ≤ simplicialComplexBudget d := by
  unfold simplicialComplexBudget
  omega

def sampleSimplicialComplexData : SimplicialComplexData :=
  { vertices := 7, faces := 10, boundaryIncidences := 4 }

example : simplicialComplexReady sampleSimplicialComplexData := by
  norm_num [simplicialComplexReady, simplicialVerticesNonempty]
  norm_num [facesControlled, sampleSimplicialComplexData]

example : simplicialComplexBudget sampleSimplicialComplexData = 21 := by
  native_decide

structure SimplicialComplexWindow where
  vertices : ℕ
  faces : ℕ
  boundaryIncidences : ℕ
  chainBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def SimplicialComplexWindow.facesControlled (w : SimplicialComplexWindow) : Prop :=
  w.faces ≤ w.vertices + w.boundaryIncidences + w.slack

def SimplicialComplexWindow.chainControlled (w : SimplicialComplexWindow) : Prop :=
  w.chainBudget ≤ w.vertices + w.faces + w.boundaryIncidences + w.slack

def simplicialComplexWindowReady (w : SimplicialComplexWindow) : Prop :=
  0 < w.vertices ∧
    w.facesControlled ∧
    w.chainControlled

def SimplicialComplexWindow.certificate (w : SimplicialComplexWindow) : ℕ :=
  w.vertices + w.faces + w.boundaryIncidences + w.slack

theorem simplicialComplex_chainBudget_le_certificate {w : SimplicialComplexWindow}
    (h : simplicialComplexWindowReady w) :
    w.chainBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hchain⟩
  exact hchain

def sampleSimplicialComplexWindow : SimplicialComplexWindow :=
  { vertices := 7, faces := 10, boundaryIncidences := 4, chainBudget := 20, slack := 0 }

example : simplicialComplexWindowReady sampleSimplicialComplexWindow := by
  norm_num [simplicialComplexWindowReady, SimplicialComplexWindow.facesControlled,
    SimplicialComplexWindow.chainControlled, sampleSimplicialComplexWindow]

example : sampleSimplicialComplexWindow.certificate = 21 := by
  native_decide


structure FiniteSimplicialComplexModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteSimplicialComplexModelsBudgetCertificate.controlled
    (c : FiniteSimplicialComplexModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteSimplicialComplexModelsBudgetCertificate.budgetControlled
    (c : FiniteSimplicialComplexModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteSimplicialComplexModelsBudgetCertificate.Ready
    (c : FiniteSimplicialComplexModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteSimplicialComplexModelsBudgetCertificate.size
    (c : FiniteSimplicialComplexModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteSimplicialComplexModels_budgetCertificate_le_size
    (c : FiniteSimplicialComplexModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteSimplicialComplexModelsBudgetCertificate :
    FiniteSimplicialComplexModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteSimplicialComplexModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.controlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.budgetControlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteSimplicialComplexModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSimplicialComplexModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteSimplicialComplexModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.controlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.budgetControlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]

example :
    sampleFiniteSimplicialComplexModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteSimplicialComplexModelsBudgetCertificate.size := by
  apply finiteSimplicialComplexModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.controlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]
  · norm_num [FiniteSimplicialComplexModelsBudgetCertificate.budgetControlled,
      sampleFiniteSimplicialComplexModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteSimplicialComplexModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteSimplicialComplexModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteSimplicialComplexModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteSimplicialComplexModels
