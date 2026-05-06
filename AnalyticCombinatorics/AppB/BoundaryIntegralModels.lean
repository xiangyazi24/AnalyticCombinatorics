import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Boundary integral models.

The finite schema tracks contour pieces, a boundary radius, and an error
budget for elementary boundary integral estimates.
-/

namespace AnalyticCombinatorics.AppB.BoundaryIntegralModels

structure BoundaryIntegralData where
  contourPieces : ℕ
  boundaryRadius : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def positiveBoundaryRadius (d : BoundaryIntegralData) : Prop :=
  0 < d.boundaryRadius

def contourPiecesControlled (d : BoundaryIntegralData) : Prop :=
  d.contourPieces ≤ d.boundaryRadius + d.errorBudget

def boundaryIntegralReady (d : BoundaryIntegralData) : Prop :=
  positiveBoundaryRadius d ∧ contourPiecesControlled d

def boundaryIntegralBudget (d : BoundaryIntegralData) : ℕ :=
  d.contourPieces + d.boundaryRadius + d.errorBudget

theorem boundaryIntegralReady.radius {d : BoundaryIntegralData}
    (h : boundaryIntegralReady d) :
    positiveBoundaryRadius d ∧ contourPiecesControlled d ∧
      d.contourPieces ≤ boundaryIntegralBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold boundaryIntegralBudget
  omega

theorem contourPieces_le_boundaryBudget (d : BoundaryIntegralData) :
    d.contourPieces ≤ boundaryIntegralBudget d := by
  unfold boundaryIntegralBudget
  omega

def sampleBoundaryIntegralData : BoundaryIntegralData :=
  { contourPieces := 8, boundaryRadius := 5, errorBudget := 4 }

example : boundaryIntegralReady sampleBoundaryIntegralData := by
  norm_num [boundaryIntegralReady, positiveBoundaryRadius]
  norm_num [contourPiecesControlled, sampleBoundaryIntegralData]

example : boundaryIntegralBudget sampleBoundaryIntegralData = 17 := by
  native_decide

/-- Finite executable readiness audit for boundary-integral data. -/
def boundaryIntegralListReady (windows : List BoundaryIntegralData) : Bool :=
  windows.all fun d =>
    0 < d.boundaryRadius && d.contourPieces ≤ d.boundaryRadius + d.errorBudget

theorem boundaryIntegralList_readyWindow :
    boundaryIntegralListReady
      [{ contourPieces := 4, boundaryRadius := 3, errorBudget := 1 },
       { contourPieces := 8, boundaryRadius := 5, errorBudget := 4 }] = true := by
  unfold boundaryIntegralListReady
  native_decide


structure BoundaryIntegralModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BoundaryIntegralModelsBudgetCertificate.controlled
    (c : BoundaryIntegralModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def BoundaryIntegralModelsBudgetCertificate.budgetControlled
    (c : BoundaryIntegralModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def BoundaryIntegralModelsBudgetCertificate.Ready
    (c : BoundaryIntegralModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BoundaryIntegralModelsBudgetCertificate.size
    (c : BoundaryIntegralModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem boundaryIntegralModels_budgetCertificate_le_size
    (c : BoundaryIntegralModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBoundaryIntegralModelsBudgetCertificate :
    BoundaryIntegralModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBoundaryIntegralModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryIntegralModelsBudgetCertificate.controlled,
      sampleBoundaryIntegralModelsBudgetCertificate]
  · norm_num [BoundaryIntegralModelsBudgetCertificate.budgetControlled,
      sampleBoundaryIntegralModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBoundaryIntegralModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryIntegralModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBoundaryIntegralModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [BoundaryIntegralModelsBudgetCertificate.controlled,
      sampleBoundaryIntegralModelsBudgetCertificate]
  · norm_num [BoundaryIntegralModelsBudgetCertificate.budgetControlled,
      sampleBoundaryIntegralModelsBudgetCertificate]

example :
    sampleBoundaryIntegralModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleBoundaryIntegralModelsBudgetCertificate.size := by
  apply boundaryIntegralModels_budgetCertificate_le_size
  constructor
  · norm_num [BoundaryIntegralModelsBudgetCertificate.controlled,
      sampleBoundaryIntegralModelsBudgetCertificate]
  · norm_num [BoundaryIntegralModelsBudgetCertificate.budgetControlled,
      sampleBoundaryIntegralModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BoundaryIntegralModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBoundaryIntegralModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBoundaryIntegralModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.BoundaryIntegralModels
