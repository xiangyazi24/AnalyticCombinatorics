import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite bookkeeping for contour deformation arguments.

The analytic deformation is represented by radius inequalities and an error
budget, keeping the algebraic checks explicit.
-/

namespace AnalyticCombinatorics.AppB.ContourDeformationModels

structure ContourMove where
  oldRadius : ℕ
  newRadius : ℕ
  errorBudget : ℕ
deriving DecidableEq, Repr

def inwardMove (m : ContourMove) : Prop :=
  m.newRadius ≤ m.oldRadius

def deformationControlled (m : ContourMove) : Prop :=
  inwardMove m ∧ m.errorBudget ≤ m.oldRadius

def radiusDrop (m : ContourMove) : ℕ :=
  m.oldRadius - m.newRadius

theorem deformationControlled.inward {m : ContourMove}
    (h : deformationControlled m) :
    inwardMove m ∧ m.errorBudget ≤ m.oldRadius := by
  refine ⟨h.1, h.2⟩

theorem radiusDrop_add_new {m : ContourMove}
    (h : inwardMove m) :
    radiusDrop m + m.newRadius = m.oldRadius := by
  unfold radiusDrop inwardMove at *
  omega

def sampleMove : ContourMove :=
  { oldRadius := 10, newRadius := 7, errorBudget := 3 }

example : deformationControlled sampleMove := by
  norm_num [deformationControlled, inwardMove, sampleMove]

example : radiusDrop sampleMove = 3 := by
  native_decide

structure ContourWindow where
  oldRadius : ℕ
  newRadius : ℕ
  arcCount : ℕ
  deformationError : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContourWindow.inwardReady (w : ContourWindow) : Prop :=
  w.newRadius ≤ w.oldRadius

def ContourWindow.errorControlled (w : ContourWindow) : Prop :=
  w.deformationError ≤ w.oldRadius + w.slack

def ContourWindow.ready (w : ContourWindow) : Prop :=
  w.inwardReady ∧ 0 < w.arcCount ∧ w.errorControlled

def ContourWindow.certificate (w : ContourWindow) : ℕ :=
  w.oldRadius + w.newRadius + w.arcCount + w.deformationError + w.slack

theorem deformationError_le_certificate (w : ContourWindow) :
    w.deformationError ≤ w.certificate := by
  unfold ContourWindow.certificate
  omega

def sampleContourWindow : ContourWindow :=
  { oldRadius := 10, newRadius := 7, arcCount := 3, deformationError := 3, slack := 0 }

example : sampleContourWindow.ready := by
  norm_num [sampleContourWindow, ContourWindow.ready, ContourWindow.inwardReady,
    ContourWindow.errorControlled]


structure ContourDeformationModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ContourDeformationModelsBudgetCertificate.controlled
    (c : ContourDeformationModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ContourDeformationModelsBudgetCertificate.budgetControlled
    (c : ContourDeformationModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ContourDeformationModelsBudgetCertificate.Ready
    (c : ContourDeformationModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ContourDeformationModelsBudgetCertificate.size
    (c : ContourDeformationModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem contourDeformationModels_budgetCertificate_le_size
    (c : ContourDeformationModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleContourDeformationModelsBudgetCertificate :
    ContourDeformationModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleContourDeformationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContourDeformationModelsBudgetCertificate.controlled,
      sampleContourDeformationModelsBudgetCertificate]
  · norm_num [ContourDeformationModelsBudgetCertificate.budgetControlled,
      sampleContourDeformationModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleContourDeformationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleContourDeformationModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleContourDeformationModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ContourDeformationModelsBudgetCertificate.controlled,
      sampleContourDeformationModelsBudgetCertificate]
  · norm_num [ContourDeformationModelsBudgetCertificate.budgetControlled,
      sampleContourDeformationModelsBudgetCertificate]

example :
    sampleContourDeformationModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleContourDeformationModelsBudgetCertificate.size := by
  apply contourDeformationModels_budgetCertificate_le_size
  constructor
  · norm_num [ContourDeformationModelsBudgetCertificate.controlled,
      sampleContourDeformationModelsBudgetCertificate]
  · norm_num [ContourDeformationModelsBudgetCertificate.budgetControlled,
      sampleContourDeformationModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ContourDeformationModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleContourDeformationModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleContourDeformationModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ContourDeformationModels
