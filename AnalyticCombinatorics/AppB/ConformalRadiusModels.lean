import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Conformal-radius bookkeeping models.

The analytic conformal radius is represented by finite inner, outer, and
distortion budgets.
-/

namespace AnalyticCombinatorics.AppB.ConformalRadiusModels

structure ConformalRadiusDatum where
  innerRadius : ℕ
  outerRadius : ℕ
  distortionBudget : ℕ
deriving DecidableEq, Repr

def radiusNested (d : ConformalRadiusDatum) : Prop :=
  d.innerRadius ≤ d.outerRadius

def positiveInnerRadius (d : ConformalRadiusDatum) : Prop :=
  0 < d.innerRadius

def conformalRadiusReady (d : ConformalRadiusDatum) : Prop :=
  positiveInnerRadius d ∧ radiusNested d

def radiusSlack (d : ConformalRadiusDatum) : ℕ :=
  d.outerRadius - d.innerRadius

theorem conformalRadiusReady.nested {d : ConformalRadiusDatum}
    (h : conformalRadiusReady d) :
    positiveInnerRadius d ∧ radiusNested d := by
  refine ⟨h.1, h.2⟩

theorem radiusSlack_add {d : ConformalRadiusDatum}
    (h : radiusNested d) :
    radiusSlack d + d.innerRadius = d.outerRadius := by
  unfold radiusSlack radiusNested at *
  omega

def sampleConformalRadius : ConformalRadiusDatum :=
  { innerRadius := 3, outerRadius := 8, distortionBudget := 2 }

example : conformalRadiusReady sampleConformalRadius := by
  norm_num [conformalRadiusReady, positiveInnerRadius, radiusNested, sampleConformalRadius]

example : radiusSlack sampleConformalRadius = 5 := by
  native_decide

structure ConformalRadiusWindow where
  innerRadius : ℕ
  outerRadius : ℕ
  distortionBudget : ℕ
  imageRadius : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConformalRadiusWindow.radiusReady (w : ConformalRadiusWindow) : Prop :=
  0 < w.innerRadius ∧ w.innerRadius ≤ w.outerRadius

def ConformalRadiusWindow.distortionControlled (w : ConformalRadiusWindow) : Prop :=
  w.imageRadius ≤ w.outerRadius + w.distortionBudget + w.slack

def ConformalRadiusWindow.ready (w : ConformalRadiusWindow) : Prop :=
  w.radiusReady ∧ w.distortionControlled

def ConformalRadiusWindow.certificate (w : ConformalRadiusWindow) : ℕ :=
  w.innerRadius + w.outerRadius + w.distortionBudget + w.imageRadius + w.slack

theorem imageRadius_le_certificate (w : ConformalRadiusWindow) :
    w.imageRadius ≤ w.certificate := by
  unfold ConformalRadiusWindow.certificate
  omega

def sampleConformalRadiusWindow : ConformalRadiusWindow :=
  { innerRadius := 3, outerRadius := 8, distortionBudget := 2, imageRadius := 7, slack := 0 }

example : sampleConformalRadiusWindow.ready := by
  norm_num [sampleConformalRadiusWindow, ConformalRadiusWindow.ready,
    ConformalRadiusWindow.radiusReady, ConformalRadiusWindow.distortionControlled]


structure ConformalRadiusModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ConformalRadiusModelsBudgetCertificate.controlled
    (c : ConformalRadiusModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def ConformalRadiusModelsBudgetCertificate.budgetControlled
    (c : ConformalRadiusModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def ConformalRadiusModelsBudgetCertificate.Ready
    (c : ConformalRadiusModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def ConformalRadiusModelsBudgetCertificate.size
    (c : ConformalRadiusModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem conformalRadiusModels_budgetCertificate_le_size
    (c : ConformalRadiusModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleConformalRadiusModelsBudgetCertificate :
    ConformalRadiusModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleConformalRadiusModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ConformalRadiusModelsBudgetCertificate.controlled,
      sampleConformalRadiusModelsBudgetCertificate]
  · norm_num [ConformalRadiusModelsBudgetCertificate.budgetControlled,
      sampleConformalRadiusModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleConformalRadiusModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleConformalRadiusModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleConformalRadiusModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [ConformalRadiusModelsBudgetCertificate.controlled,
      sampleConformalRadiusModelsBudgetCertificate]
  · norm_num [ConformalRadiusModelsBudgetCertificate.budgetControlled,
      sampleConformalRadiusModelsBudgetCertificate]

example :
    sampleConformalRadiusModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleConformalRadiusModelsBudgetCertificate.size := by
  apply conformalRadiusModels_budgetCertificate_le_size
  constructor
  · norm_num [ConformalRadiusModelsBudgetCertificate.controlled,
      sampleConformalRadiusModelsBudgetCertificate]
  · norm_num [ConformalRadiusModelsBudgetCertificate.budgetControlled,
      sampleConformalRadiusModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List ConformalRadiusModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleConformalRadiusModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleConformalRadiusModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.ConformalRadiusModels
