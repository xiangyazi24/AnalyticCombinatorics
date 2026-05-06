import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Analytic-capacity bookkeeping models.

The finite schema records cover size, radius budget, and residual capacity.
-/

namespace AnalyticCombinatorics.AppB.AnalyticCapacityModels

structure CapacityDatum where
  coverCount : ℕ
  radiusBudget : ℕ
  capacityBudget : ℕ
deriving DecidableEq, Repr

def nonemptyCover (d : CapacityDatum) : Prop :=
  0 < d.coverCount

def capacityControlled (d : CapacityDatum) : Prop :=
  d.capacityBudget ≤ d.coverCount * d.radiusBudget

def capacityReady (d : CapacityDatum) : Prop :=
  nonemptyCover d ∧ capacityControlled d

def capacitySlack (d : CapacityDatum) : ℕ :=
  d.coverCount * d.radiusBudget - d.capacityBudget

theorem capacityReady.controlled {d : CapacityDatum}
    (h : capacityReady d) :
    nonemptyCover d ∧ capacityControlled d := by
  refine ⟨h.1, h.2⟩

theorem capacitySlack_add {d : CapacityDatum}
    (h : capacityControlled d) :
    capacitySlack d + d.capacityBudget = d.coverCount * d.radiusBudget := by
  unfold capacitySlack capacityControlled at *
  omega

def sampleCapacity : CapacityDatum :=
  { coverCount := 3, radiusBudget := 5, capacityBudget := 8 }

example : capacityReady sampleCapacity := by
  norm_num [capacityReady, nonemptyCover, capacityControlled, sampleCapacity]

example : capacitySlack sampleCapacity = 7 := by
  native_decide

structure AnalyticCapacityWindow where
  coverCount : ℕ
  radiusBudget : ℕ
  capacityBudget : ℕ
  residualCapacity : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCapacityWindow.coverReady (w : AnalyticCapacityWindow) : Prop :=
  0 < w.coverCount

def AnalyticCapacityWindow.capacityControlled (w : AnalyticCapacityWindow) : Prop :=
  w.capacityBudget + w.residualCapacity ≤ w.coverCount * w.radiusBudget + w.slack

def AnalyticCapacityWindow.ready (w : AnalyticCapacityWindow) : Prop :=
  w.coverReady ∧ w.capacityControlled

def AnalyticCapacityWindow.certificate (w : AnalyticCapacityWindow) : ℕ :=
  w.coverCount + w.radiusBudget + w.capacityBudget + w.residualCapacity + w.slack

theorem residualCapacity_le_certificate (w : AnalyticCapacityWindow) :
    w.residualCapacity ≤ w.certificate := by
  unfold AnalyticCapacityWindow.certificate
  omega

def sampleAnalyticCapacityWindow : AnalyticCapacityWindow :=
  { coverCount := 3, radiusBudget := 5, capacityBudget := 8,
    residualCapacity := 7, slack := 0 }

example : sampleAnalyticCapacityWindow.ready := by
  norm_num [sampleAnalyticCapacityWindow, AnalyticCapacityWindow.ready,
    AnalyticCapacityWindow.coverReady, AnalyticCapacityWindow.capacityControlled]


structure AnalyticCapacityModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def AnalyticCapacityModelsBudgetCertificate.controlled
    (c : AnalyticCapacityModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def AnalyticCapacityModelsBudgetCertificate.budgetControlled
    (c : AnalyticCapacityModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def AnalyticCapacityModelsBudgetCertificate.Ready
    (c : AnalyticCapacityModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def AnalyticCapacityModelsBudgetCertificate.size
    (c : AnalyticCapacityModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem analyticCapacityModels_budgetCertificate_le_size
    (c : AnalyticCapacityModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleAnalyticCapacityModelsBudgetCertificate :
    AnalyticCapacityModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleAnalyticCapacityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCapacityModelsBudgetCertificate.controlled,
      sampleAnalyticCapacityModelsBudgetCertificate]
  · norm_num [AnalyticCapacityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCapacityModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleAnalyticCapacityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCapacityModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleAnalyticCapacityModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [AnalyticCapacityModelsBudgetCertificate.controlled,
      sampleAnalyticCapacityModelsBudgetCertificate]
  · norm_num [AnalyticCapacityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCapacityModelsBudgetCertificate]

example :
    sampleAnalyticCapacityModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleAnalyticCapacityModelsBudgetCertificate.size := by
  apply analyticCapacityModels_budgetCertificate_le_size
  constructor
  · norm_num [AnalyticCapacityModelsBudgetCertificate.controlled,
      sampleAnalyticCapacityModelsBudgetCertificate]
  · norm_num [AnalyticCapacityModelsBudgetCertificate.budgetControlled,
      sampleAnalyticCapacityModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List AnalyticCapacityModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleAnalyticCapacityModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleAnalyticCapacityModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.AnalyticCapacityModels
