import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite Cartesian power models.

The finite schema records base size, power depth, and product slack for
Cartesian power constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteCartesianPowerModels

structure CartesianPowerData where
  baseSize : ℕ
  powerDepth : ℕ
  productSlack : ℕ
deriving DecidableEq, Repr

def baseSizePositive (d : CartesianPowerData) : Prop :=
  0 < d.baseSize

def powerDepthControlled (d : CartesianPowerData) : Prop :=
  d.powerDepth ≤ d.baseSize + d.productSlack

def cartesianPowerReady (d : CartesianPowerData) : Prop :=
  baseSizePositive d ∧ powerDepthControlled d

def cartesianPowerBudget (d : CartesianPowerData) : ℕ :=
  d.baseSize + d.powerDepth + d.productSlack

theorem cartesianPowerReady.base {d : CartesianPowerData}
    (h : cartesianPowerReady d) :
    baseSizePositive d ∧ powerDepthControlled d ∧ d.powerDepth ≤ cartesianPowerBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold cartesianPowerBudget
  omega

theorem powerDepth_le_cartesianPowerBudget (d : CartesianPowerData) :
    d.powerDepth ≤ cartesianPowerBudget d := by
  unfold cartesianPowerBudget
  omega

def sampleCartesianPowerData : CartesianPowerData :=
  { baseSize := 6, powerDepth := 8, productSlack := 3 }

example : cartesianPowerReady sampleCartesianPowerData := by
  norm_num [cartesianPowerReady, baseSizePositive]
  norm_num [powerDepthControlled, sampleCartesianPowerData]

example : cartesianPowerBudget sampleCartesianPowerData = 17 := by
  native_decide

structure CartesianPowerWindow where
  baseSize : ℕ
  powerDepth : ℕ
  productSlack : ℕ
  expansionBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def CartesianPowerWindow.depthControlled (w : CartesianPowerWindow) : Prop :=
  w.powerDepth ≤ w.baseSize + w.productSlack + w.slack

def CartesianPowerWindow.expansionControlled (w : CartesianPowerWindow) : Prop :=
  w.expansionBudget ≤ w.baseSize + w.powerDepth + w.productSlack + w.slack

def cartesianPowerWindowReady (w : CartesianPowerWindow) : Prop :=
  0 < w.baseSize ∧
    w.depthControlled ∧
    w.expansionControlled

def CartesianPowerWindow.certificate (w : CartesianPowerWindow) : ℕ :=
  w.baseSize + w.powerDepth + w.productSlack + w.slack

theorem cartesianPower_expansionBudget_le_certificate {w : CartesianPowerWindow}
    (h : cartesianPowerWindowReady w) :
    w.expansionBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hexpansion⟩
  exact hexpansion

def sampleCartesianPowerWindow : CartesianPowerWindow :=
  { baseSize := 6, powerDepth := 8, productSlack := 3, expansionBudget := 16, slack := 0 }

example : cartesianPowerWindowReady sampleCartesianPowerWindow := by
  norm_num [cartesianPowerWindowReady, CartesianPowerWindow.depthControlled,
    CartesianPowerWindow.expansionControlled, sampleCartesianPowerWindow]

example : sampleCartesianPowerWindow.certificate = 17 := by
  native_decide


structure FiniteCartesianPowerModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteCartesianPowerModelsBudgetCertificate.controlled
    (c : FiniteCartesianPowerModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteCartesianPowerModelsBudgetCertificate.budgetControlled
    (c : FiniteCartesianPowerModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteCartesianPowerModelsBudgetCertificate.Ready
    (c : FiniteCartesianPowerModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteCartesianPowerModelsBudgetCertificate.size
    (c : FiniteCartesianPowerModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCartesianPowerModels_budgetCertificate_le_size
    (c : FiniteCartesianPowerModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteCartesianPowerModelsBudgetCertificate :
    FiniteCartesianPowerModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

example : sampleFiniteCartesianPowerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.controlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.budgetControlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]

example :
    sampleFiniteCartesianPowerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCartesianPowerModelsBudgetCertificate.size := by
  apply finiteCartesianPowerModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.controlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.budgetControlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]

/-- Finite executable readiness audit for Cartesian-power certificates. -/
def finiteCartesianPowerModelsBudgetCertificateListReady
    (data : List FiniteCartesianPowerModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteCartesianPowerModelsBudgetCertificateList_readyWindow :
    finiteCartesianPowerModelsBudgetCertificateListReady
      [sampleFiniteCartesianPowerModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold finiteCartesianPowerModelsBudgetCertificateListReady
    sampleFiniteCartesianPowerModelsBudgetCertificate
  native_decide

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleFiniteCartesianPowerModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.controlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]
  · norm_num [FiniteCartesianPowerModelsBudgetCertificate.budgetControlled,
      sampleFiniteCartesianPowerModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteCartesianPowerModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteCartesianPowerModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List FiniteCartesianPowerModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteCartesianPowerModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFiniteCartesianPowerModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FiniteCartesianPowerModels
