import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite product construction models.

The finite schema records left factors, right factors, and product slack
for symbolic product constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteProductConstructionModels

structure ProductConstructionData where
  leftFactors : ℕ
  rightFactors : ℕ
  productSlack : ℕ
deriving DecidableEq, Repr

def leftFactorsPositive (d : ProductConstructionData) : Prop :=
  0 < d.leftFactors

def rightFactorsControlled (d : ProductConstructionData) : Prop :=
  d.rightFactors ≤ d.leftFactors + d.productSlack

def productConstructionReady (d : ProductConstructionData) : Prop :=
  leftFactorsPositive d ∧ rightFactorsControlled d

def productConstructionBudget (d : ProductConstructionData) : ℕ :=
  d.leftFactors + d.rightFactors + d.productSlack

theorem productConstructionReady.left {d : ProductConstructionData}
    (h : productConstructionReady d) :
    leftFactorsPositive d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem rightFactors_le_productConstructionBudget
    (d : ProductConstructionData) :
    d.rightFactors ≤ productConstructionBudget d := by
  unfold productConstructionBudget
  omega

def sampleProductConstructionData : ProductConstructionData :=
  { leftFactors := 6, rightFactors := 8, productSlack := 3 }

example : productConstructionReady sampleProductConstructionData := by
  norm_num [productConstructionReady, leftFactorsPositive]
  norm_num [rightFactorsControlled, sampleProductConstructionData]

example : productConstructionBudget sampleProductConstructionData = 17 := by
  native_decide

structure ProductConstructionWindow where
  leftFactors : ℕ
  rightFactors : ℕ
  productSlack : ℕ
  productBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def ProductConstructionWindow.rightControlled (w : ProductConstructionWindow) : Prop :=
  w.rightFactors ≤ w.leftFactors + w.productSlack + w.slack

def ProductConstructionWindow.productControlled (w : ProductConstructionWindow) : Prop :=
  w.productBudget ≤ w.leftFactors + w.rightFactors + w.productSlack + w.slack

def productConstructionWindowReady (w : ProductConstructionWindow) : Prop :=
  0 < w.leftFactors ∧
    w.rightControlled ∧
    w.productControlled

def ProductConstructionWindow.certificate (w : ProductConstructionWindow) : ℕ :=
  w.leftFactors + w.rightFactors + w.productSlack + w.slack

theorem productConstruction_productBudget_le_certificate {w : ProductConstructionWindow}
    (h : productConstructionWindowReady w) :
    w.productBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hproduct⟩
  exact hproduct

def sampleProductConstructionWindow : ProductConstructionWindow :=
  { leftFactors := 6, rightFactors := 8, productSlack := 3, productBudget := 16, slack := 0 }

example : productConstructionWindowReady sampleProductConstructionWindow := by
  norm_num [productConstructionWindowReady, ProductConstructionWindow.rightControlled,
    ProductConstructionWindow.productControlled, sampleProductConstructionWindow]

example : sampleProductConstructionWindow.certificate = 17 := by
  native_decide


structure FiniteProductConstructionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteProductConstructionModelsBudgetCertificate.controlled
    (c : FiniteProductConstructionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteProductConstructionModelsBudgetCertificate.budgetControlled
    (c : FiniteProductConstructionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteProductConstructionModelsBudgetCertificate.Ready
    (c : FiniteProductConstructionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteProductConstructionModelsBudgetCertificate.size
    (c : FiniteProductConstructionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteProductConstructionModels_budgetCertificate_le_size
    (c : FiniteProductConstructionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteProductConstructionModelsBudgetCertificate :
    FiniteProductConstructionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteProductConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.controlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteProductConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProductConstructionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteProductConstructionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.controlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]

example :
    sampleFiniteProductConstructionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteProductConstructionModelsBudgetCertificate.size := by
  apply finiteProductConstructionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.controlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]
  · norm_num [FiniteProductConstructionModelsBudgetCertificate.budgetControlled,
      sampleFiniteProductConstructionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteProductConstructionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteProductConstructionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteProductConstructionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteProductConstructionModels
