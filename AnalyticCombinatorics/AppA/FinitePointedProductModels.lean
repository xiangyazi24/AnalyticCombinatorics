import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite pointed product models.

This module records a small arithmetic schema for finite pointed products:
the product side is nonempty and the number of point choices is controlled
by a slack budget.
-/

namespace AnalyticCombinatorics.AppA.FinitePointedProductModels

structure PointedProductData where
  productFactors : ℕ
  pointChoices : ℕ
  pointSlack : ℕ
deriving DecidableEq, Repr

def hasProductFactor (d : PointedProductData) : Prop :=
  0 < d.productFactors

def choicesControlled (d : PointedProductData) : Prop :=
  d.pointChoices ≤ d.productFactors + d.pointSlack

def pointedProductReady (d : PointedProductData) : Prop :=
  hasProductFactor d ∧ choicesControlled d

def pointedProductBudget (d : PointedProductData) : ℕ :=
  d.productFactors + d.pointChoices + d.pointSlack

theorem pointedProductReady.hasProductFactor {d : PointedProductData}
    (h : pointedProductReady d) :
    hasProductFactor d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem pointChoices_le_budget (d : PointedProductData) :
    d.pointChoices ≤ pointedProductBudget d := by
  unfold pointedProductBudget
  omega

def samplePointedProductData : PointedProductData :=
  { productFactors := 6, pointChoices := 8, pointSlack := 3 }

example : pointedProductReady samplePointedProductData := by
  norm_num [pointedProductReady, hasProductFactor]
  norm_num [choicesControlled, samplePointedProductData]

example : pointedProductBudget samplePointedProductData = 17 := by
  native_decide

/-- Finite executable readiness audit for pointed-product data. -/
def pointedProductListReady (windows : List PointedProductData) : Bool :=
  windows.all fun d =>
    0 < d.productFactors && d.pointChoices ≤ d.productFactors + d.pointSlack

theorem pointedProductList_readyWindow :
    pointedProductListReady
      [{ productFactors := 3, pointChoices := 4, pointSlack := 1 },
       { productFactors := 6, pointChoices := 8, pointSlack := 3 }] = true := by
  unfold pointedProductListReady
  native_decide


structure FinitePointedProductModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FinitePointedProductModelsBudgetCertificate.controlled
    (c : FinitePointedProductModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FinitePointedProductModelsBudgetCertificate.budgetControlled
    (c : FinitePointedProductModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FinitePointedProductModelsBudgetCertificate.Ready
    (c : FinitePointedProductModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FinitePointedProductModelsBudgetCertificate.size
    (c : FinitePointedProductModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finitePointedProductModels_budgetCertificate_le_size
    (c : FinitePointedProductModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFinitePointedProductModelsBudgetCertificate :
    FinitePointedProductModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFinitePointedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedProductModelsBudgetCertificate.controlled,
      sampleFinitePointedProductModelsBudgetCertificate]
  · norm_num [FinitePointedProductModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedProductModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFinitePointedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedProductModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFinitePointedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FinitePointedProductModelsBudgetCertificate.controlled,
      sampleFinitePointedProductModelsBudgetCertificate]
  · norm_num [FinitePointedProductModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedProductModelsBudgetCertificate]

example :
    sampleFinitePointedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFinitePointedProductModelsBudgetCertificate.size := by
  apply finitePointedProductModels_budgetCertificate_le_size
  constructor
  · norm_num [FinitePointedProductModelsBudgetCertificate.controlled,
      sampleFinitePointedProductModelsBudgetCertificate]
  · norm_num [FinitePointedProductModelsBudgetCertificate.budgetControlled,
      sampleFinitePointedProductModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FinitePointedProductModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFinitePointedProductModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleFinitePointedProductModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppA.FinitePointedProductModels
