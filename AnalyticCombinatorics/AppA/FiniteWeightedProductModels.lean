import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite weighted product models.

This module records finite bookkeeping for weighted product constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteWeightedProductModels

structure WeightedProductData where
  productFactors : ℕ
  weightWindow : ℕ
  productSlack : ℕ
deriving DecidableEq, Repr

def hasProductFactors (d : WeightedProductData) : Prop :=
  0 < d.productFactors

def weightWindowControlled (d : WeightedProductData) : Prop :=
  d.weightWindow ≤ d.productFactors + d.productSlack

def weightedProductReady (d : WeightedProductData) : Prop :=
  hasProductFactors d ∧ weightWindowControlled d

def weightedProductBudget (d : WeightedProductData) : ℕ :=
  d.productFactors + d.weightWindow + d.productSlack

theorem weightedProductReady.hasProductFactors {d : WeightedProductData}
    (h : weightedProductReady d) :
    hasProductFactors d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem weightWindow_le_budget (d : WeightedProductData) :
    d.weightWindow ≤ weightedProductBudget d := by
  unfold weightedProductBudget
  omega

def sampleWeightedProductData : WeightedProductData :=
  { productFactors := 7, weightWindow := 9, productSlack := 3 }

example : weightedProductReady sampleWeightedProductData := by
  norm_num [weightedProductReady, hasProductFactors]
  norm_num [weightWindowControlled, sampleWeightedProductData]

example : weightedProductBudget sampleWeightedProductData = 19 := by
  native_decide

structure WeightedProductWindow where
  productFactors : ℕ
  weightWindow : ℕ
  productSlack : ℕ
  factorWeightBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def WeightedProductWindow.weightControlled (w : WeightedProductWindow) : Prop :=
  w.weightWindow ≤ w.productFactors + w.productSlack + w.slack

def WeightedProductWindow.factorWeightControlled (w : WeightedProductWindow) : Prop :=
  w.factorWeightBudget ≤ w.productFactors + w.weightWindow + w.productSlack + w.slack

def weightedProductWindowReady (w : WeightedProductWindow) : Prop :=
  0 < w.productFactors ∧
    w.weightControlled ∧
    w.factorWeightControlled

def WeightedProductWindow.certificate (w : WeightedProductWindow) : ℕ :=
  w.productFactors + w.weightWindow + w.productSlack + w.slack

theorem weightedProduct_factorWeightBudget_le_certificate {w : WeightedProductWindow}
    (h : weightedProductWindowReady w) :
    w.factorWeightBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hfactor⟩
  exact hfactor

def sampleWeightedProductWindow : WeightedProductWindow :=
  { productFactors := 7, weightWindow := 9, productSlack := 3, factorWeightBudget := 18,
    slack := 0 }

example : weightedProductWindowReady sampleWeightedProductWindow := by
  norm_num [weightedProductWindowReady, WeightedProductWindow.weightControlled,
    WeightedProductWindow.factorWeightControlled, sampleWeightedProductWindow]

example : sampleWeightedProductWindow.certificate = 19 := by
  native_decide


structure FiniteWeightedProductModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteWeightedProductModelsBudgetCertificate.controlled
    (c : FiniteWeightedProductModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteWeightedProductModelsBudgetCertificate.budgetControlled
    (c : FiniteWeightedProductModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteWeightedProductModelsBudgetCertificate.Ready
    (c : FiniteWeightedProductModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteWeightedProductModelsBudgetCertificate.size
    (c : FiniteWeightedProductModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteWeightedProductModels_budgetCertificate_le_size
    (c : FiniteWeightedProductModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteWeightedProductModelsBudgetCertificate :
    FiniteWeightedProductModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteWeightedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.controlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteWeightedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedProductModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteWeightedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.controlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]

example :
    sampleFiniteWeightedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteWeightedProductModelsBudgetCertificate.size := by
  apply finiteWeightedProductModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.controlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]
  · norm_num [FiniteWeightedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteWeightedProductModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteWeightedProductModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteWeightedProductModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteWeightedProductModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteWeightedProductModels
