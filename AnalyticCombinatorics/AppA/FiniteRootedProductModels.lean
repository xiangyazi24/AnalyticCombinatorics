import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite rooted product models.

This module records finite bookkeeping for rooted product constructions.
-/

namespace AnalyticCombinatorics.AppA.FiniteRootedProductModels

structure RootedProductData where
  productRoots : ℕ
  factorWindow : ℕ
  productSlack : ℕ
deriving DecidableEq, Repr

def hasProductRoots (d : RootedProductData) : Prop :=
  0 < d.productRoots

def factorWindowControlled (d : RootedProductData) : Prop :=
  d.factorWindow ≤ d.productRoots + d.productSlack

def rootedProductReady (d : RootedProductData) : Prop :=
  hasProductRoots d ∧ factorWindowControlled d

def rootedProductBudget (d : RootedProductData) : ℕ :=
  d.productRoots + d.factorWindow + d.productSlack

theorem rootedProductReady.hasProductRoots {d : RootedProductData}
    (h : rootedProductReady d) :
    hasProductRoots d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem factorWindow_le_budget (d : RootedProductData) :
    d.factorWindow ≤ rootedProductBudget d := by
  unfold rootedProductBudget
  omega

def sampleRootedProductData : RootedProductData :=
  { productRoots := 6, factorWindow := 8, productSlack := 3 }

example : rootedProductReady sampleRootedProductData := by
  norm_num [rootedProductReady, hasProductRoots]
  norm_num [factorWindowControlled, sampleRootedProductData]

example : rootedProductBudget sampleRootedProductData = 17 := by
  native_decide

structure RootedProductWindow where
  productRoots : ℕ
  factorWindow : ℕ
  productSlack : ℕ
  rootedFactorBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def RootedProductWindow.factorControlled (w : RootedProductWindow) : Prop :=
  w.factorWindow ≤ w.productRoots + w.productSlack + w.slack

def RootedProductWindow.rootedFactorControlled (w : RootedProductWindow) : Prop :=
  w.rootedFactorBudget ≤ w.productRoots + w.factorWindow + w.productSlack + w.slack

def rootedProductWindowReady (w : RootedProductWindow) : Prop :=
  0 < w.productRoots ∧
    w.factorControlled ∧
    w.rootedFactorControlled

def RootedProductWindow.certificate (w : RootedProductWindow) : ℕ :=
  w.productRoots + w.factorWindow + w.productSlack + w.slack

theorem rootedProduct_factorBudget_le_certificate {w : RootedProductWindow}
    (h : rootedProductWindowReady w) :
    w.rootedFactorBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hfactor⟩
  exact hfactor

def sampleRootedProductWindow : RootedProductWindow :=
  { productRoots := 6, factorWindow := 8, productSlack := 3, rootedFactorBudget := 16, slack := 0 }

example : rootedProductWindowReady sampleRootedProductWindow := by
  norm_num [rootedProductWindowReady, RootedProductWindow.factorControlled,
    RootedProductWindow.rootedFactorControlled, sampleRootedProductWindow]

example : sampleRootedProductWindow.certificate = 17 := by
  native_decide


structure FiniteRootedProductModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteRootedProductModelsBudgetCertificate.controlled
    (c : FiniteRootedProductModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteRootedProductModelsBudgetCertificate.budgetControlled
    (c : FiniteRootedProductModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteRootedProductModelsBudgetCertificate.Ready
    (c : FiniteRootedProductModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteRootedProductModelsBudgetCertificate.size
    (c : FiniteRootedProductModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteRootedProductModels_budgetCertificate_le_size
    (c : FiniteRootedProductModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteRootedProductModelsBudgetCertificate :
    FiniteRootedProductModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteRootedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedProductModelsBudgetCertificate.controlled,
      sampleFiniteRootedProductModelsBudgetCertificate]
  · norm_num [FiniteRootedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedProductModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteRootedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedProductModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteRootedProductModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteRootedProductModelsBudgetCertificate.controlled,
      sampleFiniteRootedProductModelsBudgetCertificate]
  · norm_num [FiniteRootedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedProductModelsBudgetCertificate]

example :
    sampleFiniteRootedProductModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteRootedProductModelsBudgetCertificate.size := by
  apply finiteRootedProductModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteRootedProductModelsBudgetCertificate.controlled,
      sampleFiniteRootedProductModelsBudgetCertificate]
  · norm_num [FiniteRootedProductModelsBudgetCertificate.budgetControlled,
      sampleFiniteRootedProductModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteRootedProductModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteRootedProductModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteRootedProductModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteRootedProductModels
