import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite labelled product window models.

This module records finite bookkeeping for labelled product windows.
-/

namespace AnalyticCombinatorics.AppA.FiniteLabelledProductWindowModels

structure LabelledProductWindowData where
  labelBlocks : ℕ
  productWindow : ℕ
  labelSlack : ℕ
deriving DecidableEq, Repr

def hasLabelBlocks (d : LabelledProductWindowData) : Prop :=
  0 < d.labelBlocks

def productWindowControlled (d : LabelledProductWindowData) : Prop :=
  d.productWindow ≤ d.labelBlocks + d.labelSlack

def labelledProductReady (d : LabelledProductWindowData) : Prop :=
  hasLabelBlocks d ∧ productWindowControlled d

def labelledProductBudget (d : LabelledProductWindowData) : ℕ :=
  d.labelBlocks + d.productWindow + d.labelSlack

theorem labelledProductReady.hasLabelBlocks
    {d : LabelledProductWindowData}
    (h : labelledProductReady d) :
    hasLabelBlocks d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem productWindow_le_budget (d : LabelledProductWindowData) :
    d.productWindow ≤ labelledProductBudget d := by
  unfold labelledProductBudget
  omega

def sampleLabelledProductWindowData : LabelledProductWindowData :=
  { labelBlocks := 6, productWindow := 8, labelSlack := 3 }

example : labelledProductReady sampleLabelledProductWindowData := by
  norm_num [labelledProductReady, hasLabelBlocks]
  norm_num [productWindowControlled, sampleLabelledProductWindowData]

example : labelledProductBudget sampleLabelledProductWindowData = 17 := by
  native_decide

structure LabelledProductCertificateWindow where
  labelBlocks : ℕ
  productWindow : ℕ
  labelSlack : ℕ
  productBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledProductCertificateWindow.windowControlled
    (w : LabelledProductCertificateWindow) : Prop :=
  w.productWindow ≤ w.labelBlocks + w.labelSlack + w.slack

def LabelledProductCertificateWindow.productControlled
    (w : LabelledProductCertificateWindow) : Prop :=
  w.productBudget ≤ w.labelBlocks + w.productWindow + w.labelSlack + w.slack

def labelledProductCertificateReady (w : LabelledProductCertificateWindow) : Prop :=
  0 < w.labelBlocks ∧
    w.windowControlled ∧
    w.productControlled

def LabelledProductCertificateWindow.certificate (w : LabelledProductCertificateWindow) : ℕ :=
  w.labelBlocks + w.productWindow + w.labelSlack + w.slack

theorem labelledProduct_productBudget_le_certificate {w : LabelledProductCertificateWindow}
    (h : labelledProductCertificateReady w) :
    w.productBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hproduct⟩
  exact hproduct

def sampleLabelledProductCertificateWindow : LabelledProductCertificateWindow :=
  { labelBlocks := 6, productWindow := 8, labelSlack := 3, productBudget := 16, slack := 0 }

example : labelledProductCertificateReady sampleLabelledProductCertificateWindow := by
  norm_num [labelledProductCertificateReady, LabelledProductCertificateWindow.windowControlled,
    LabelledProductCertificateWindow.productControlled, sampleLabelledProductCertificateWindow]

example : sampleLabelledProductCertificateWindow.certificate = 17 := by
  native_decide


structure FiniteLabelledProductWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteLabelledProductWindowModelsBudgetCertificate.controlled
    (c : FiniteLabelledProductWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteLabelledProductWindowModelsBudgetCertificate.budgetControlled
    (c : FiniteLabelledProductWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteLabelledProductWindowModelsBudgetCertificate.Ready
    (c : FiniteLabelledProductWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteLabelledProductWindowModelsBudgetCertificate.size
    (c : FiniteLabelledProductWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteLabelledProductWindowModels_budgetCertificate_le_size
    (c : FiniteLabelledProductWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteLabelledProductWindowModelsBudgetCertificate :
    FiniteLabelledProductWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteLabelledProductWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteLabelledProductWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledProductWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteLabelledProductWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]

example :
    sampleFiniteLabelledProductWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteLabelledProductWindowModelsBudgetCertificate.size := by
  apply finiteLabelledProductWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.controlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]
  · norm_num [FiniteLabelledProductWindowModelsBudgetCertificate.budgetControlled,
      sampleFiniteLabelledProductWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List FiniteLabelledProductWindowModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteLabelledProductWindowModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteLabelledProductWindowModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteLabelledProductWindowModels
