import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Labelled product window schemas.

This module records finite bookkeeping for labelled product windows.
-/

namespace AnalyticCombinatorics.PartA.Ch2.LabelledProductWindowSchemas

structure LabelledProductSchemaData where
  productLabels : ℕ
  factorWindow : ℕ
  productSlack : ℕ
deriving DecidableEq, Repr

def hasProductLabels (d : LabelledProductSchemaData) : Prop :=
  0 < d.productLabels

def factorWindowControlled (d : LabelledProductSchemaData) : Prop :=
  d.factorWindow ≤ d.productLabels + d.productSlack

def labelledProductSchemaReady (d : LabelledProductSchemaData) : Prop :=
  hasProductLabels d ∧ factorWindowControlled d

def labelledProductSchemaBudget (d : LabelledProductSchemaData) : ℕ :=
  d.productLabels + d.factorWindow + d.productSlack

theorem labelledProductSchemaReady.hasProductLabels
    {d : LabelledProductSchemaData}
    (h : labelledProductSchemaReady d) :
    hasProductLabels d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem factorWindow_le_budget (d : LabelledProductSchemaData) :
    d.factorWindow ≤ labelledProductSchemaBudget d := by
  unfold labelledProductSchemaBudget
  omega

def sampleLabelledProductSchemaData : LabelledProductSchemaData :=
  { productLabels := 6, factorWindow := 8, productSlack := 3 }

example : labelledProductSchemaReady sampleLabelledProductSchemaData := by
  norm_num [labelledProductSchemaReady, hasProductLabels]
  norm_num [factorWindowControlled, sampleLabelledProductSchemaData]

example : labelledProductSchemaBudget sampleLabelledProductSchemaData = 17 := by
  native_decide

structure LabelledProductWindowBudgetCertificate where
  labelWindow : ℕ
  factorWindow : ℕ
  productSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def LabelledProductWindowBudgetCertificate.controlled
    (c : LabelledProductWindowBudgetCertificate) : Prop :=
  0 < c.labelWindow ∧
    c.factorWindow ≤ c.labelWindow + c.productSlackWindow + c.slack

def LabelledProductWindowBudgetCertificate.budgetControlled
    (c : LabelledProductWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.labelWindow + c.factorWindow + c.productSlackWindow + c.slack

def LabelledProductWindowBudgetCertificate.Ready
    (c : LabelledProductWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def LabelledProductWindowBudgetCertificate.size
    (c : LabelledProductWindowBudgetCertificate) : ℕ :=
  c.labelWindow + c.factorWindow + c.productSlackWindow + c.slack

theorem labelledProductWindow_budgetCertificate_le_size
    (c : LabelledProductWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleLabelledProductWindowBudgetCertificate :
    LabelledProductWindowBudgetCertificate :=
  { labelWindow := 6
    factorWindow := 8
    productSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleLabelledProductWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledProductWindowBudgetCertificate.controlled,
      sampleLabelledProductWindowBudgetCertificate]
  · norm_num [LabelledProductWindowBudgetCertificate.budgetControlled,
      sampleLabelledProductWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleLabelledProductWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledProductWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleLabelledProductWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [LabelledProductWindowBudgetCertificate.controlled,
      sampleLabelledProductWindowBudgetCertificate]
  · norm_num [LabelledProductWindowBudgetCertificate.budgetControlled,
      sampleLabelledProductWindowBudgetCertificate]

example :
    sampleLabelledProductWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleLabelledProductWindowBudgetCertificate.size := by
  apply labelledProductWindow_budgetCertificate_le_size
  constructor
  · norm_num [LabelledProductWindowBudgetCertificate.controlled,
      sampleLabelledProductWindowBudgetCertificate]
  · norm_num [LabelledProductWindowBudgetCertificate.budgetControlled,
      sampleLabelledProductWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List LabelledProductWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleLabelledProductWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleLabelledProductWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch2.LabelledProductWindowSchemas
