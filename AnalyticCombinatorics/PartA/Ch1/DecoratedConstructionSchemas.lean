import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Decorated construction schemas.

This module records finite bookkeeping for decorated constructions.
-/

namespace AnalyticCombinatorics.PartA.Ch1.DecoratedConstructionSchemas

structure DecoratedConstructionData where
  constructionSize : ℕ
  decorationSlots : ℕ
  decorationSlack : ℕ
deriving DecidableEq, Repr

def hasConstructionSize (d : DecoratedConstructionData) : Prop :=
  0 < d.constructionSize

def decorationSlotsControlled (d : DecoratedConstructionData) : Prop :=
  d.decorationSlots ≤ d.constructionSize + d.decorationSlack

def decoratedConstructionReady (d : DecoratedConstructionData) : Prop :=
  hasConstructionSize d ∧ decorationSlotsControlled d

def decoratedConstructionBudget (d : DecoratedConstructionData) : ℕ :=
  d.constructionSize + d.decorationSlots + d.decorationSlack

theorem decoratedConstructionReady.hasConstructionSize
    {d : DecoratedConstructionData}
    (h : decoratedConstructionReady d) :
    hasConstructionSize d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem decorationSlots_le_budget (d : DecoratedConstructionData) :
    d.decorationSlots ≤ decoratedConstructionBudget d := by
  unfold decoratedConstructionBudget
  omega

def sampleDecoratedConstructionData : DecoratedConstructionData :=
  { constructionSize := 6, decorationSlots := 8, decorationSlack := 3 }

example : decoratedConstructionReady sampleDecoratedConstructionData := by
  norm_num [decoratedConstructionReady, hasConstructionSize]
  norm_num [decorationSlotsControlled, sampleDecoratedConstructionData]

example : decoratedConstructionBudget sampleDecoratedConstructionData = 17 := by
  native_decide

structure DecoratedConstructionBudgetCertificate where
  constructionWindow : ℕ
  decorationWindow : ℕ
  slackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DecoratedConstructionBudgetCertificate.controlled
    (c : DecoratedConstructionBudgetCertificate) : Prop :=
  0 < c.constructionWindow ∧
    c.decorationWindow ≤ c.constructionWindow + c.slackWindow + c.slack

def DecoratedConstructionBudgetCertificate.budgetControlled
    (c : DecoratedConstructionBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.constructionWindow + c.decorationWindow + c.slackWindow + c.slack

def DecoratedConstructionBudgetCertificate.Ready
    (c : DecoratedConstructionBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DecoratedConstructionBudgetCertificate.size
    (c : DecoratedConstructionBudgetCertificate) : ℕ :=
  c.constructionWindow + c.decorationWindow + c.slackWindow + c.slack

theorem decoratedConstruction_budgetCertificate_le_size
    (c : DecoratedConstructionBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDecoratedConstructionBudgetCertificate :
    DecoratedConstructionBudgetCertificate :=
  { constructionWindow := 6
    decorationWindow := 8
    slackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDecoratedConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [DecoratedConstructionBudgetCertificate.controlled,
      sampleDecoratedConstructionBudgetCertificate]
  · norm_num [DecoratedConstructionBudgetCertificate.budgetControlled,
      sampleDecoratedConstructionBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDecoratedConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleDecoratedConstructionBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDecoratedConstructionBudgetCertificate.Ready := by
  constructor
  · norm_num [DecoratedConstructionBudgetCertificate.controlled,
      sampleDecoratedConstructionBudgetCertificate]
  · norm_num [DecoratedConstructionBudgetCertificate.budgetControlled,
      sampleDecoratedConstructionBudgetCertificate]

example :
    sampleDecoratedConstructionBudgetCertificate.certificateBudgetWindow ≤
      sampleDecoratedConstructionBudgetCertificate.size := by
  apply decoratedConstruction_budgetCertificate_le_size
  constructor
  · norm_num [DecoratedConstructionBudgetCertificate.controlled,
      sampleDecoratedConstructionBudgetCertificate]
  · norm_num [DecoratedConstructionBudgetCertificate.budgetControlled,
      sampleDecoratedConstructionBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DecoratedConstructionBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDecoratedConstructionBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleDecoratedConstructionBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartA.Ch1.DecoratedConstructionSchemas
