import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Finite tree substitution models.

This module records finite bookkeeping for substituting finite trees.
-/

namespace AnalyticCombinatorics.AppA.FiniteTreeSubstitutionModels

structure TreeSubstitutionData where
  treeNodes : ℕ
  substitutionWindow : ℕ
  treeSlack : ℕ
deriving DecidableEq, Repr

def hasTreeNodes (d : TreeSubstitutionData) : Prop :=
  0 < d.treeNodes

def substitutionWindowControlled (d : TreeSubstitutionData) : Prop :=
  d.substitutionWindow ≤ d.treeNodes + d.treeSlack

def treeSubstitutionReady (d : TreeSubstitutionData) : Prop :=
  hasTreeNodes d ∧ substitutionWindowControlled d

def treeSubstitutionBudget (d : TreeSubstitutionData) : ℕ :=
  d.treeNodes + d.substitutionWindow + d.treeSlack

theorem treeSubstitutionReady.hasTreeNodes {d : TreeSubstitutionData}
    (h : treeSubstitutionReady d) :
    hasTreeNodes d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem substitutionWindow_le_budget (d : TreeSubstitutionData) :
    d.substitutionWindow ≤ treeSubstitutionBudget d := by
  unfold treeSubstitutionBudget
  omega

def sampleTreeSubstitutionData : TreeSubstitutionData :=
  { treeNodes := 7, substitutionWindow := 9, treeSlack := 3 }

example : treeSubstitutionReady sampleTreeSubstitutionData := by
  norm_num [treeSubstitutionReady, hasTreeNodes]
  norm_num [substitutionWindowControlled, sampleTreeSubstitutionData]

example : treeSubstitutionBudget sampleTreeSubstitutionData = 19 := by
  native_decide

structure TreeSubstitutionWindow where
  treeNodes : ℕ
  substitutionWindow : ℕ
  treeSlack : ℕ
  graftBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def TreeSubstitutionWindow.substitutionControlled (w : TreeSubstitutionWindow) : Prop :=
  w.substitutionWindow ≤ w.treeNodes + w.treeSlack + w.slack

def TreeSubstitutionWindow.graftControlled (w : TreeSubstitutionWindow) : Prop :=
  w.graftBudget ≤ w.treeNodes + w.substitutionWindow + w.treeSlack + w.slack

def treeSubstitutionWindowReady (w : TreeSubstitutionWindow) : Prop :=
  0 < w.treeNodes ∧
    w.substitutionControlled ∧
    w.graftControlled

def TreeSubstitutionWindow.certificate (w : TreeSubstitutionWindow) : ℕ :=
  w.treeNodes + w.substitutionWindow + w.treeSlack + w.slack

theorem treeSubstitution_graftBudget_le_certificate {w : TreeSubstitutionWindow}
    (h : treeSubstitutionWindowReady w) :
    w.graftBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hgraft⟩
  exact hgraft

def sampleTreeSubstitutionWindow : TreeSubstitutionWindow :=
  { treeNodes := 7, substitutionWindow := 9, treeSlack := 3, graftBudget := 18, slack := 0 }

example : treeSubstitutionWindowReady sampleTreeSubstitutionWindow := by
  norm_num [treeSubstitutionWindowReady, TreeSubstitutionWindow.substitutionControlled,
    TreeSubstitutionWindow.graftControlled, sampleTreeSubstitutionWindow]

example : sampleTreeSubstitutionWindow.certificate = 19 := by
  native_decide


structure FiniteTreeSubstitutionModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def FiniteTreeSubstitutionModelsBudgetCertificate.controlled
    (c : FiniteTreeSubstitutionModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def FiniteTreeSubstitutionModelsBudgetCertificate.budgetControlled
    (c : FiniteTreeSubstitutionModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def FiniteTreeSubstitutionModelsBudgetCertificate.Ready
    (c : FiniteTreeSubstitutionModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def FiniteTreeSubstitutionModelsBudgetCertificate.size
    (c : FiniteTreeSubstitutionModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem finiteTreeSubstitutionModels_budgetCertificate_le_size
    (c : FiniteTreeSubstitutionModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleFiniteTreeSubstitutionModelsBudgetCertificate :
    FiniteTreeSubstitutionModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleFiniteTreeSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleFiniteTreeSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTreeSubstitutionModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleFiniteTreeSubstitutionModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]

example :
    sampleFiniteTreeSubstitutionModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleFiniteTreeSubstitutionModelsBudgetCertificate.size := by
  apply finiteTreeSubstitutionModels_budgetCertificate_le_size
  constructor
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.controlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]
  · norm_num [FiniteTreeSubstitutionModelsBudgetCertificate.budgetControlled,
      sampleFiniteTreeSubstitutionModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List FiniteTreeSubstitutionModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleFiniteTreeSubstitutionModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleFiniteTreeSubstitutionModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppA.FiniteTreeSubstitutionModels
