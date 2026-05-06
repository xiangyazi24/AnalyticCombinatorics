import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Laurent window models.

This module isolates a small Laurent-window schema where a positive annulus
width controls the Laurent order up to a tail slack.
-/

namespace AnalyticCombinatorics.AppB.UniformLaurentWindowModels

structure LaurentWindowData where
  annulusWidth : ℕ
  laurentOrder : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def hasAnnulusWidth (d : LaurentWindowData) : Prop :=
  0 < d.annulusWidth

def laurentOrderControlled (d : LaurentWindowData) : Prop :=
  d.laurentOrder ≤ d.annulusWidth + d.tailSlack

def laurentWindowReady (d : LaurentWindowData) : Prop :=
  hasAnnulusWidth d ∧ laurentOrderControlled d

def laurentWindowBudget (d : LaurentWindowData) : ℕ :=
  d.annulusWidth + d.laurentOrder + d.tailSlack

theorem laurentWindowReady.hasAnnulusWidth {d : LaurentWindowData}
    (h : laurentWindowReady d) :
    hasAnnulusWidth d ∧ laurentOrderControlled d ∧
      d.laurentOrder ≤ laurentWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold laurentWindowBudget
  omega

theorem laurentOrder_le_budget (d : LaurentWindowData) :
    d.laurentOrder ≤ laurentWindowBudget d := by
  unfold laurentWindowBudget
  omega

def sampleLaurentWindowData : LaurentWindowData :=
  { annulusWidth := 5, laurentOrder := 7, tailSlack := 3 }

example : laurentWindowReady sampleLaurentWindowData := by
  norm_num [laurentWindowReady, hasAnnulusWidth]
  norm_num [laurentOrderControlled, sampleLaurentWindowData]

example : laurentWindowBudget sampleLaurentWindowData = 15 := by
  native_decide

/-- Finite executable readiness audit for a list of Laurent windows. -/
def laurentWindowListReady (windows : List LaurentWindowData) : Bool :=
  windows.all fun d =>
    0 < d.annulusWidth && d.laurentOrder ≤ d.annulusWidth + d.tailSlack

theorem laurentWindowList_readyWindow :
    laurentWindowListReady
      [{ annulusWidth := 3, laurentOrder := 4, tailSlack := 1 },
       { annulusWidth := 5, laurentOrder := 7, tailSlack := 3 }] = true := by
  unfold laurentWindowListReady
  native_decide


structure UniformLaurentWindowModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformLaurentWindowModelsBudgetCertificate.controlled
    (c : UniformLaurentWindowModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def UniformLaurentWindowModelsBudgetCertificate.budgetControlled
    (c : UniformLaurentWindowModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformLaurentWindowModelsBudgetCertificate.Ready
    (c : UniformLaurentWindowModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformLaurentWindowModelsBudgetCertificate.size
    (c : UniformLaurentWindowModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformLaurentWindowModels_budgetCertificate_le_size
    (c : UniformLaurentWindowModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformLaurentWindowModelsBudgetCertificate :
    UniformLaurentWindowModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleUniformLaurentWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.controlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformLaurentWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaurentWindowModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleUniformLaurentWindowModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.controlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]

example :
    sampleUniformLaurentWindowModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformLaurentWindowModelsBudgetCertificate.size := by
  apply uniformLaurentWindowModels_budgetCertificate_le_size
  constructor
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.controlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]
  · norm_num [UniformLaurentWindowModelsBudgetCertificate.budgetControlled,
      sampleUniformLaurentWindowModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List UniformLaurentWindowModelsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformLaurentWindowModelsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformLaurentWindowModelsBudgetCertificate
  native_decide
end AnalyticCombinatorics.AppB.UniformLaurentWindowModels
