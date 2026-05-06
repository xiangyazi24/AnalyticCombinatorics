import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Darboux window schemas.

This module records finite bookkeeping for Darboux transfer windows: a
positive contact order controls coefficient depth with boundary slack.
-/

namespace AnalyticCombinatorics.PartB.Ch6.DarbouxWindowSchemas

structure DarbouxWindowData where
  contactOrder : ℕ
  coefficientDepth : ℕ
  boundarySlack : ℕ
deriving DecidableEq, Repr

def hasContactOrder (d : DarbouxWindowData) : Prop :=
  0 < d.contactOrder

def coefficientDepthControlled (d : DarbouxWindowData) : Prop :=
  d.coefficientDepth ≤ d.contactOrder + d.boundarySlack

def darbouxWindowReady (d : DarbouxWindowData) : Prop :=
  hasContactOrder d ∧ coefficientDepthControlled d

def darbouxWindowBudget (d : DarbouxWindowData) : ℕ :=
  d.contactOrder + d.coefficientDepth + d.boundarySlack

theorem darbouxWindowReady.hasContactOrder {d : DarbouxWindowData}
    (h : darbouxWindowReady d) :
    hasContactOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem coefficientDepth_le_budget (d : DarbouxWindowData) :
    d.coefficientDepth ≤ darbouxWindowBudget d := by
  unfold darbouxWindowBudget
  omega

def sampleDarbouxWindowData : DarbouxWindowData :=
  { contactOrder := 6, coefficientDepth := 8, boundarySlack := 3 }

example : darbouxWindowReady sampleDarbouxWindowData := by
  norm_num [darbouxWindowReady, hasContactOrder]
  norm_num [coefficientDepthControlled, sampleDarbouxWindowData]

example : darbouxWindowBudget sampleDarbouxWindowData = 17 := by
  native_decide

structure DarbouxWindowBudgetCertificate where
  contactOrderWindow : ℕ
  coefficientDepthWindow : ℕ
  boundarySlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxWindowBudgetCertificate.controlled
    (c : DarbouxWindowBudgetCertificate) : Prop :=
  0 < c.contactOrderWindow ∧
    c.coefficientDepthWindow ≤
      c.contactOrderWindow + c.boundarySlackWindow + c.slack

def DarbouxWindowBudgetCertificate.budgetControlled
    (c : DarbouxWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.contactOrderWindow + c.coefficientDepthWindow + c.boundarySlackWindow +
      c.slack

def DarbouxWindowBudgetCertificate.Ready
    (c : DarbouxWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def DarbouxWindowBudgetCertificate.size
    (c : DarbouxWindowBudgetCertificate) : ℕ :=
  c.contactOrderWindow + c.coefficientDepthWindow + c.boundarySlackWindow +
    c.slack

theorem darbouxWindow_budgetCertificate_le_size
    (c : DarbouxWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDarbouxWindowBudgetCertificate :
    DarbouxWindowBudgetCertificate :=
  { contactOrderWindow := 6
    coefficientDepthWindow := 8
    boundarySlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleDarbouxWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxWindowBudgetCertificate.controlled,
      sampleDarbouxWindowBudgetCertificate]
  · norm_num [DarbouxWindowBudgetCertificate.budgetControlled,
      sampleDarbouxWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleDarbouxWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleDarbouxWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleDarbouxWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [DarbouxWindowBudgetCertificate.controlled,
      sampleDarbouxWindowBudgetCertificate]
  · norm_num [DarbouxWindowBudgetCertificate.budgetControlled,
      sampleDarbouxWindowBudgetCertificate]

example :
    sampleDarbouxWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleDarbouxWindowBudgetCertificate.size := by
  apply darbouxWindow_budgetCertificate_le_size
  constructor
  · norm_num [DarbouxWindowBudgetCertificate.controlled,
      sampleDarbouxWindowBudgetCertificate]
  · norm_num [DarbouxWindowBudgetCertificate.budgetControlled,
      sampleDarbouxWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List DarbouxWindowBudgetCertificate) : Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady [sampleDarbouxWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady sampleDarbouxWindowBudgetCertificate
  native_decide

end AnalyticCombinatorics.PartB.Ch6.DarbouxWindowSchemas
