import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Bessel saddle window schemas.

This module records finite bookkeeping for Bessel-type saddle windows.
-/

namespace AnalyticCombinatorics.PartB.Ch8.BesselSaddleWindowSchemas

structure BesselSaddleWindowData where
  saddleOrder : ℕ
  besselScale : ℕ
  contourSlack : ℕ
deriving DecidableEq, Repr

def hasSaddleOrder (d : BesselSaddleWindowData) : Prop :=
  0 < d.saddleOrder

def besselScaleControlled (d : BesselSaddleWindowData) : Prop :=
  d.besselScale ≤ d.saddleOrder + d.contourSlack

def besselSaddleWindowReady (d : BesselSaddleWindowData) : Prop :=
  hasSaddleOrder d ∧ besselScaleControlled d

def besselSaddleWindowBudget (d : BesselSaddleWindowData) : ℕ :=
  d.saddleOrder + d.besselScale + d.contourSlack

theorem besselSaddleWindowReady.hasSaddleOrder
    {d : BesselSaddleWindowData}
    (h : besselSaddleWindowReady d) :
    hasSaddleOrder d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem besselScale_le_budget (d : BesselSaddleWindowData) :
    d.besselScale ≤ besselSaddleWindowBudget d := by
  unfold besselSaddleWindowBudget
  omega

def sampleBesselSaddleWindowData : BesselSaddleWindowData :=
  { saddleOrder := 6, besselScale := 8, contourSlack := 3 }

example : besselSaddleWindowReady sampleBesselSaddleWindowData := by
  norm_num [besselSaddleWindowReady, hasSaddleOrder]
  norm_num [besselScaleControlled, sampleBesselSaddleWindowData]

example : besselSaddleWindowBudget sampleBesselSaddleWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Bessel saddle windows. -/
def besselSaddleWindowListReady
    (windows : List BesselSaddleWindowData) : Bool :=
  windows.all fun d =>
    0 < d.saddleOrder && d.besselScale ≤ d.saddleOrder + d.contourSlack

theorem besselSaddleWindowList_readyWindow :
    besselSaddleWindowListReady
      [{ saddleOrder := 4, besselScale := 5, contourSlack := 1 },
       { saddleOrder := 6, besselScale := 8, contourSlack := 3 }] = true := by
  unfold besselSaddleWindowListReady
  native_decide

structure BesselSaddleWindowBudgetCertificate where
  saddleOrderWindow : ℕ
  besselScaleWindow : ℕ
  contourSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def BesselSaddleWindowBudgetCertificate.controlled
    (c : BesselSaddleWindowBudgetCertificate) : Prop :=
  0 < c.saddleOrderWindow ∧
    c.besselScaleWindow ≤ c.saddleOrderWindow + c.contourSlackWindow + c.slack

def BesselSaddleWindowBudgetCertificate.budgetControlled
    (c : BesselSaddleWindowBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤
    c.saddleOrderWindow + c.besselScaleWindow + c.contourSlackWindow + c.slack

def BesselSaddleWindowBudgetCertificate.Ready
    (c : BesselSaddleWindowBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def BesselSaddleWindowBudgetCertificate.size
    (c : BesselSaddleWindowBudgetCertificate) : ℕ :=
  c.saddleOrderWindow + c.besselScaleWindow + c.contourSlackWindow + c.slack

theorem besselSaddleWindow_budgetCertificate_le_size
    (c : BesselSaddleWindowBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleBesselSaddleWindowBudgetCertificate :
    BesselSaddleWindowBudgetCertificate :=
  { saddleOrderWindow := 6
    besselScaleWindow := 8
    contourSlackWindow := 3
    certificateBudgetWindow := 18
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleBesselSaddleWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [BesselSaddleWindowBudgetCertificate.controlled,
      sampleBesselSaddleWindowBudgetCertificate]
  · norm_num [BesselSaddleWindowBudgetCertificate.budgetControlled,
      sampleBesselSaddleWindowBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleBesselSaddleWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleBesselSaddleWindowBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleBesselSaddleWindowBudgetCertificate.Ready := by
  constructor
  · norm_num [BesselSaddleWindowBudgetCertificate.controlled,
      sampleBesselSaddleWindowBudgetCertificate]
  · norm_num [BesselSaddleWindowBudgetCertificate.budgetControlled,
      sampleBesselSaddleWindowBudgetCertificate]

example :
    sampleBesselSaddleWindowBudgetCertificate.certificateBudgetWindow ≤
      sampleBesselSaddleWindowBudgetCertificate.size := by
  apply besselSaddleWindow_budgetCertificate_le_size
  constructor
  · norm_num [BesselSaddleWindowBudgetCertificate.controlled,
      sampleBesselSaddleWindowBudgetCertificate]
  · norm_num [BesselSaddleWindowBudgetCertificate.budgetControlled,
      sampleBesselSaddleWindowBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady
    (data : List BesselSaddleWindowBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleBesselSaddleWindowBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleBesselSaddleWindowBudgetCertificate
  native_decide
end AnalyticCombinatorics.PartB.Ch8.BesselSaddleWindowSchemas
