import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Holomorphic germ bookkeeping.

The analytic germ is represented by finite order, radius, and coefficient
budgets.
-/

namespace AnalyticCombinatorics.AppB.HolomorphicGermModels

structure GermDatum where
  vanishingOrder : ℕ
  radiusBudget : ℕ
  coefficientBudget : ℕ
deriving DecidableEq, Repr

def positiveRadius (g : GermDatum) : Prop :=
  0 < g.radiusBudget

def coefficientControlled (g : GermDatum) : Prop :=
  g.coefficientBudget ≤ g.radiusBudget + g.vanishingOrder

def germReady (g : GermDatum) : Prop :=
  positiveRadius g ∧ coefficientControlled g

def germComplexity (g : GermDatum) : ℕ :=
  g.vanishingOrder + g.radiusBudget + g.coefficientBudget

theorem germReady.radius {g : GermDatum}
    (h : germReady g) :
    positiveRadius g ∧ coefficientControlled g ∧
      g.radiusBudget ≤ germComplexity g := by
  refine ⟨h.1, h.2, ?_⟩
  unfold germComplexity
  omega

theorem radiusBudget_le_complexity (g : GermDatum) :
    g.radiusBudget ≤ germComplexity g := by
  unfold germComplexity
  omega

def sampleGerm : GermDatum :=
  { vanishingOrder := 2, radiusBudget := 5, coefficientBudget := 6 }

example : germReady sampleGerm := by
  norm_num [germReady, positiveRadius, coefficientControlled, sampleGerm]

example : germComplexity sampleGerm = 13 := by
  native_decide

structure GermWindow where
  orderWindow : ℕ
  radiusWindow : ℕ
  coefficientWindow : ℕ
  germBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def GermWindow.coefficientsControlled (w : GermWindow) : Prop :=
  w.coefficientWindow ≤ w.radiusWindow + w.orderWindow + w.slack

def germWindowReady (w : GermWindow) : Prop :=
  0 < w.radiusWindow ∧ w.coefficientsControlled ∧
    w.germBudget ≤ w.orderWindow + w.radiusWindow + w.coefficientWindow + w.slack

def GermWindow.certificate (w : GermWindow) : ℕ :=
  w.orderWindow + w.radiusWindow + w.coefficientWindow + w.germBudget + w.slack

theorem germ_germBudget_le_certificate (w : GermWindow) :
    w.germBudget ≤ w.certificate := by
  unfold GermWindow.certificate
  omega

def sampleGermWindow : GermWindow :=
  { orderWindow := 2, radiusWindow := 5, coefficientWindow := 6, germBudget := 14, slack := 1 }

example : germWindowReady sampleGermWindow := by
  norm_num [germWindowReady, GermWindow.coefficientsControlled, sampleGermWindow]


structure HolomorphicGermModelsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def HolomorphicGermModelsBudgetCertificate.controlled
    (c : HolomorphicGermModelsBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def HolomorphicGermModelsBudgetCertificate.budgetControlled
    (c : HolomorphicGermModelsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def HolomorphicGermModelsBudgetCertificate.Ready
    (c : HolomorphicGermModelsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def HolomorphicGermModelsBudgetCertificate.size
    (c : HolomorphicGermModelsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem holomorphicGermModels_budgetCertificate_le_size
    (c : HolomorphicGermModelsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleHolomorphicGermModelsBudgetCertificate :
    HolomorphicGermModelsBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleHolomorphicGermModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolomorphicGermModelsBudgetCertificate.controlled,
      sampleHolomorphicGermModelsBudgetCertificate]
  · norm_num [HolomorphicGermModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicGermModelsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleHolomorphicGermModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHolomorphicGermModelsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

example : sampleHolomorphicGermModelsBudgetCertificate.Ready := by
  constructor
  · norm_num [HolomorphicGermModelsBudgetCertificate.controlled,
      sampleHolomorphicGermModelsBudgetCertificate]
  · norm_num [HolomorphicGermModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicGermModelsBudgetCertificate]

example :
    sampleHolomorphicGermModelsBudgetCertificate.certificateBudgetWindow ≤
      sampleHolomorphicGermModelsBudgetCertificate.size := by
  apply holomorphicGermModels_budgetCertificate_le_size
  constructor
  · norm_num [HolomorphicGermModelsBudgetCertificate.controlled,
      sampleHolomorphicGermModelsBudgetCertificate]
  · norm_num [HolomorphicGermModelsBudgetCertificate.budgetControlled,
      sampleHolomorphicGermModelsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
def budgetCertificateListReady (data : List HolomorphicGermModelsBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleHolomorphicGermModelsBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleHolomorphicGermModelsBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppB.HolomorphicGermModels
