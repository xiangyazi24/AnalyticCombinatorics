import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Stable coupling window schemas.

This module records finite bookkeeping for stable-law coupling windows.
-/

namespace AnalyticCombinatorics.AppC.StableCouplingWindowSchemas

structure StableCouplingWindowData where
  stableScale : ℕ
  couplingWindow : ℕ
  stableSlack : ℕ
deriving DecidableEq, Repr

def hasStableScale (d : StableCouplingWindowData) : Prop :=
  0 < d.stableScale

def couplingWindowControlled (d : StableCouplingWindowData) : Prop :=
  d.couplingWindow ≤ d.stableScale + d.stableSlack

def stableCouplingWindowReady (d : StableCouplingWindowData) : Prop :=
  hasStableScale d ∧ couplingWindowControlled d

def stableCouplingWindowBudget (d : StableCouplingWindowData) : ℕ :=
  d.stableScale + d.couplingWindow + d.stableSlack

theorem stableCouplingWindowReady.hasStableScale
    {d : StableCouplingWindowData}
    (h : stableCouplingWindowReady d) :
    hasStableScale d := by
  rcases h with ⟨hleft, hright⟩
  exact hleft

theorem couplingWindow_le_budget (d : StableCouplingWindowData) :
    d.couplingWindow ≤ stableCouplingWindowBudget d := by
  unfold stableCouplingWindowBudget
  omega

def sampleStableCouplingWindowData : StableCouplingWindowData :=
  { stableScale := 7, couplingWindow := 9, stableSlack := 3 }

example : stableCouplingWindowReady sampleStableCouplingWindowData := by
  norm_num [stableCouplingWindowReady, hasStableScale]
  norm_num [couplingWindowControlled, sampleStableCouplingWindowData]

example : stableCouplingWindowBudget sampleStableCouplingWindowData = 19 := by
  native_decide

structure StableCouplingCertificateWindow where
  stableWindow : ℕ
  couplingWindow : ℕ
  stableSlack : ℕ
  stableBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableCouplingCertificateWindow.couplingControlled
    (w : StableCouplingCertificateWindow) : Prop :=
  w.couplingWindow ≤ w.stableWindow + w.stableSlack + w.slack

def stableCouplingCertificateReady (w : StableCouplingCertificateWindow) : Prop :=
  0 < w.stableWindow ∧ w.couplingControlled ∧
    w.stableBudget ≤ w.stableWindow + w.couplingWindow + w.slack

def StableCouplingCertificateWindow.certificate
    (w : StableCouplingCertificateWindow) : ℕ :=
  w.stableWindow + w.couplingWindow + w.stableSlack + w.stableBudget + w.slack

theorem stableCoupling_stableBudget_le_certificate
    (w : StableCouplingCertificateWindow) :
    w.stableBudget ≤ w.certificate := by
  unfold StableCouplingCertificateWindow.certificate
  omega

def sampleStableCouplingCertificateWindow : StableCouplingCertificateWindow :=
  { stableWindow := 6, couplingWindow := 8, stableSlack := 2, stableBudget := 15, slack := 1 }

example : stableCouplingCertificateReady sampleStableCouplingCertificateWindow := by
  norm_num [stableCouplingCertificateReady,
    StableCouplingCertificateWindow.couplingControlled, sampleStableCouplingCertificateWindow]


structure StableCouplingWindowSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def StableCouplingWindowSchemasBudgetCertificate.controlled
    (c : StableCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def StableCouplingWindowSchemasBudgetCertificate.budgetControlled
    (c : StableCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def StableCouplingWindowSchemasBudgetCertificate.Ready
    (c : StableCouplingWindowSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def StableCouplingWindowSchemasBudgetCertificate.size
    (c : StableCouplingWindowSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem stableCouplingWindowSchemas_budgetCertificate_le_size
    (c : StableCouplingWindowSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleStableCouplingWindowSchemasBudgetCertificate :
    StableCouplingWindowSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleStableCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.controlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]

example : sampleStableCouplingWindowSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.controlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]

example :
    sampleStableCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableCouplingWindowSchemasBudgetCertificate.size := by
  apply stableCouplingWindowSchemas_budgetCertificate_le_size
  constructor
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.controlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]
  · norm_num [StableCouplingWindowSchemasBudgetCertificate.budgetControlled,
      sampleStableCouplingWindowSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleStableCouplingWindowSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleStableCouplingWindowSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List StableCouplingWindowSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleStableCouplingWindowSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleStableCouplingWindowSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.StableCouplingWindowSchemas
