import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Mixing limit schemas.

The finite schema records mixing window, state budget, and tail slack.
-/

namespace AnalyticCombinatorics.AppC.MixingLimitSchemas

structure MixingLimitData where
  mixingWindow : ℕ
  stateBudget : ℕ
  tailSlack : ℕ
deriving DecidableEq, Repr

def stateBudgetPositive (d : MixingLimitData) : Prop :=
  0 < d.stateBudget

def mixingWindowControlled (d : MixingLimitData) : Prop :=
  d.mixingWindow ≤ d.stateBudget + d.tailSlack

def mixingLimitReady (d : MixingLimitData) : Prop :=
  stateBudgetPositive d ∧ mixingWindowControlled d

def mixingLimitBudget (d : MixingLimitData) : ℕ :=
  d.mixingWindow + d.stateBudget + d.tailSlack

theorem mixingLimitReady.states {d : MixingLimitData}
    (h : mixingLimitReady d) :
    stateBudgetPositive d ∧ mixingWindowControlled d ∧ d.mixingWindow ≤ mixingLimitBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold mixingLimitBudget
  omega

theorem mixingWindow_le_mixingLimitBudget (d : MixingLimitData) :
    d.mixingWindow ≤ mixingLimitBudget d := by
  unfold mixingLimitBudget
  omega

def sampleMixingLimitData : MixingLimitData :=
  { mixingWindow := 6, stateBudget := 4, tailSlack := 3 }

example : mixingLimitReady sampleMixingLimitData := by
  norm_num [mixingLimitReady, stateBudgetPositive]
  norm_num [mixingWindowControlled, sampleMixingLimitData]

example : mixingLimitBudget sampleMixingLimitData = 13 := by
  native_decide

structure MixingLimitWindow where
  mixingWindow : ℕ
  stateBudget : ℕ
  tailSlack : ℕ
  couplingBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MixingLimitWindow.windowControlled (w : MixingLimitWindow) : Prop :=
  w.mixingWindow ≤ w.stateBudget + w.tailSlack + w.slack

def MixingLimitWindow.couplingControlled (w : MixingLimitWindow) : Prop :=
  w.couplingBudget ≤ w.mixingWindow + w.stateBudget + w.tailSlack + w.slack

def mixingLimitWindowReady (w : MixingLimitWindow) : Prop :=
  0 < w.stateBudget ∧
    w.windowControlled ∧
    w.couplingControlled

def MixingLimitWindow.certificate (w : MixingLimitWindow) : ℕ :=
  w.mixingWindow + w.stateBudget + w.tailSlack + w.slack

theorem mixingLimit_couplingBudget_le_certificate {w : MixingLimitWindow}
    (h : mixingLimitWindowReady w) :
    w.couplingBudget ≤ w.certificate := by
  rcases h with ⟨_, _, hcoupling⟩
  exact hcoupling

def sampleMixingLimitWindow : MixingLimitWindow :=
  { mixingWindow := 6, stateBudget := 4, tailSlack := 3, couplingBudget := 12, slack := 0 }

example : mixingLimitWindowReady sampleMixingLimitWindow := by
  norm_num [mixingLimitWindowReady, MixingLimitWindow.windowControlled,
    MixingLimitWindow.couplingControlled, sampleMixingLimitWindow]

example : sampleMixingLimitWindow.certificate = 13 := by
  native_decide


structure MixingLimitSchemasBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def MixingLimitSchemasBudgetCertificate.controlled
    (c : MixingLimitSchemasBudgetCertificate) : Prop :=
  c.primaryWindow ≤ c.secondaryWindow + c.slack

def MixingLimitSchemasBudgetCertificate.budgetControlled
    (c : MixingLimitSchemasBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def MixingLimitSchemasBudgetCertificate.Ready
    (c : MixingLimitSchemasBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def MixingLimitSchemasBudgetCertificate.size
    (c : MixingLimitSchemasBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem mixingLimitSchemas_budgetCertificate_le_size
    (c : MixingLimitSchemasBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleMixingLimitSchemasBudgetCertificate :
    MixingLimitSchemasBudgetCertificate :=
  { primaryWindow := 3
    secondaryWindow := 5
    certificateBudgetWindow := 9
    slack := 1 }

theorem sampleBudgetCertificate_ready :
    sampleMixingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MixingLimitSchemasBudgetCertificate.controlled,
      sampleMixingLimitSchemasBudgetCertificate]
  · norm_num [MixingLimitSchemasBudgetCertificate.budgetControlled,
      sampleMixingLimitSchemasBudgetCertificate]

example : sampleMixingLimitSchemasBudgetCertificate.Ready := by
  constructor
  · norm_num [MixingLimitSchemasBudgetCertificate.controlled,
      sampleMixingLimitSchemasBudgetCertificate]
  · norm_num [MixingLimitSchemasBudgetCertificate.budgetControlled,
      sampleMixingLimitSchemasBudgetCertificate]

example :
    sampleMixingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMixingLimitSchemasBudgetCertificate.size := by
  apply mixingLimitSchemas_budgetCertificate_le_size
  constructor
  · norm_num [MixingLimitSchemasBudgetCertificate.controlled,
      sampleMixingLimitSchemasBudgetCertificate]
  · norm_num [MixingLimitSchemasBudgetCertificate.budgetControlled,
      sampleMixingLimitSchemasBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_le_size :
    sampleMixingLimitSchemasBudgetCertificate.certificateBudgetWindow ≤
      sampleMixingLimitSchemasBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady (data : List MixingLimitSchemasBudgetCertificate) : Bool :=
  data.all fun c =>
    c.primaryWindow ≤ c.secondaryWindow + c.slack &&
      c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleMixingLimitSchemasBudgetCertificate,
       { primaryWindow := 4, secondaryWindow := 6,
         certificateBudgetWindow := 11, slack := 1 }] = true := by
  unfold budgetCertificateListReady sampleMixingLimitSchemasBudgetCertificate
  native_decide

end AnalyticCombinatorics.AppC.MixingLimitSchemas
