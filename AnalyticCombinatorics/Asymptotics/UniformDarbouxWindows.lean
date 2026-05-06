import Mathlib.Tactic

set_option linter.style.nativeDecide false

/-!
Uniform Darboux windows.

This module records finite bookkeeping for Darboux windows: a positive arc
count controls local expansion order with uniform slack.
-/

namespace AnalyticCombinatorics.Asymptotics.UniformDarbouxWindows

structure DarbouxWindowData where
  arcCount : ℕ
  expansionOrder : ℕ
  uniformSlack : ℕ
deriving DecidableEq, Repr

def hasArcCount (d : DarbouxWindowData) : Prop :=
  0 < d.arcCount

def expansionOrderControlled (d : DarbouxWindowData) : Prop :=
  d.expansionOrder ≤ d.arcCount + d.uniformSlack

def darbouxWindowReady (d : DarbouxWindowData) : Prop :=
  hasArcCount d ∧ expansionOrderControlled d

def darbouxWindowBudget (d : DarbouxWindowData) : ℕ :=
  d.arcCount + d.expansionOrder + d.uniformSlack

theorem darbouxWindowReady.hasArcCount {d : DarbouxWindowData}
    (h : darbouxWindowReady d) :
    hasArcCount d ∧ expansionOrderControlled d ∧ d.expansionOrder ≤ darbouxWindowBudget d := by
  refine ⟨h.1, h.2, ?_⟩
  unfold darbouxWindowBudget
  omega

theorem expansionOrder_le_budget (d : DarbouxWindowData) :
    d.expansionOrder ≤ darbouxWindowBudget d := by
  unfold darbouxWindowBudget
  omega

def sampleDarbouxWindowData : DarbouxWindowData :=
  { arcCount := 6, expansionOrder := 8, uniformSlack := 3 }

example : darbouxWindowReady sampleDarbouxWindowData := by
  norm_num [darbouxWindowReady, hasArcCount]
  norm_num [expansionOrderControlled, sampleDarbouxWindowData]

example : darbouxWindowBudget sampleDarbouxWindowData = 17 := by
  native_decide

/-- Finite executable readiness audit for Darboux window data. -/
def darbouxWindowDataListReady (data : List DarbouxWindowData) : Bool :=
  data.all fun d => 0 < d.arcCount && d.expansionOrder ≤ d.arcCount + d.uniformSlack

theorem darbouxWindowDataList_readyWindow :
    darbouxWindowDataListReady
      [{ arcCount := 4, expansionOrder := 5, uniformSlack := 1 },
       { arcCount := 6, expansionOrder := 8, uniformSlack := 3 }] = true := by
  unfold darbouxWindowDataListReady
  native_decide

structure DarbouxCertificateWindow where
  arcWindow : ℕ
  expansionWindow : ℕ
  uniformSlack : ℕ
  darbouxBudget : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxCertificateWindow.expansionControlled
    (w : DarbouxCertificateWindow) : Prop :=
  w.expansionWindow ≤ w.arcWindow + w.uniformSlack + w.slack

def darbouxCertificateReady (w : DarbouxCertificateWindow) : Prop :=
  0 < w.arcWindow ∧ w.expansionControlled ∧
    w.darbouxBudget ≤ w.arcWindow + w.expansionWindow + w.slack

def DarbouxCertificateWindow.certificate (w : DarbouxCertificateWindow) : ℕ :=
  w.arcWindow + w.expansionWindow + w.uniformSlack + w.darbouxBudget + w.slack

theorem darboux_budget_le_certificate (w : DarbouxCertificateWindow) :
    w.darbouxBudget ≤ w.certificate := by
  unfold DarbouxCertificateWindow.certificate
  omega

def sampleDarbouxCertificateWindow : DarbouxCertificateWindow :=
  { arcWindow := 5, expansionWindow := 7, uniformSlack := 2,
    darbouxBudget := 14, slack := 2 }

example : darbouxCertificateReady sampleDarbouxCertificateWindow := by
  norm_num [darbouxCertificateReady,
    DarbouxCertificateWindow.expansionControlled, sampleDarbouxCertificateWindow]

/-- A refinement certificate for Darboux windows. -/
structure DarbouxRefinementCertificate where
  arcWindow : ℕ
  expansionWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudget : ℕ
  slack : ℕ

/-- The expansion window is controlled by arc count and slack. -/
def darbouxRefinementCertificateControlled
    (w : DarbouxRefinementCertificate) : Prop :=
  0 < w.arcWindow ∧
    w.expansionWindow ≤ w.arcWindow + w.uniformSlackWindow + w.slack

/-- Readiness for a Darboux refinement certificate. -/
def darbouxRefinementCertificateReady
    (w : DarbouxRefinementCertificate) : Prop :=
  darbouxRefinementCertificateControlled w ∧
    w.certificateBudget ≤ w.arcWindow + w.expansionWindow + w.slack

/-- Total size of a Darboux refinement certificate. -/
def darbouxRefinementCertificateSize
    (w : DarbouxRefinementCertificate) : ℕ :=
  w.arcWindow + w.expansionWindow + w.uniformSlackWindow +
    w.certificateBudget + w.slack

theorem darbouxRefinementCertificate_budget_le_size
    (w : DarbouxRefinementCertificate)
    (h : darbouxRefinementCertificateReady w) :
    w.certificateBudget ≤ darbouxRefinementCertificateSize w := by
  rcases h with ⟨_, hbudget⟩
  unfold darbouxRefinementCertificateSize
  omega

def sampleDarbouxRefinementCertificate :
    DarbouxRefinementCertificate where
  arcWindow := 5
  expansionWindow := 7
  uniformSlackWindow := 2
  certificateBudget := 12
  slack := 1

example :
    darbouxRefinementCertificateReady sampleDarbouxRefinementCertificate := by
  norm_num [darbouxRefinementCertificateReady,
    darbouxRefinementCertificateControlled, sampleDarbouxRefinementCertificate]

example :
    sampleDarbouxRefinementCertificate.certificateBudget ≤
      darbouxRefinementCertificateSize sampleDarbouxRefinementCertificate := by
  apply darbouxRefinementCertificate_budget_le_size
  norm_num [darbouxRefinementCertificateReady,
    darbouxRefinementCertificateControlled, sampleDarbouxRefinementCertificate]

/-- A second-stage Darboux certificate keeping the budget external to size. -/
structure DarbouxBudgetRefinementCertificate where
  arcWindow : ℕ
  expansionWindow : ℕ
  uniformSlackWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def DarbouxBudgetRefinementCertificate.expansionControlled
    (cert : DarbouxBudgetRefinementCertificate) : Prop :=
  0 < cert.arcWindow ∧
    cert.expansionWindow ≤ cert.arcWindow + cert.uniformSlackWindow + cert.slack

def DarbouxBudgetRefinementCertificate.budgetControlled
    (cert : DarbouxBudgetRefinementCertificate) : Prop :=
  cert.certificateBudgetWindow ≤
    cert.arcWindow + cert.expansionWindow + cert.uniformSlackWindow + cert.slack

def darbouxBudgetRefinementReady
    (cert : DarbouxBudgetRefinementCertificate) : Prop :=
  cert.expansionControlled ∧ cert.budgetControlled

def DarbouxBudgetRefinementCertificate.size
    (cert : DarbouxBudgetRefinementCertificate) : ℕ :=
  cert.arcWindow + cert.expansionWindow + cert.uniformSlackWindow + cert.slack

theorem darboux_certificateBudgetWindow_le_size
    (cert : DarbouxBudgetRefinementCertificate)
    (h : darbouxBudgetRefinementReady cert) :
    cert.certificateBudgetWindow ≤ cert.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleDarbouxBudgetRefinementCertificate :
    DarbouxBudgetRefinementCertificate :=
  { arcWindow := 5, expansionWindow := 7, uniformSlackWindow := 2,
    certificateBudgetWindow := 15, slack := 1 }

example :
    darbouxBudgetRefinementReady sampleDarbouxBudgetRefinementCertificate := by
  norm_num [darbouxBudgetRefinementReady,
    DarbouxBudgetRefinementCertificate.expansionControlled,
    DarbouxBudgetRefinementCertificate.budgetControlled,
    sampleDarbouxBudgetRefinementCertificate]

example :
    sampleDarbouxBudgetRefinementCertificate.certificateBudgetWindow ≤
      sampleDarbouxBudgetRefinementCertificate.size := by
  apply darboux_certificateBudgetWindow_le_size
  norm_num [darbouxBudgetRefinementReady,
    DarbouxBudgetRefinementCertificate.expansionControlled,
    DarbouxBudgetRefinementCertificate.budgetControlled,
    sampleDarbouxBudgetRefinementCertificate]


structure UniformDarbouxWindowsBudgetCertificate where
  primaryWindow : ℕ
  secondaryWindow : ℕ
  certificateBudgetWindow : ℕ
  slack : ℕ
deriving DecidableEq, Repr

def UniformDarbouxWindowsBudgetCertificate.controlled
    (c : UniformDarbouxWindowsBudgetCertificate) : Prop :=
  0 < c.primaryWindow ∧ c.secondaryWindow ≤ c.primaryWindow + c.slack

def UniformDarbouxWindowsBudgetCertificate.budgetControlled
    (c : UniformDarbouxWindowsBudgetCertificate) : Prop :=
  c.certificateBudgetWindow ≤ c.primaryWindow + c.secondaryWindow + c.slack

def UniformDarbouxWindowsBudgetCertificate.Ready
    (c : UniformDarbouxWindowsBudgetCertificate) : Prop :=
  c.controlled ∧ c.budgetControlled

def UniformDarbouxWindowsBudgetCertificate.size
    (c : UniformDarbouxWindowsBudgetCertificate) : ℕ :=
  c.primaryWindow + c.secondaryWindow + c.slack

theorem uniformDarbouxWindows_budgetCertificate_le_size
    (c : UniformDarbouxWindowsBudgetCertificate) (h : c.Ready) :
    c.certificateBudgetWindow ≤ c.size := by
  rcases h with ⟨_, hbudget⟩
  exact hbudget

def sampleUniformDarbouxWindowsBudgetCertificate :
    UniformDarbouxWindowsBudgetCertificate :=
  { primaryWindow := 5
    secondaryWindow := 6
    certificateBudgetWindow := 12
    slack := 1 }

example : sampleUniformDarbouxWindowsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDarbouxWindowsBudgetCertificate.controlled,
      sampleUniformDarbouxWindowsBudgetCertificate]
  · norm_num [UniformDarbouxWindowsBudgetCertificate.budgetControlled,
      sampleUniformDarbouxWindowsBudgetCertificate]

example :
    sampleUniformDarbouxWindowsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDarbouxWindowsBudgetCertificate.size := by
  apply uniformDarbouxWindows_budgetCertificate_le_size
  constructor
  · norm_num [UniformDarbouxWindowsBudgetCertificate.controlled,
      sampleUniformDarbouxWindowsBudgetCertificate]
  · norm_num [UniformDarbouxWindowsBudgetCertificate.budgetControlled,
      sampleUniformDarbouxWindowsBudgetCertificate]

/-- Finite executable readiness audit for budget certificates. -/
theorem sampleBudgetCertificate_ready :
    sampleUniformDarbouxWindowsBudgetCertificate.Ready := by
  constructor
  · norm_num [UniformDarbouxWindowsBudgetCertificate.controlled,
      sampleUniformDarbouxWindowsBudgetCertificate]
  · norm_num [UniformDarbouxWindowsBudgetCertificate.budgetControlled,
      sampleUniformDarbouxWindowsBudgetCertificate]

theorem sampleBudgetCertificate_le_size :
    sampleUniformDarbouxWindowsBudgetCertificate.certificateBudgetWindow ≤
      sampleUniformDarbouxWindowsBudgetCertificate.size := by
  exact sampleBudgetCertificate_ready.2

def budgetCertificateListReady
    (data : List UniformDarbouxWindowsBudgetCertificate) :
    Bool :=
  data.all fun c => c.certificateBudgetWindow ≤ c.size

theorem budgetCertificateList_readyWindow :
    budgetCertificateListReady
      [sampleUniformDarbouxWindowsBudgetCertificate] = true := by
  unfold budgetCertificateListReady
    sampleUniformDarbouxWindowsBudgetCertificate
  native_decide
end AnalyticCombinatorics.Asymptotics.UniformDarbouxWindows
